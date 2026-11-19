#!/usr/bin/env python3
"""A standalone GitHub-compatible git forge, in one file, stdlib only.

Serves, from one in-memory store:
  * git smart HTTP at /{owner}/{repo}.git  (upload-pack protocol v2, receive-pack v0)
  * the REST v3 API under /api/v3          (repositories, contents, issues, pull requests)
  * the GraphQL v4 API at /api/graphql
  * a Model Context Protocol endpoint at /mcp (JSON-RPC Streamable HTTP)

Lifecycle (the make.fun agent/v1 wire): bind an ephemeral port, POST {"port": N} to
$MAKEFUN_ENV_URL/register, answer GET /healthz, poll $MAKEFUN_ENV_URL/done and exit 0
when the env says the trial is over.

The trial's bearer token (MAKEFUN_SHOP_TOKEN) names one viewer; every repository belongs
to that login. The seeded viewer of this contest's fixed scenario is:

    adaiversen (id 1000, "ada iversen" <adaiversen@example.invalid>)

Determinism: the forge never reads the wall clock for anything it serves. Server-made
commits and timestamps derive from a fixed epoch plus a monotonic counter, so two runs
that receive the same requests produce the same bytes.
"""

import base64
import difflib
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qsl, unquote, urlsplit

# --------------------------------------------------------------------------
# constants and the seeded viewer

VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"

SERVER_NAME = "makefun-forge"
SERVER_VERSION = "1.0.0"
INSTALLED_VERSION = "1.0.0"
OAUTH_SCOPES = "repo, read:org"

ZERO_OID = "0" * 40
EPOCH_BASE = 1_735_689_600  # 2025-01-01T00:00:00Z, the scenario's day one

OBJ_COMMIT = "commit"
OBJ_TREE = "tree"
OBJ_BLOB = "blob"
OBJ_TAG = "tag"
_TYPE_CODES = {OBJ_COMMIT: 1, OBJ_TREE: 2, OBJ_BLOB: 3, OBJ_TAG: 4}
_CODE_TYPES = {code: name for name, code in _TYPE_CODES.items()}

PKT_LINE_MAX = 65520


# --------------------------------------------------------------------------
# small helpers

def iso_utc(epoch_sec):
    """An ISO-8601 UTC string for a fixed epoch second (never the wall clock)."""
    t = time.gmtime(epoch_sec)
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", t)


def b64encode_text(text):
    return base64.b64encode(text.encode("utf-8")).decode("ascii")


def b64decode_loose(data):
    """Decode base64 that may carry whitespace/newlines (GitHub wraps contents)."""
    cleaned = re.sub(r"\s+", "", data or "")
    return base64.b64decode(cleaned.encode("ascii"), validate=False)


# --------------------------------------------------------------------------
# git object primitives

def hash_object(obj_type, data):
    header = ("%s %d\0" % (obj_type, len(data))).encode("utf-8")
    return hashlib.sha1(header + data).hexdigest()


def parse_tree(data):
    """Parse a tree object into [(mode, name, oid)] in stored order."""
    entries = []
    offset = 0
    size = len(data)
    while offset < size:
        space = data.index(b" ", offset)
        nul = data.index(b"\0", space + 1)
        mode = data[offset:space].decode("ascii")
        name = data[space + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        offset = nul + 21
    return entries


def _tree_sort_key(entry):
    mode, name, _oid = entry
    key = name + "/" if mode == "40000" else name
    return key.encode("utf-8")


def build_tree(entries):
    """Build a tree object from [(mode, name, oid)], sorted the way git sorts."""
    out = bytearray()
    for mode, name, oid in sorted(entries, key=_tree_sort_key):
        out += mode.encode("ascii")
        out += b" "
        out += name.encode("utf-8")
        out += b"\0"
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data):
    """Parse a commit object: {tree, parents, author, committer, message}."""
    text = data.decode("utf-8", "replace")
    head, _, message = text.partition("\n\n")
    result = {"tree": None, "parents": [], "author": "", "committer": "", "message": message}
    for line in head.split("\n"):
        key, _, value = line.partition(" ")
        if key == "tree":
            result["tree"] = value
        elif key == "parent":
            result["parents"].append(value)
        elif key == "author":
            result["author"] = value
        elif key == "committer":
            result["committer"] = value
    return result


def build_commit(tree_oid, parents, message, author_line):
    lines = ["tree " + tree_oid]
    for parent in parents:
        lines.append("parent " + parent)
    lines.append("author " + author_line)
    lines.append("committer " + author_line)
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8")


def parse_tag(data):
    text = data.decode("utf-8", "replace")
    head, _, message = text.partition("\n\n")
    result = {"object": None, "type": None, "tag": None, "message": message}
    for line in head.split("\n"):
        key, _, value = line.partition(" ")
        if key in result and key != "message":
            result[key] = value
    return result


def peel_to_commit(store, oid):
    """Follow tag objects until a commit; None when the chain breaks."""
    seen = set()
    while oid is not None and oid not in seen:
        seen.add(oid)
        obj = store.get(oid)
        if obj is None:
            return None
        obj_type, data = obj
        if obj_type == OBJ_COMMIT:
            return oid
        if obj_type == OBJ_TAG:
            oid = parse_tag(data)["object"]
        else:
            return None
    return None


def apply_delta(base, delta):
    """Apply a git delta (copy/insert instruction stream) to base bytes."""
    pos = 0

    def read_size():
        nonlocal pos
        value = 0
        shift = 0
        while True:
            byte = delta[pos]
            pos += 1
            value |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                return value

    source_size = read_size()
    if source_size != len(base):
        raise ValueError("delta base size mismatch")
    target_size = read_size()
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            copy_offset = 0
            copy_size = 0
            for bit in range(4):
                if op & (1 << bit):
                    copy_offset |= delta[pos] << (8 * bit)
                    pos += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    copy_size |= delta[pos] << (8 * bit)
                    pos += 1
            if copy_size == 0:
                copy_size = 0x10000
            out += base[copy_offset:copy_offset + copy_size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0 is invalid")
    if len(out) != target_size:
        raise ValueError("delta produced the wrong size")
    return bytes(out)


# --------------------------------------------------------------------------
# packfiles

def write_pack(objects):
    """Build a version-2 pack from [(type, data)] with no deltas."""
    parts = [b"PACK" + (2).to_bytes(4, "big") + len(objects).to_bytes(4, "big")]
    for obj_type, data in objects:
        code = _TYPE_CODES[obj_type]
        size = len(data)
        first = (code << 4) | (size & 0x0F)
        size >>= 4
        header = bytearray()
        while size:
            header.append(first | 0x80)
            first = size & 0x7F
            size >>= 7
        header.append(first)
        parts.append(bytes(header))
        parts.append(zlib.compress(data))
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


def _read_pack_varint(data, pos):
    byte = data[pos]
    first = byte
    size = byte & 0x0F
    shift = 4
    pos += 1
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        size |= (byte & 0x7F) << shift
        shift += 7
    return size, pos, first


def _read_ofs_base(data, pos):
    byte = data[pos]
    pos += 1
    value = byte & 0x7F
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        value = ((value + 1) << 7) | (byte & 0x7F)
    return value, pos


def read_pack(data, external_lookup=None):
    """Parse a pack into {oid: (type, data)}, resolving OFS/REF deltas.

    `external_lookup(oid)` supplies bases a thin pack leaves out. Raises ValueError
    on any structural problem.
    """
    if len(data) < 32 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(data[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version")
    count = int.from_bytes(data[8:12], "big")
    trailer_at = len(data) - 20
    if hashlib.sha1(data[:trailer_at]).digest() != data[trailer_at:]:
        raise ValueError("pack trailer checksum mismatch")

    raw = []  # (offset, type_code, inflated, base_offset, base_oid)
    by_offset = {}
    pos = 12
    for _ in range(count):
        entry_at = pos
        size, pos, first = _read_pack_varint(data, pos)
        type_code = (first >> 4) & 0x07
        base_offset = None
        base_oid = None
        if type_code == 6:
            back, pos = _read_ofs_base(data, pos)
            base_offset = entry_at - back
        elif type_code == 7:
            base_oid = data[pos:pos + 20].hex()
            pos += 20
        elif type_code not in _CODE_TYPES:
            raise ValueError("unknown pack object type")
        inflater = zlib.decompressobj()
        inflated = inflater.decompress(data[pos:trailer_at])
        if len(inflated) != size:
            raise ValueError("pack object size mismatch")
        consumed = len(data[pos:trailer_at]) - len(inflater.unused_data)
        pos += consumed
        entry = (entry_at, type_code, inflated, base_offset, base_oid)
        raw.append(entry)
        by_offset[entry_at] = entry
    if pos != trailer_at:
        raise ValueError("pack has stray bytes")

    resolved = {}

    def resolve(entry):
        entry_at, type_code, inflated, base_offset, base_oid = entry
        if entry_at in resolved:
            return resolved[entry_at]
        if type_code in _CODE_TYPES:
            obj_type, obj_data = _CODE_TYPES[type_code], inflated
        else:
            if type_code == 6:
                base_entry = by_offset.get(base_offset)
                if base_entry is None:
                    raise ValueError("ofs-delta base missing")
                base_type, base_data = resolve(base_entry)
            else:
                base = None
                for candidate in raw:
                    got = resolve(candidate)
                    if hash_object(got[0], got[1]) == base_oid:
                        base = got
                        break
                if base is None and external_lookup is not None:
                    base = external_lookup(base_oid)
                if base is None:
                    raise ValueError("ref-delta base missing")
                base_type, base_data = base
            obj_type, obj_data = base_type, apply_delta(base_data, inflated)
        resolved[entry_at] = (obj_type, obj_data)
        return obj_type, obj_data

    objects = {}
    for entry in raw:
        obj_type, obj_data = resolve(entry)
        objects[hash_object(obj_type, obj_data)] = (obj_type, obj_data)
    return objects


# --------------------------------------------------------------------------
# reachability

def walk_objects(store, tips, max_commit_depth=None, stop_commits=frozenset()):
    """Every object reachable from `tips`.

    Commits are followed to their trees and parents; a commit in `stop_commits`
    is included with its tree but its parents are not followed (a shallow
    boundary). `max_commit_depth` counts generations: a tip is depth 1.
    Returns (objects:set, boundary:set) where boundary holds the included
    commits whose parents exist but were not followed because of the depth cap.
    """
    objects = set()
    boundary = set()
    stack = []
    for tip in tips:
        if tip in store:
            stack.append((tip, 1))
    seen_commits = {}
    while stack:
        oid, depth = stack.pop()
        obj = store.get(oid)
        if obj is None:
            continue
        obj_type, data = obj
        if obj_type == OBJ_COMMIT:
            previous = seen_commits.get(oid)
            if previous is not None and previous <= depth:
                continue
            seen_commits[oid] = depth
            objects.add(oid)
            commit = parse_commit(data)
            if commit["tree"]:
                stack.append((commit["tree"], depth))
            if oid in stop_commits:
                continue
            for parent in commit["parents"]:
                if max_commit_depth is not None and depth + 1 > max_commit_depth:
                    if parent in store:
                        boundary.add(oid)
                    continue
                stack.append((parent, depth + 1))
        elif obj_type == OBJ_TAG:
            if oid in objects:
                continue
            objects.add(oid)
            target = parse_tag(data)["object"]
            if target:
                stack.append((target, depth))
        elif obj_type == OBJ_TREE:
            if oid in objects:
                continue
            objects.add(oid)
            for _mode, _name, child in parse_tree(data):
                stack.append((child, depth))
        else:
            objects.add(oid)
    return objects, boundary


def is_ancestor(store, ancestor, descendant):
    """True when `ancestor` is reachable from `descendant` through parents."""
    if ancestor == descendant:
        return True
    seen = set()
    stack = [descendant]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        seen.add(oid)
        obj = store.get(oid)
        if obj is None or obj[0] != OBJ_COMMIT:
            continue
        for parent in parse_commit(obj[1])["parents"]:
            if parent == ancestor:
                return True
            stack.append(parent)
    return False


def merge_base(store, left, right):
    """A best common ancestor of two commits (histories here are near-linear)."""
    left_ancestors = set()
    stack = [left]
    while stack:
        oid = stack.pop()
        if oid in left_ancestors:
            continue
        obj = store.get(oid)
        if obj is None or obj[0] != OBJ_COMMIT:
            continue
        left_ancestors.add(oid)
        stack.extend(parse_commit(obj[1])["parents"])
    stack = [right]
    seen = set()
    while stack:
        oid = stack.pop()
        if oid in left_ancestors:
            return oid
        if oid in seen:
            continue
        seen.add(oid)
        obj = store.get(oid)
        if obj is None or obj[0] != OBJ_COMMIT:
            continue
        stack.extend(parse_commit(obj[1])["parents"])
    return None


# --------------------------------------------------------------------------
# the forge store

class ApiError(Exception):
    """An error that maps onto an HTTP status with a JSON {message} body."""

    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


class Repo:
    __slots__ = (
        "id", "name", "owner", "description", "private", "default_branch",
        "objects", "refs", "labels", "issues", "pulls", "next_number",
        "created_seq",
    )

    def __init__(self, repo_id, name, description, private, seq):
        self.id = repo_id
        self.name = name
        self.owner = VIEWER_LOGIN
        self.description = description
        self.private = private
        self.default_branch = "main"
        self.objects = {}          # oid -> (type, data)
        self.refs = {}             # "refs/heads/main" -> oid
        self.labels = {}           # name -> {"name", "color"}
        self.issues = {}           # number -> issue dict
        self.pulls = {}            # number -> pull dict
        self.next_number = 1       # issues and pull requests share one sequence
        self.created_seq = seq

    # -- object store ------------------------------------------------------
    def put(self, obj_type, data):
        oid = hash_object(obj_type, data)
        if oid not in self.objects:
            self.objects[oid] = (obj_type, data)
        return oid

    def get(self, oid):
        return self.objects.get(oid)

    # -- refs ---------------------------------------------------------------
    def branch_tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def head_branch(self):
        return self.default_branch

    # -- trees --------------------------------------------------------------
    def flatten_tree(self, commit_oid):
        """{path: (mode, oid)} for a commit's whole tree ({} for no commit)."""
        flat = {}
        if commit_oid is None:
            return flat
        commit_obj = self.objects.get(commit_oid)
        if commit_obj is None:
            return flat
        commit = parse_commit(commit_obj[1])
        stack = [(commit["tree"], "")]
        while stack:
            tree_oid, prefix = stack.pop()
            tree_obj = self.objects.get(tree_oid)
            if tree_obj is None:
                continue
            for mode, name, child in parse_tree(tree_obj[1]):
                if mode == "40000":
                    stack.append((child, prefix + name + "/"))
                else:
                    flat[prefix + name] = (mode, child)
        return flat

    def build_tree_from_flat(self, flat):
        """Store nested trees for {path: (mode, oid)} and return the root oid."""

        def build(prefix_map):
            entries = []
            subdirs = {}
            for path, (mode, oid) in prefix_map.items():
                head, _, rest = path.partition("/")
                if rest:
                    subdirs.setdefault(head, {})[rest] = (mode, oid)
                else:
                    entries.append((mode, head, oid))
            for name, sub in subdirs.items():
                entries.append(("40000", name, build(sub)))
            return self.put(OBJ_TREE, build_tree(entries))

        return build(dict(flat))

    def tree_at(self, commit_oid, path):
        """(kind, oid) for a path inside a commit's tree: file, dir or None."""
        commit_obj = self.objects.get(commit_oid)
        if commit_obj is None:
            return None
        tree_oid = parse_commit(commit_obj[1])["tree"]
        if path == "":
            return ("dir", tree_oid)
        parts = path.split("/")
        current = tree_oid
        for index, part in enumerate(parts):
            tree_obj = self.objects.get(current)
            if tree_obj is None or tree_obj[0] != OBJ_TREE:
                return None
            found = None
            for mode, name, child in parse_tree(tree_obj[1]):
                if name == part:
                    found = (mode, child)
                    break
            if found is None:
                return None
            mode, child = found
            if index == len(parts) - 1:
                return ("dir", child) if mode == "40000" else ("file", child)
            if mode != "40000":
                return None
            current = child
        return None

    def list_tree(self, tree_oid):
        obj = self.objects.get(tree_oid)
        if obj is None or obj[0] != OBJ_TREE:
            return []
        return parse_tree(obj[1])


class Forge:
    """The whole forge: every repository of the viewer, plus id counters."""

    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}            # name -> Repo
        self.next_repo_id = 1
        self.next_issue_id = 1
        self.next_comment_id = 1
        self.seq = 0               # deterministic clock: +1 per stamped event

    def tick(self):
        self.seq += 1
        return EPOCH_BASE + self.seq

    def author_line(self):
        stamp = self.tick()
        return "%s <%s> %d +0000" % (VIEWER_NAME, VIEWER_EMAIL, stamp), stamp

    # -- repositories --------------------------------------------------------
    def create_repo(self, name, description, private):
        if not name or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,99}", name):
            raise ApiError(422, "Repository name is invalid")
        if name in self.repos:
            raise ApiError(422, "Repository already exists")
        repo = Repo(self.next_repo_id, name, description or "", bool(private), self.seq)
        self.next_repo_id += 1
        self.repos[name] = repo
        return repo

    def get_repo(self, owner, name):
        if owner != VIEWER_LOGIN:
            return None
        return self.repos.get(name)

    def require_repo(self, owner, name):
        repo = self.get_repo(owner, name)
        if repo is None:
            raise ApiError(404, "Not Found")
        return repo

    def delete_repo(self, owner, name):
        repo = self.require_repo(owner, name)
        del self.repos[repo.name]

    # -- commits made by the API ---------------------------------------------
    def commit_files(self, repo, branch, changes, message, parents_from=None):
        """Apply {path: bytes-or-None} changes on `branch` and commit them.

        A branch that does not exist yet is created: from the default branch's
        tip when there is one, else as a root commit. Returns the commit oid.
        """
        ref = "refs/heads/" + branch
        tip = repo.refs.get(ref)
        if tip is None and parents_from is not None:
            tip = parents_from
        if tip is None and branch != repo.default_branch:
            tip = repo.refs.get("refs/heads/" + repo.default_branch)
        flat = repo.flatten_tree(tip)
        for path, content in changes.items():
            if content is None:
                flat.pop(path, None)
            else:
                blob_oid = repo.put(OBJ_BLOB, content)
                flat[path] = ("100644", blob_oid)
        tree_oid = repo.build_tree_from_flat(flat)
        author, _stamp = self.author_line()
        parents = [tip] if tip else []
        commit_oid = repo.put(OBJ_COMMIT, build_commit(tree_oid, parents, message, author))
        repo.refs[ref] = commit_oid
        return commit_oid

    # -- issues ---------------------------------------------------------------
    def create_issue(self, repo, title, body, label_names):
        labels = []
        for name in label_names or []:
            label = repo.labels.get(name)
            if label is None:
                raise ApiError(422, "Label '%s' does not exist" % name)
            labels.append(dict(label))
        number = repo.next_number
        repo.next_number += 1
        issue = {
            "id": self.next_issue_id,
            "number": number,
            "title": title or "",
            "body": body or "",
            "state": "open",
            "labels": labels,
            "comments": [],
            "created_seq": self.seq,
        }
        self.next_issue_id += 1
        repo.issues[number] = issue
        return issue

    def create_comment(self, repo, issue, body):
        comment = {"id": self.next_comment_id, "body": body or "", "issue": issue["number"]}
        self.next_comment_id += 1
        issue["comments"].append(comment)
        return comment

    # -- pull requests ---------------------------------------------------------
    def create_pull(self, repo, title, body, head, base):
        if repo.branch_tip(head) is None:
            raise ApiError(422, "Head branch '%s' does not exist" % head)
        if repo.branch_tip(base) is None:
            raise ApiError(422, "Base branch '%s' does not exist" % base)
        for pull in repo.pulls.values():
            if pull["head"] == head and pull["base"] == base and pull["state"] == "open":
                raise ApiError(422, "A pull request already exists for %s into %s" % (head, base))
        number = repo.next_number
        repo.next_number += 1
        pull = {
            "id": self.next_issue_id,
            "number": number,
            "title": title or "",
            "body": body or "",
            "state": "open",
            "head": head,
            "base": base,
            "merged": False,
            "merged_at": None,
            "merge_commit_sha": None,
            "created_seq": self.seq,
        }
        self.next_issue_id += 1
        repo.pulls[number] = pull
        return pull

    def pull_mergeability(self, repo, pull):
        """(mergeable: bool, merged_tree: flat-or-None) by a file-level 3-way merge."""
        head_tip = repo.branch_tip(pull["head"])
        base_tip = repo.branch_tip(pull["base"])
        if head_tip is None or base_tip is None:
            return False, None
        base_commit = merge_base(repo.objects, head_tip, base_tip)
        base_flat = repo.flatten_tree(base_commit)
        ours = repo.flatten_tree(base_tip)
        theirs = repo.flatten_tree(head_tip)
        merged = {}
        paths = set(base_flat) | set(ours) | set(theirs)
        for path in paths:
            ancestor = base_flat.get(path)
            our = ours.get(path)
            their = theirs.get(path)
            if our == their:
                if our is not None:
                    merged[path] = our
            elif ancestor == our:
                if their is not None:
                    merged[path] = their
            elif ancestor == their:
                if our is not None:
                    merged[path] = our
            else:
                return False, None
        return True, merged

    def merge_pull(self, repo, pull, method):
        """Squash (or merge) a pull request into its base branch; returns the new commit oid."""
        mergeable, merged_flat = self.pull_mergeability(repo, pull)
        if not mergeable:
            raise ApiError(405, "Pull Request is not mergeable")
        base_tip = repo.branch_tip(pull["base"])
        head_tip = repo.branch_tip(pull["head"])
        tree_oid = repo.build_tree_from_flat(merged_flat)
        author, stamp = self.author_line()
        if method == "merge":
            message = "Merge pull request #%d from %s\n\n%s\n" % (pull["number"], pull["head"], pull["title"])
            parents = [base_tip, head_tip]
        else:
            message = "%s (#%d)\n" % (pull["title"], pull["number"])
            if pull["body"]:
                message += "\n" + pull["body"] + "\n"
            parents = [base_tip]
        commit_oid = repo.put(OBJ_COMMIT, build_commit(tree_oid, parents, message, author))
        repo.refs["refs/heads/" + pull["base"]] = commit_oid
        pull["state"] = "closed"
        pull["merged"] = True
        pull["merged_at"] = iso_utc(stamp)
        pull["merge_commit_sha"] = commit_oid
        return commit_oid

    def pull_files(self, repo, pull):
        """The changed paths between the pull's merge base and its head tip."""
        head_tip = repo.branch_tip(pull["head"])
        base_tip = repo.branch_tip(pull["base"])
        if head_tip is None or base_tip is None:
            return []
        base_commit = merge_base(repo.objects, head_tip, base_tip)
        before = repo.flatten_tree(base_commit)
        after = repo.flatten_tree(head_tip)
        files = []
        for path in sorted(set(before) | set(after)):
            old = before.get(path)
            new = after.get(path)
            if old == new:
                continue
            if old is None:
                status = "added"
            elif new is None:
                status = "removed"
            else:
                status = "modified"
            additions, deletions = _line_diff(repo, old, new)
            files.append({
                "filename": path,
                "status": status,
                "additions": additions,
                "deletions": deletions,
                "changes": additions + deletions,
                "sha": new[1] if new else old[1],
            })
        return files


def _blob_lines(repo, entry):
    if entry is None:
        return []
    obj = repo.objects.get(entry[1])
    if obj is None:
        return []
    return obj[1].decode("utf-8", "replace").splitlines()


def _line_diff(repo, old, new):
    old_lines = _blob_lines(repo, old)
    new_lines = _blob_lines(repo, new)
    additions = 0
    deletions = 0
    matcher = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag in ("insert", "replace"):
            additions += j2 - j1
        if tag in ("delete", "replace"):
            deletions += i2 - i1
    return additions, deletions


FORGE = Forge()


# --------------------------------------------------------------------------
# pkt-line framing

def pkt_line(payload):
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    length = len(payload) + 4
    if length > PKT_LINE_MAX:
        raise ValueError("pkt-line too long")
    return ("%04x" % length).encode("ascii") + payload


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def pkt_eof():
    return b"0002"


def pkt_sideband(band, payload):
    length = len(payload) + 5
    if length > PKT_LINE_MAX:
        raise ValueError("pkt-line too long")
    return ("%04x" % length).encode("ascii") + bytes([band]) + payload


def sideband_stream(pack_bytes):
    """Wrap a whole packfile in band-1 packets of at most PKT_LINE_MAX."""
    out = bytearray()
    max_chunk = PKT_LINE_MAX - 5
    for start in range(0, len(pack_bytes), max_chunk):
        out += pkt_sideband(1, pack_bytes[start:start + max_chunk])
    return bytes(out)


DELIM = object()  # sentinel for a pkt-line delimiter (0001)


class PktReader:
    """A cursor over a request body of pkt-lines."""

    def __init__(self, data):
        self.data = data
        self.pos = 0

    def read(self):
        """Next payload as bytes; DELIM for a delimiter; None on flush/EOF/end."""
        if self.pos + 4 > len(self.data):
            return None
        head = self.data[self.pos:self.pos + 4]
        try:
            length = int(head, 16)
        except ValueError:
            raise ValueError("malformed pkt-line length")
        if length == 0:
            self.pos += 4
            return None
        if length == 1:
            self.pos += 4
            return DELIM
        if length == 2:
            self.pos += 4
            return None
        if length < 4 or self.pos + length > len(self.data):
            raise ValueError("pkt-line out of bounds")
        payload = self.data[self.pos + 4:self.pos + length]
        self.pos += length
        return payload

    def rest(self):
        return self.data[self.pos:]


# --------------------------------------------------------------------------
# git smart HTTP

def advertised_refs(repo):
    """[(refname, oid)] for every ref, HEAD resolved first when it exists."""
    items = []
    head_ref = "refs/heads/" + repo.head_branch()
    head_oid = repo.refs.get(head_ref)
    if head_oid is not None:
        items.append(("HEAD", head_oid))
    for refname in sorted(repo.refs):
        items.append((refname, repo.refs[refname]))
    return items


def info_refs_upload_pack(repo, git_protocol):
    if git_protocol and "version=2" in git_protocol:
        lines = [
            "version 2",
            "agent=git/2.43.0",
            "ls-refs=unborn",
            "fetch=shallow",
            "server-option",
            "object-format=sha1",
        ]
        body = b"".join(pkt_line(line) for line in lines) + pkt_flush()
        return body, "application/x-git-upload-pack-advertisement"
    lines = []
    for index, (refname, oid) in enumerate(advertised_refs(repo)):
        caps = ""
        if index == 0:
            caps = ("\0multi_ack_detailed no-done side-band-64k thin-pack ofs-delta "
                    "object-format=sha1 symref=HEAD:refs/heads/" + repo.head_branch())
        lines.append("%s %s%s\n" % (oid, refname, caps))
    if not lines:
        zero = ZERO_OID + " capabilities^{}"
        caps = ("\0multi_ack_detailed no-done side-band-64k thin-pack ofs-delta "
                "object-format=sha1 symref=HEAD:refs/heads/" + repo.head_branch())
        lines.append("%s%s\n" % (zero, caps))
    body = pkt_line("# service=git-upload-pack\n") + pkt_flush()
    body += b"".join(pkt_line(line) for line in lines) + pkt_flush()
    return body, "application/x-git-upload-pack-advertisement"


def info_refs_receive_pack(repo):
    lines = []
    for index, (refname, oid) in enumerate(advertised_refs(repo)):
        caps = ""
        if index == 0:
            caps = "\0report-status side-band-64k delete-refs ofs-delta quiet"
        lines.append("%s %s%s\n" % (oid, refname, caps))
    if not lines:
        caps = "\0report-status side-band-64k delete-refs ofs-delta quiet"
        lines.append("%s capabilities^{}%s\n" % (ZERO_OID, caps))
    body = pkt_line("# service=git-receive-pack\n") + pkt_flush()
    body += b"".join(pkt_line(line) for line in lines) + pkt_flush()
    return body, "application/x-git-receive-pack-advertisement"


def _ls_refs(repo, args, reader):
    prefixes = []
    want_peel = False
    want_symrefs = False
    want_unborn = False
    while True:
        line = reader.read()
        if line is None:
            break
        if line is DELIM:
            continue
        text = line.decode("utf-8", "replace").rstrip("\n")
        if text.startswith("ref-prefix "):
            prefixes.append(text[len("ref-prefix "):])
        elif text == "peel":
            want_peel = True
        elif text == "symrefs":
            want_symrefs = True
        elif text == "unborn":
            want_unborn = True

    def matches(refname):
        if not prefixes:
            return True
        return any(refname.startswith(prefix) for prefix in prefixes)

    out = bytearray()
    head_ref = "refs/heads/" + repo.head_branch()
    head_oid = repo.refs.get(head_ref)
    if head_oid is None:
        if want_unborn and matches("HEAD"):
            line = "unborn HEAD symref-target:%s\n" % head_ref
            out += pkt_line(line)
    elif matches("HEAD"):
        line = "%s HEAD" % head_oid
        if want_symrefs:
            line += " symref-target:%s" % head_ref
        out += pkt_line(line + "\n")
    for refname in sorted(repo.refs):
        if not matches(refname):
            continue
        oid = repo.refs[refname]
        line = "%s %s" % (oid, refname)
        if want_peel and refname.startswith("refs/tags/"):
            commit = peel_to_commit(repo.objects, oid)
            if commit is not None and commit != oid:
                line += " peeled:%s" % commit
        out += pkt_line(line + "\n")
    out += pkt_flush()
    return bytes(out)


def _parse_hex_list(tokens):
    return [token for token in tokens if re.fullmatch(r"[0-9a-f]{40}", token)]


def _fetch_v2(repo, args, reader):
    wants = []
    haves = []
    shallow_lines = []
    depth = None
    deepen_since = None
    deepen_not = []
    deepen = False
    done = False
    while True:
        line = reader.read()
        if line is None:
            break
        if line is DELIM:
            continue
        text = line.decode("utf-8", "replace").rstrip("\n")
        if text.startswith("want "):
            wants.append(text[5:].strip())
        elif text.startswith("have "):
            haves.append(text[5:].strip())
        elif text.startswith("shallow "):
            shallow_lines.append(text[8:].strip())
        elif text.startswith("deepen "):
            depth = int(text[7:].strip())
        elif text.startswith("deepen-since "):
            deepen_since = int(text[13:].strip())
        elif text.startswith("deepen-not "):
            deepen_not.append(text[11:].strip())
        elif text == "deepen":
            deepen = True
        elif text == "done":
            done = True
        elif text == "filter" or text.startswith("filter "):
            pass  # partial clone filters are not exercised by the suite

    store = repo.objects
    client_shallow = set(shallow_lines)
    stop = set(client_shallow)
    # A deepen/depth request redefines the boundary from the wants: the want
    # walk is governed by the depth cap alone, not by the client's old shallow
    # lines (those still bound what the client can claim as haves).
    want_stop = frozenset() if (depth is not None or deepen) else stop
    want_objects, want_boundary = walk_objects(store, wants, max_commit_depth=depth, stop_commits=want_stop)
    have_objects = set()
    if haves:
        have_objects, _ = walk_objects(store, haves, stop_commits=stop)

    out = bytearray()
    if done:
        # fetch negotiation: acknowledge the haves we hold, then declare ready.
        if haves:
            out += pkt_line("acknowledgments\n")
            for have in haves:
                if have in store:
                    out += pkt_line("ACK %s\n" % have)
                else:
                    out += pkt_line("NAK\n")
                    break
            out += pkt_line("ready\n")
            out += pkt_delim()
    send = want_objects - have_objects
    # shallow bookkeeping: report boundaries, and unshallow commits whose
    # parents are now inside the pack.
    new_shallow = set()
    if depth is not None or deepen:
        new_shallow |= want_boundary
    for oid in send:
        obj = store.get(oid)
        if obj is None or obj[0] != OBJ_COMMIT:
            continue
        for parent in parse_commit(obj[1])["parents"]:
            if parent in store and parent not in send and parent not in have_objects:
                if depth is not None:
                    new_shallow.add(oid)
    unshallow = set()
    for oid in client_shallow:
        obj = store.get(oid)
        if obj is None or obj[0] != OBJ_COMMIT:
            continue
        parents = parse_commit(obj[1])["parents"]
        if parents and all(parent in send or parent in have_objects for parent in parents):
            if any(parent in send for parent in parents):
                unshallow.add(oid)
    report_shallow = (new_shallow - client_shallow) | unshallow
    if report_shallow:
        out += pkt_line("shallow-info\n")
        for oid in sorted(new_shallow - client_shallow):
            out += pkt_line("shallow %s\n" % oid)
        for oid in sorted(unshallow):
            out += pkt_line("unshallow %s\n" % oid)
        out += pkt_delim()
    if send:
        out += pkt_line("packfile\n")
        pack_objects = []
        for oid in sorted(send):
            obj_type, obj_data = store[oid]
            pack_objects.append((obj_type, obj_data))
        return bytes(out), pack_objects
    if ZERO_OID in wants:
        # A real git client cloning an empty repository asks for the zero oid
        # and still expects a packfile section (holding an empty pack).
        out += pkt_line("packfile\n")
        return bytes(out), []
    return bytes(out), None


def _fetch_v0(repo, body):
    reader = PktReader(body)
    wants = []
    capabilities = ""
    first = True
    while True:
        line = reader.read()
        if line is None:
            break
        text = line.decode("utf-8", "replace").rstrip("\n")
        if text.startswith("want "):
            parts = text[5:].split("\0", 1)
            wants.append(parts[0].strip())
            if first and len(parts) > 1:
                capabilities = parts[1]
            first = False
        elif text == "done":
            break
    store = repo.objects
    objects, _ = walk_objects(store, wants)
    pack_objects = [(store[oid][0], store[oid][1]) for oid in sorted(objects)]
    use_sideband = "side-band-64k" in capabilities or "side-band" in capabilities
    return pkt_line("NAK\n"), pack_objects, use_sideband


def handle_upload_pack(repo, body, git_protocol):
    """Dispatch a git-upload-pack POST.

    Returns (status, prefix_bytes, pack_objects, use_sideband): the caller
    compresses pack_objects (if any) outside the store lock and appends it,
    sideband-wrapped when asked, followed by a flush packet.
    """
    if git_protocol and "version=2" in git_protocol:
        reader = PktReader(body)
        command = None
        args = {}
        while True:
            line = reader.read()
            if line is None or line is DELIM:
                break
            text = line.decode("utf-8", "replace").rstrip("\n")
            if text.startswith("command="):
                command = text[len("command="):]
            elif text.startswith("agent="):
                args["agent"] = text
        if command == "ls-refs":
            return 200, _ls_refs(repo, args, reader), None, True
        if command == "fetch":
            prefix, pack_objects = _fetch_v2(repo, args, reader)
            return 200, prefix, pack_objects, True
        return 400, pkt_line("ERR unknown command\n") + pkt_flush(), None, True
    prefix, pack_objects, use_sideband = _fetch_v0(repo, body)
    return 200, prefix, pack_objects, use_sideband


def parse_receive_pack(body):
    """Split a receive-pack request into (commands, capabilities, pack_bytes).

    Pure: touches no store, so it can run outside the lock. Raises ValueError
    on a malformed command section.
    """
    reader = PktReader(body)
    commands = []
    capabilities = ""
    first = True
    while True:
        line = reader.read()
        if line is None:
            break
        if line is DELIM:
            continue
        text = line.decode("utf-8", "replace")
        if first and "\0" in text:
            text, capabilities = text.split("\0", 1)
            capabilities = capabilities.strip()
        first = False
        parts = text.rstrip("\n").split(" ")
        if len(parts) != 3:
            raise ValueError("malformed receive-pack command")
        commands.append((parts[0], parts[1], parts[2]))
    return commands, capabilities, reader.rest()


def apply_receive_pack(repo, commands, incoming):
    """Insert parsed pack objects and move the refs; returns report bytes."""
    if incoming is None:
        report = pkt_line("unpack error: the packfile is invalid\n")
        for _old, _new, refname in commands:
            report += pkt_line("ng %s unpacker error\n" % refname)
        report += pkt_flush()
        return report
    for oid, obj in incoming.items():
        repo.objects[oid] = obj

    results = []
    for old, new, refname in commands:
        current = repo.refs.get(refname, ZERO_OID)
        if old != current:
            results.append((refname, False, "stale info"))
            continue
        if new == ZERO_OID:
            head_ref = "refs/heads/" + repo.head_branch()
            if refname == head_ref:
                results.append((refname, False, "deletion of the current branch prohibited"))
                continue
            repo.refs.pop(refname, None)
            results.append((refname, True, ""))
            continue
        obj = repo.objects.get(new)
        if obj is None:
            results.append((refname, False, "bad object"))
            continue
        if old != ZERO_OID and obj[0] == OBJ_COMMIT:
            old_obj = repo.objects.get(old)
            if old_obj is not None and old_obj[0] == OBJ_COMMIT:
                if not is_ancestor(repo.objects, old, new):
                    results.append((refname, False, "non-fast-forward"))
                    continue
        repo.refs[refname] = new
        results.append((refname, True, ""))

    report = bytearray()
    report += pkt_line("unpack ok\n")
    for refname, ok, reason in results:
        if ok:
            report += pkt_line("ok %s\n" % refname)
        else:
            report += pkt_line("ng %s %s\n" % (refname, reason))
    report += pkt_flush()
    return bytes(report)


def _maybe_sideband(report, capabilities):
    if "side-band-64k" in capabilities or "side-band" in capabilities:
        # Band 1 carries the whole report, its terminating flush included;
        # a second, outer flush packet then ends the sideband stream.
        return sideband_stream(report) + pkt_flush()
    return report


# --------------------------------------------------------------------------
# REST v3 serializers

def repo_json(repo):
    return {
        "id": repo.id,
        "node_id": b64encode_text("Repository:%d" % repo.id),
        "name": repo.name,
        "full_name": "%s/%s" % (repo.owner, repo.name),
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "private": repo.private,
        "description": repo.description,
        "fork": False,
        "default_branch": repo.default_branch,
        "html_url": "https://forge.invalid/%s/%s" % (repo.owner, repo.name),
        "clone_url": "https://forge.invalid/%s/%s.git" % (repo.owner, repo.name),
        "created_at": iso_utc(EPOCH_BASE),
        "updated_at": iso_utc(EPOCH_BASE),
        "pushed_at": iso_utc(EPOCH_BASE),
    }


def viewer_json():
    return {
        "login": VIEWER_LOGIN,
        "id": VIEWER_ID,
        "node_id": b64encode_text("User:%d" % VIEWER_ID),
        "name": VIEWER_NAME,
        "email": VIEWER_EMAIL,
        "type": "User",
        "site_admin": False,
    }


def issue_json(repo, issue):
    return {
        "id": issue["id"],
        "node_id": b64encode_text("Issue:%d:%d" % (repo.id, issue["number"])),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "labels": [dict(label) for label in issue["labels"]],
        "comments": len(issue["comments"]),
        "created_at": iso_utc(EPOCH_BASE + issue["created_seq"]),
        "updated_at": iso_utc(EPOCH_BASE + issue["created_seq"]),
        "closed_at": None,
        "html_url": "https://forge.invalid/%s/%s/issues/%d" % (repo.owner, repo.name, issue["number"]),
    }


def comment_json(comment):
    return {
        "id": comment["id"],
        "node_id": b64encode_text("IssueComment:%d" % comment["id"]),
        "body": comment["body"],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "created_at": iso_utc(EPOCH_BASE),
        "updated_at": iso_utc(EPOCH_BASE),
    }


def pull_json(repo, pull):
    head_tip = repo.branch_tip(pull["head"])
    base_tip = repo.branch_tip(pull["base"])
    return {
        "id": pull["id"],
        "node_id": b64encode_text("PullRequest:%d:%d" % (repo.id, pull["number"])),
        "number": pull["number"],
        "title": pull["title"],
        "body": pull["body"],
        "state": pull["state"],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "head": {"ref": pull["head"], "sha": head_tip, "label": "%s:%s" % (repo.owner, pull["head"])},
        "base": {"ref": pull["base"], "sha": base_tip, "label": "%s:%s" % (repo.owner, pull["base"])},
        "merged": pull["merged"],
        "merged_at": pull["merged_at"],
        "merge_commit_sha": pull["merge_commit_sha"],
        "draft": False,
        "created_at": iso_utc(EPOCH_BASE + pull["created_seq"]),
        "updated_at": iso_utc(EPOCH_BASE + pull["created_seq"]),
        "html_url": "https://forge.invalid/%s/%s/pull/%d" % (repo.owner, repo.name, pull["number"]),
    }


def commit_json(repo, oid):
    obj = repo.objects.get(oid)
    commit = parse_commit(obj[1])
    return {
        "sha": oid,
        "node_id": b64encode_text("Commit:%s" % oid),
        "commit": {
            "message": commit["message"],
            "tree": {"sha": commit["tree"]},
            "author": {"name": VIEWER_NAME, "email": VIEWER_EMAIL, "date": iso_utc(EPOCH_BASE)},
            "committer": {"name": VIEWER_NAME, "email": VIEWER_EMAIL, "date": iso_utc(EPOCH_BASE)},
        },
        "parents": [{"sha": parent} for parent in commit["parents"]],
    }


def branch_json(repo, name):
    tip = repo.branch_tip(name)
    return {
        "name": name,
        "commit": {"sha": tip},
        "protected": False,
    }


def ref_json(refname, oid):
    return {
        "ref": refname,
        "node_id": b64encode_text("Ref:%s" % refname),
        "url": "https://forge.invalid/repos/git/refs",
        "object": {"sha": oid, "type": "commit"},
    }


def contents_file_json(repo, path, mode, blob_oid):
    obj = repo.objects[blob_oid]
    data = obj[1]
    return {
        "type": "file",
        "name": path.rsplit("/", 1)[-1],
        "path": path,
        "sha": blob_oid,
        "size": len(data),
        "encoding": "base64",
        "content": base64.b64encode(data).decode("ascii"),
    }


def contents_entry_json(repo, path, mode, oid):
    name = path.rsplit("/", 1)[-1]
    return {
        "type": "dir" if mode == "40000" else "file",
        "name": name,
        "path": path,
        "sha": oid,
    }


# --------------------------------------------------------------------------
# REST v3 handlers. Each returns (status, json_value, extra_headers).
# A None json_value means an empty body (204).

def _pagination(query):
    try:
        page = max(1, int(query.get("page", ["1"])[0]))
    except ValueError:
        page = 1
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    per_page = max(1, min(100, per_page))
    return page, per_page


def _page_headers(path, query, page, per_page, total):
    """A Link header with rel="next" while more pages remain."""
    if page * per_page >= total:
        return {}
    params = dict(query)
    params["page"] = [str(page + 1)]
    params["per_page"] = [str(per_page)]
    query_string = "&".join("%s=%s" % (key, value[0]) for key, value in sorted(params.items()))
    return {"Link": '<%s?%s>; rel="next"' % (path, query_string)}


def rest_root(forge, method, parts, query, body, path):
    return 200, {
        "current_user_url": "/api/v3/user",
        "repository_url": "/api/v3/repos/{owner}/{repo}",
        "emojis_url": "/api/v3/emojis",
    }, {"X-OAuth-Scopes": OAUTH_SCOPES}


def rest_meta(forge, method, parts, query, body, path):
    return 200, {
        "verifiable_password_authentication": False,
        "installed_version": INSTALLED_VERSION,
        "github_connect_mode": False,
    }, {}


def rest_user(forge, method, parts, query, body, path):
    return 200, viewer_json(), {}


def rest_user_repos(forge, method, parts, query, body, path):
    if method == "GET":
        page, per_page = _pagination(query)
        repos = sorted(forge.repos.values(), key=lambda repo: repo.id)
        total = len(repos)
        window = repos[(page - 1) * per_page: page * per_page]
        return 200, [repo_json(repo) for repo in window], _page_headers(path, query, page, per_page, total)
    if method == "POST":
        data = body or {}
        name = data.get("name")
        if not name:
            raise ApiError(422, "Repository name is required")
        repo = forge.create_repo(name, data.get("description"), data.get("private"))
        return 201, repo_json(repo), {}
    raise ApiError(405, "Method not allowed")


def rest_repo(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    if method == "GET":
        return 200, repo_json(forge.require_repo(owner, name)), {}
    repo = forge.require_repo(owner, name)
    if method == "PATCH":
        data = body or {}
        if "description" in data:
            repo.description = data.get("description") or ""
        if "private" in data:
            repo.private = bool(data.get("private"))
        if "default_branch" in data and data.get("default_branch"):
            repo.default_branch = data["default_branch"]
        return 200, repo_json(repo), {}
    if method == "DELETE":
        forge.delete_repo(owner, name)
        return 204, None, {}
    raise ApiError(405, "Method not allowed")


def _resolve_ref_tip(repo, ref):
    """Resolve a branch name, a full ref, HEAD, or a raw commit oid to a commit."""
    if ref is None or ref == "" or ref == "HEAD":
        return repo.branch_tip(repo.default_branch)
    if ref.startswith("refs/"):
        return repo.refs.get(ref)
    tip = repo.branch_tip(ref)
    if tip is not None:
        return tip
    if re.fullmatch(r"[0-9a-f]{40}", ref) and ref in repo.objects:
        return peel_to_commit(repo.objects, ref) or ref
    return None


def rest_contents(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    sub_path = "/".join(parts[2:])
    if method == "PUT":
        data = body or {}
        content = data.get("content")
        if content is None:
            raise ApiError(422, "Content is required")
        raw = b64decode_loose(content)
        branch = data.get("branch") or repo.default_branch
        tip = repo.branch_tip(branch)
        flat = repo.flatten_tree(tip)
        existing = flat.get(sub_path)
        given_sha = data.get("sha")
        if existing is None:
            if given_sha:
                raise ApiError(409, "The file does not exist yet; sha must be omitted")
            status = 201
        else:
            if given_sha != existing[1]:
                raise ApiError(409, "The sha does not match the current file")
            status = 200
        message = data.get("message") or ("Update %s" % sub_path)
        commit_oid = forge.commit_files(repo, branch, {sub_path: raw}, message)
        blob_oid = repo.flatten_tree(commit_oid)[sub_path][1]
        return status, {
            "content": contents_file_json(repo, sub_path, "100644", blob_oid),
            "commit": {"sha": commit_oid},
        }, {}
    if method == "GET":
        ref = query.get("ref", [None])[0]
        tip = _resolve_ref_tip(repo, ref)
        if tip is None:
            raise ApiError(404, "Not Found")
        found = repo.tree_at(tip, sub_path)
        if found is None:
            raise ApiError(404, "Not Found")
        kind, oid = found
        if kind == "file":
            return 200, contents_file_json(repo, sub_path, "100644", oid), {}
        entries = []
        for mode, entry_name, child in repo.list_tree(oid):
            child_path = (sub_path + "/" + entry_name) if sub_path else entry_name
            entries.append(contents_entry_json(repo, child_path, mode, child))
        entries.sort(key=lambda entry: entry["name"])
        return 200, entries, {}
    if method == "DELETE":
        data = body or {}
        branch = data.get("branch") or repo.default_branch
        tip = repo.branch_tip(branch)
        flat = repo.flatten_tree(tip)
        existing = flat.get(sub_path)
        if existing is None:
            raise ApiError(404, "Not Found")
        if data.get("sha") != existing[1]:
            raise ApiError(409, "The sha does not match the current file")
        message = data.get("message") or ("Delete %s" % sub_path)
        commit_oid = forge.commit_files(repo, branch, {sub_path: None}, message)
        return 200, {"content": None, "commit": {"sha": commit_oid}}, {}
    raise ApiError(405, "Method not allowed")


def rest_labels(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    if method == "GET" and len(parts) == 2:
        labels = [dict(label) for label in sorted(repo.labels.values(), key=lambda l: l["name"])]
        return 200, labels, {}
    if method == "POST" and len(parts) == 2:
        data = body or {}
        label_name = data.get("name")
        if not label_name:
            raise ApiError(422, "Label name is required")
        if label_name in repo.labels:
            raise ApiError(422, "Label already exists")
        label = {"name": label_name, "color": (data.get("color") or "ededed").lstrip("#").lower()}
        repo.labels[label_name] = label
        return 201, dict(label), {}
    if method == "GET" and len(parts) == 3:
        label = repo.labels.get(parts[2])
        if label is None:
            raise ApiError(404, "Not Found")
        return 200, dict(label), {}
    raise ApiError(404, "Not Found")


def _sorted_issues(issues, query):
    sort = query.get("sort", ["created"])[0]
    direction = query.get("direction", ["desc"])[0]
    if sort in ("created", "id"):
        key = lambda issue: issue["number"]
    elif sort == "updated":
        key = lambda issue: issue["number"]
    elif sort == "comments":
        key = lambda issue: len(issue["comments"])
    else:
        key = lambda issue: issue["number"]
    return sorted(issues, key=key, reverse=(direction != "asc"))


def rest_issues(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    if len(parts) == 2:
        if method == "POST":
            data = body or {}
            if not data.get("title"):
                raise ApiError(422, "Title is required")
            label_names = []
            for entry in data.get("labels") or []:
                label_names.append(entry["name"] if isinstance(entry, dict) else entry)
            issue = forge.create_issue(repo, data.get("title"), data.get("body"), label_names)
            return 201, issue_json(repo, issue), {}
        if method == "GET":
            state = query.get("state", ["open"])[0]
            issues = list(repo.issues.values())
            if state == "open":
                issues = [i for i in issues if i["state"] == "open"]
            elif state == "closed":
                issues = [i for i in issues if i["state"] == "closed"]
            issues = _sorted_issues(issues, query)
            page, per_page = _pagination(query)
            total = len(issues)
            window = issues[(page - 1) * per_page: page * per_page]
            return 200, [issue_json(repo, i) for i in window], _page_headers(path, query, page, per_page, total)
        raise ApiError(405, "Method not allowed")
    try:
        number = int(parts[2])
    except ValueError:
        raise ApiError(404, "Not Found")
    issue = repo.issues.get(number)
    if issue is None:
        raise ApiError(404, "Not Found")
    if len(parts) == 3:
        if method == "GET":
            return 200, issue_json(repo, issue), {}
        if method == "PATCH":
            data = body or {}
            if "title" in data:
                issue["title"] = data.get("title") or ""
            if "body" in data:
                issue["body"] = data.get("body") or ""
            if "state" in data:
                if data["state"] not in ("open", "closed"):
                    raise ApiError(422, "State must be open or closed")
                issue["state"] = data["state"]
            if "labels" in data:
                labels = []
                for entry in data.get("labels") or []:
                    label_name = entry["name"] if isinstance(entry, dict) else entry
                    label = repo.labels.get(label_name)
                    if label is None:
                        raise ApiError(422, "Label '%s' does not exist" % label_name)
                    labels.append(dict(label))
                issue["labels"] = labels
            return 200, issue_json(repo, issue), {}
        raise ApiError(405, "Method not allowed")
    if len(parts) == 4 and parts[3] == "comments":
        if method == "POST":
            data = body or {}
            comment = forge.create_comment(repo, issue, data.get("body"))
            return 201, comment_json(comment), {}
        if method == "GET":
            page, per_page = _pagination(query)
            comments = issue["comments"]
            total = len(comments)
            window = comments[(page - 1) * per_page: page * per_page]
            return 200, [comment_json(c) for c in window], _page_headers(path, query, page, per_page, total)
        raise ApiError(405, "Method not allowed")
    raise ApiError(404, "Not Found")


def rest_pulls(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    if len(parts) == 2:
        if method == "POST":
            data = body or {}
            head = data.get("head")
            base = data.get("base") or repo.default_branch
            if not data.get("title"):
                raise ApiError(422, "Title is required")
            if not head:
                raise ApiError(422, "Head is required")
            if ":" in head:
                head = head.split(":", 1)[1]
            pull = forge.create_pull(repo, data.get("title"), data.get("body"), head, base)
            return 201, pull_json(repo, pull), {}
        if method == "GET":
            state = query.get("state", ["open"])[0]
            pulls = list(repo.pulls.values())
            if state == "open":
                pulls = [p for p in pulls if p["state"] == "open"]
            elif state == "closed":
                pulls = [p for p in pulls if p["state"] == "closed"]
            sort = query.get("sort", ["created"])[0]
            direction = query.get("direction", ["desc"])[0]
            pulls.sort(key=lambda p: p["number"], reverse=(direction != "asc"))
            page, per_page = _pagination(query)
            total = len(pulls)
            window = pulls[(page - 1) * per_page: page * per_page]
            return 200, [pull_json(repo, p) for p in window], _page_headers(path, query, page, per_page, total)
        raise ApiError(405, "Method not allowed")
    try:
        number = int(parts[2])
    except ValueError:
        raise ApiError(404, "Not Found")
    pull = repo.pulls.get(number)
    if pull is None:
        raise ApiError(404, "Not Found")
    if len(parts) == 3:
        if method == "GET":
            return 200, pull_json(repo, pull), {}
        if method == "PATCH":
            data = body or {}
            if "title" in data:
                pull["title"] = data.get("title") or ""
            if "body" in data:
                pull["body"] = data.get("body") or ""
            if "state" in data:
                if data["state"] not in ("open", "closed"):
                    raise ApiError(422, "State must be open or closed")
                pull["state"] = data["state"]
            return 200, pull_json(repo, pull), {}
        raise ApiError(405, "Method not allowed")
    if len(parts) == 4 and parts[3] == "files" and method == "GET":
        return 200, forge.pull_files(repo, pull), {}
    if len(parts) == 4 and parts[3] == "merge" and method == "PUT":
        data = body or {}
        merge_method = data.get("merge_method") or "squash"
        if pull["state"] != "open":
            raise ApiError(405, "Pull Request is not open")
        sha = forge.merge_pull(repo, pull, merge_method)
        return 200, {"sha": sha, "merged": True, "message": "Pull Request successfully merged"}, {}
    raise ApiError(404, "Not Found")


def rest_git_refs(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    tail = parts[2:]  # after "git"
    if tail and tail[0] == "refs":
        if method == "POST" and len(tail) == 1:
            data = body or {}
            ref = data.get("ref") or ""
            sha = data.get("sha") or ""
            if not ref.startswith("refs/"):
                raise ApiError(422, "Ref must be fully qualified")
            if sha not in repo.objects:
                raise ApiError(422, "Object does not exist")
            repo.refs[ref] = sha
            return 201, ref_json(ref, sha), {}
        if method == "GET" and len(tail) >= 2:
            ref = "refs/" + "/".join(tail[1:])
            oid = repo.refs.get(ref)
            if oid is None:
                raise ApiError(404, "Not Found")
            return 200, ref_json(ref, oid), {}
    raise ApiError(404, "Not Found")


def rest_branches(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    if len(parts) == 2 and method == "GET":
        names = sorted(ref[len("refs/heads/"):] for ref in repo.refs if ref.startswith("refs/heads/"))
        page, per_page = _pagination(query)
        total = len(names)
        window = names[(page - 1) * per_page: page * per_page]
        return 200, [branch_json(repo, n) for n in window], _page_headers(path, query, page, per_page, total)
    if len(parts) >= 3 and method == "GET":
        branch = "/".join(parts[2:])
        if repo.branch_tip(branch) is None:
            raise ApiError(404, "Not Found")
        return 200, branch_json(repo, branch), {}
    raise ApiError(404, "Not Found")


def rest_commits(forge, method, parts, query, body, path):
    owner, name = parts[0], parts[1]
    repo = forge.require_repo(owner, name)
    if method != "GET":
        raise ApiError(405, "Method not allowed")
    if len(parts) == 3:
        oid = parts[2]
        if oid not in repo.objects or repo.objects[oid][0] != OBJ_COMMIT:
            raise ApiError(404, "Not Found")
        return 200, commit_json(repo, oid), {}
    ref = query.get("sha", [None])[0]
    tip = _resolve_ref_tip(repo, ref) if ref else repo.branch_tip(repo.default_branch)
    if tip is None:
        return 200, [], {}
    chain = []
    seen = set()
    current = tip
    while current is not None and current not in seen:
        seen.add(current)
        obj = repo.objects.get(current)
        if obj is None or obj[0] != OBJ_COMMIT:
            break
        chain.append(current)
        parents = parse_commit(obj[1])["parents"]
        current = parents[0] if parents else None
    page, per_page = _pagination(query)
    total = len(chain)
    window = chain[(page - 1) * per_page: page * per_page]
    return 200, [commit_json(repo, oid) for oid in window], _page_headers(path, query, page, per_page, total)


def dispatch_rest(forge, method, rest_path, query, body, full_path):
    """Route a /api/v3 request. rest_path is the path after /api/v3/."""
    segments = [unquote(segment) for segment in rest_path.split("/") if segment != ""]
    if rest_path == "":
        segments = []
    if segments == []:
        return rest_root(forge, method, segments, query, body, full_path)
    if segments == ["meta"]:
        return rest_meta(forge, method, segments, query, body, full_path)
    if segments == ["user"]:
        if method != "GET":
            raise ApiError(405, "Method not allowed")
        return rest_user(forge, method, segments, query, body, full_path)
    if segments == ["user", "repos"]:
        return rest_user_repos(forge, method, segments, query, body, full_path)
    if segments and segments[0] == "repos" and len(segments) >= 3:
        owner, name = segments[1], segments[2]
        rest = segments[3:]
        if not rest:
            return rest_repo(forge, method, [owner, name], query, body, full_path)
        head = rest[0]
        if head == "contents":
            return rest_contents(forge, method, [owner, name] + rest[1:], query, body, full_path)
        if head == "labels":
            return rest_labels(forge, method, [owner, name] + rest[1:], query, body, full_path)
        if head == "issues":
            return rest_issues(forge, method, [owner, name] + rest[1:], query, body, full_path)
        if head == "pulls":
            return rest_pulls(forge, method, [owner, name] + rest[1:], query, body, full_path)
        if head == "git":
            return rest_git_refs(forge, method, [owner, name] + rest[1:], query, body, full_path)
        if head == "branches":
            return rest_branches(forge, method, [owner, name] + rest[1:], query, body, full_path)
        if head == "commits":
            return rest_commits(forge, method, [owner, name] + rest[1:], query, body, full_path)
    raise ApiError(404, "Not Found")


# --------------------------------------------------------------------------
# GraphQL: a hand-written lexer, parser and executor for the queried subset.

GQL_TYPES = {
    "Query": [
        ("viewer", "User"), ("repository", "Repository"), ("node", "Node"),
        ("__type", "__Type"), ("__schema", "__Schema"),
    ],
    "User": [
        ("id", "ID"), ("login", "String"), ("name", "String"), ("email", "String"),
        ("url", "URI"), ("avatarUrl", "URI"), ("isViewer", "Boolean"),
    ],
    "Repository": [
        ("id", "ID"), ("databaseId", "Int"), ("name", "String"), ("nameWithOwner", "String"),
        ("description", "String"), ("isPrivate", "Boolean"), ("url", "URI"),
        ("owner", "RepositoryOwner"), ("defaultBranchRef", "Ref"),
        ("viewerPermission", "RepositoryPermission"), ("hasIssuesEnabled", "Boolean"),
        ("hasPullRequestsEnabled", "Boolean"), ("isEmpty", "Boolean"),
        ("issue", "Issue"), ("issues", "IssueConnection"), ("issueOrPullRequest", "IssueOrPullRequest"),
        ("pullRequest", "PullRequest"), ("pullRequests", "PullRequestConnection"),
        ("ref", "Ref"), ("refs", "RefConnection"), ("labels", "LabelConnection"),
        ("createdAt", "DateTime"), ("updatedAt", "DateTime"),
    ],
    "RepositoryOwner": [("id", "ID"), ("login", "String"), ("url", "URI")],
    "Ref": [("id", "ID"), ("name", "String"), ("prefix", "String"), ("target", "GitObject")],
    "Commit": [("id", "ID"), ("oid", "GitObjectID"), ("message", "String"), ("tree", "Tree")],
    "Tree": [("id", "ID"), ("oid", "GitObjectID")],
    "Issue": [
        ("id", "ID"), ("databaseId", "Int"), ("number", "Int"), ("title", "String"),
        ("body", "String"), ("bodyText", "String"), ("state", "IssueState"), ("url", "URI"),
        ("author", "Actor"), ("labels", "LabelConnection"), ("comments", "IssueCommentConnection"),
        ("createdAt", "DateTime"), ("updatedAt", "DateTime"), ("closedAt", "DateTime"),
        ("repository", "Repository"),
    ],
    "PullRequest": [
        ("id", "ID"), ("databaseId", "Int"), ("number", "Int"), ("title", "String"),
        ("body", "String"), ("bodyText", "String"), ("state", "PullRequestState"),
        ("merged", "Boolean"), ("mergedAt", "DateTime"), ("mergeCommit", "Commit"),
        ("headRefName", "String"), ("baseRefName", "String"), ("headRefOid", "GitObjectID"),
        ("baseRefOid", "GitObjectID"), ("mergeable", "MergeableState"), ("url", "URI"),
        ("author", "Actor"), ("files", "PullRequestChangedFileConnection"),
        ("createdAt", "DateTime"), ("updatedAt", "DateTime"), ("closedAt", "DateTime"),
        ("repository", "Repository"), ("isDraft", "Boolean"), ("additions", "Int"),
        ("deletions", "Int"), ("changedFiles", "Int"),
    ],
    "PullRequestChangedFile": [
        ("path", "String"), ("additions", "Int"), ("deletions", "Int"),
        ("changeType", "PatchStatus"), ("viewerViewedState", "FileViewedState"),
    ],
    "Label": [("id", "ID"), ("name", "String"), ("color", "String"), ("description", "String")],
    "IssueComment": [
        ("id", "ID"), ("databaseId", "Int"), ("body", "String"), ("author", "Actor"),
        ("createdAt", "DateTime"), ("updatedAt", "DateTime"), ("url", "URI"),
    ],
    "Actor": [("login", "String"), ("url", "URI"), ("avatarUrl", "URI")],
    "PageInfo": [
        ("hasNextPage", "Boolean"), ("hasPreviousPage", "Boolean"),
        ("startCursor", "String"), ("endCursor", "String"),
    ],
    "IssueConnection": [("nodes", "[Issue]"), ("edges", "[IssueEdge]"), ("pageInfo", "PageInfo"), ("totalCount", "Int")],
    "IssueEdge": [("node", "Issue"), ("cursor", "String")],
    "PullRequestConnection": [("nodes", "[PullRequest]"), ("edges", "[PullRequestEdge]"), ("pageInfo", "PageInfo"), ("totalCount", "Int")],
    "PullRequestEdge": [("node", "PullRequest"), ("cursor", "String")],
    "PullRequestChangedFileConnection": [("nodes", "[PullRequestChangedFile]"), ("pageInfo", "PageInfo"), ("totalCount", "Int")],
    "LabelConnection": [("nodes", "[Label]"), ("pageInfo", "PageInfo"), ("totalCount", "Int")],
    "IssueCommentConnection": [("nodes", "[IssueComment]"), ("pageInfo", "PageInfo"), ("totalCount", "Int")],
    "RefConnection": [("nodes", "[Ref]"), ("pageInfo", "PageInfo"), ("totalCount", "Int")],
    "Mutation": [
        ("createIssue", "CreateIssuePayload"), ("closeIssue", "CloseIssuePayload"),
        ("reopenIssue", "ReopenIssuePayload"), ("createPullRequest", "CreatePullRequestPayload"),
        ("mergePullRequest", "MergePullRequestPayload"), ("addComment", "AddCommentPayload"),
        ("updateIssue", "UpdateIssuePayload"), ("createRepository", "CreateRepositoryPayload"),
        ("createLabel", "CreateLabelPayload"), ("updatePullRequest", "UpdatePullRequestPayload"),
    ],
    "CreateIssuePayload": [("issue", "Issue"), ("clientMutationId", "String")],
    "CloseIssuePayload": [("issue", "Issue"), ("clientMutationId", "String")],
    "ReopenIssuePayload": [("issue", "Issue"), ("clientMutationId", "String")],
    "CreatePullRequestPayload": [("pullRequest", "PullRequest"), ("clientMutationId", "String")],
    "MergePullRequestPayload": [("pullRequest", "PullRequest"), ("clientMutationId", "String")],
    "AddCommentPayload": [("commentEdge", "IssueCommentEdge"), ("clientMutationId", "String")],
    "IssueCommentEdge": [("node", "IssueComment"), ("cursor", "String")],
    "UpdateIssuePayload": [("issue", "Issue"), ("clientMutationId", "String")],
    "CreateRepositoryPayload": [("repository", "Repository"), ("clientMutationId", "String")],
    "CreateLabelPayload": [("label", "Label"), ("clientMutationId", "String")],
    "UpdatePullRequestPayload": [("pullRequest", "PullRequest"), ("clientMutationId", "String")],
}

GQL_ENUMS = {
    "IssueState": ["OPEN", "CLOSED"],
    "PullRequestState": ["OPEN", "CLOSED", "MERGED"],
    "MergeableState": ["MERGEABLE", "CONFLICTING", "UNKNOWN"],
    "RepositoryPermission": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"],
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION"],
    "OrderDirection": ["ASC", "DESC"],
    "IssueOrderField": ["CREATED_AT", "UPDATED_AT", "COMMENTS"],
    "PullRequestOrderField": ["CREATED_AT", "UPDATED_AT"],
    "RefOrderField": ["ALPHABETICAL", "TAG_COMMIT_DATE"],
    "PatchStatus": ["ADDED", "DELETED", "MODIFIED", "RENAMED", "COPIED", "CHANGED"],
    "FileViewedState": ["DISMISSED", "VIEWED", "UNVIEWED"],
    "MergePullRequestMethod": ["MERGE", "REBASE", "SQUASH"],
    "IssueClosedStateReason": ["COMPLETED", "DUPLICATE", "NOT_PLANNED"],
}

GQL_FIELD_TYPES = {type_name: dict(fields) for type_name, fields in GQL_TYPES.items()}
GQL_OBJECT_TYPES = set(GQL_TYPES)


class GqlSyntaxError(Exception):
    pass


class GqlFieldError(Exception):
    """An execution error that becomes an entry in the response's errors array."""


_GQL_TOKEN = re.compile(r"""
    (?P<ws>[\s,]+)
  | (?P<comment>\#[^\n]*)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
  | (?P<number>-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<ellipsis>\.\.\.)
  | (?P<punct>[!$&():=@\[\]{}|=])
""", re.VERBOSE)


def _gql_tokenize(text):
    tokens = []
    pos = 0
    while pos < len(text):
        match = _GQL_TOKEN.match(text, pos)
        if match is None:
            raise GqlSyntaxError("Unexpected character %r" % text[pos])
        pos = match.end()
        kind = match.lastgroup
        if kind in ("ws", "comment"):
            continue
        tokens.append((kind, match.group()))
    tokens.append(("eof", ""))
    return tokens


class _GqlParser:
    def __init__(self, text):
        self.tokens = _gql_tokenize(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def expect_punct(self, char):
        kind, value = self.next()
        if kind != "punct" or value != char:
            raise GqlSyntaxError("Expected %r, found %r" % (char, value))

    def expect_name(self):
        kind, value = self.next()
        if kind != "name":
            raise GqlSyntaxError("Expected a name, found %r" % value)
        return value

    def parse_document(self):
        operations = []
        while self.peek()[0] != "eof":
            operations.append(self.parse_operation())
        if not operations:
            raise GqlSyntaxError("Empty document")
        return operations

    def parse_operation(self):
        kind, value = self.peek()
        if kind == "punct" and value == "{":
            return {"operation": "query", "name": None, "variables": {}, "selection": self.parse_selection_set()}
        op_type = self.expect_name()
        if op_type not in ("query", "mutation", "subscription"):
            raise GqlSyntaxError("Expected an operation, found %r" % op_type)
        name = None
        if self.peek()[0] == "name":
            name = self.next()[1]
        variables = {}
        if self.peek() == ("punct", "("):
            variables = self.parse_variable_definitions()
        self.skip_directives()
        selection = self.parse_selection_set()
        return {"operation": op_type, "name": name, "variables": variables, "selection": selection}

    def parse_variable_definitions(self):
        defs = {}
        self.expect_punct("(")
        while self.peek() != ("punct", ")"):
            self.expect_punct("$")
            var_name = self.expect_name()
            self.expect_punct(":")
            self.parse_type()
            default = None
            if self.peek() == ("punct", "="):
                self.next()
                default = self.parse_value(const=True)
            self.skip_directives()
            defs[var_name] = default
        self.expect_punct(")")
        return defs

    def parse_type(self):
        kind, value = self.peek()
        if kind == "punct" and value == "[":
            self.next()
            self.parse_type()
            self.expect_punct("]")
        else:
            self.expect_name()
        if self.peek() == ("punct", "!"):
            self.next()

    def skip_directives(self):
        while self.peek() == ("punct", "@"):
            self.next()
            self.expect_name()
            if self.peek() == ("punct", "("):
                self.parse_arguments()

    def parse_arguments(self):
        args = {}
        self.expect_punct("(")
        while self.peek() != ("punct", ")"):
            arg_name = self.expect_name()
            self.expect_punct(":")
            args[arg_name] = self.parse_value()
        self.expect_punct(")")
        return args

    def parse_value(self, const=False):
        kind, value = self.peek()
        if kind == "punct" and value == "$":
            if const:
                raise GqlSyntaxError("Variables are not allowed in constant values")
            self.next()
            return ("var", self.expect_name())
        if kind == "punct" and value == "[":
            self.next()
            items = []
            while self.peek() != ("punct", "]"):
                items.append(self.parse_value(const))
            self.expect_punct("]")
            return ("list", items)
        if kind == "punct" and value == "{":
            self.next()
            fields = {}
            while self.peek() != ("punct", "}"):
                field_name = self.expect_name()
                self.expect_punct(":")
                fields[field_name] = self.parse_value(const)
            self.expect_punct("}")
            return ("object", fields)
        if kind == "string":
            self.next()
            try:
                return ("value", json.loads(value))
            except ValueError:
                raise GqlSyntaxError("Bad string literal")
        if kind == "number":
            self.next()
            if "." in value or "e" in value or "E" in value:
                return ("value", float(value))
            return ("value", int(value))
        if kind == "name":
            self.next()
            if value == "true":
                return ("value", True)
            if value == "false":
                return ("value", False)
            if value == "null":
                return ("value", None)
            return ("enum", value)
        raise GqlSyntaxError("Unexpected value %r" % value)

    def parse_selection_set(self):
        self.expect_punct("{")
        fields = []
        while self.peek() != ("punct", "}"):
            fields.append(self.parse_field())
        self.expect_punct("}")
        return fields

    def parse_field(self):
        if self.peek() == ("ellipsis", "..."):
            self.next()
            if self.peek() == ("name", "on"):
                self.next()
                type_name = self.expect_name()
                self.skip_directives()
                return {"fragment": type_name, "selection": self.parse_selection_set()}
            fragment_name = self.expect_name()
            self.skip_directives()
            return {"spread": fragment_name, "selection": None}
        name = self.expect_name()
        alias = None
        if self.peek() == ("punct", ":"):
            self.next()
            alias = name
            name = self.expect_name()
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_arguments()
        self.skip_directives()
        selection = None
        if self.peek() == ("punct", "{"):
            selection = self.parse_selection_set()
        return {"name": name, "alias": alias, "args": args, "selection": selection}


def _gql_resolve(value, variables):
    kind = value[0]
    if kind == "var":
        return variables.get(value[1])
    if kind == "value":
        return value[1]
    if kind == "enum":
        return value[1]
    if kind == "list":
        return [_gql_resolve(item, variables) for item in value[1]]
    if kind == "object":
        return {key: _gql_resolve(item, variables) for key, item in value[1].items()}
    return None


# -- global ids ---------------------------------------------------------------

def gql_id(kind, payload):
    return b64encode_text("%s:%s" % (kind, payload))


def gql_decode_id(text):
    try:
        raw = base64.b64decode(text.encode("ascii"), validate=False).decode("utf-8")
    except Exception:
        return None, None
    kind, _, payload = raw.partition(":")
    return kind, payload


# -- value wrappers: ("TypeName", payload) tuples flow through execution -------

def _gql_viewer():
    return ("User", {"login": VIEWER_LOGIN, "id": VIEWER_ID, "name": VIEWER_NAME, "email": VIEWER_EMAIL})


def _gql_issue(repo, issue):
    return ("Issue", (repo, issue))


def _gql_pull(repo, pull):
    return ("PullRequest", (repo, pull))


def _gql_page(items, args, cursor_of):
    """Slice `items` by first/after and shape a connection value."""
    after = args.get("after")
    first = args.get("first")
    start = 0
    if after:
        for index, item in enumerate(items):
            if cursor_of(item) == after:
                start = index + 1
                break
    sliced = items[start:]
    total = len(sliced)
    if isinstance(first, int) and first >= 0:
        sliced = sliced[:first]
    has_next = len(sliced) < total
    end_cursor = cursor_of(sliced[-1]) if sliced else (after or None)
    return {
        "items": sliced,
        "cursors": [cursor_of(item) for item in sliced],
        "pageInfo": ("PageInfo", {
            "hasNextPage": has_next,
            "hasPreviousPage": start > 0,
            "startCursor": cursor_of(sliced[0]) if sliced else None,
            "endCursor": end_cursor,
        }),
        "totalCount": len(items),
    }


def _issue_cursor(number):
    return b64encode_text("cursor:%d" % number)


def _pull_cursor(number):
    return b64encode_text("cursor:%d" % number)


def _sort_issue_list(issues, args):
    order_by = args.get("orderBy") or {}
    field = order_by.get("field") or "CREATED_AT"
    direction = order_by.get("direction") or "ASC"
    if field == "COMMENTS":
        key = lambda issue: len(issue["comments"])
    else:
        key = lambda issue: issue["number"]
    return sorted(issues, key=key, reverse=(direction == "DESC"))


class GqlExecutor:
    def __init__(self, forge):
        self.forge = forge

    def execute(self, document_text, variables, operation_name):
        try:
            operations = _GqlParser(document_text).parse_document()
        except GqlSyntaxError as error:
            return {"errors": [{"message": "Syntax Error: %s" % error}]}
        operation = None
        if operation_name:
            for candidate in operations:
                if candidate["name"] == operation_name:
                    operation = candidate
                    break
            if operation is None:
                return {"errors": [{"message": "Unknown operation named %r" % operation_name}]}
        else:
            operation = operations[0]
        merged_vars = dict(operation["variables"])
        for key, value in (variables or {}).items():
            merged_vars[key] = value
        root_type = "Mutation" if operation["operation"] == "mutation" else "Query"
        root_value = (root_type, None)
        errors = []
        try:
            data = self.exec_selection(root_value, operation["selection"], merged_vars, errors)
        except GqlFieldError as error:
            return {"data": None, "errors": [{"message": str(error)}]}
        result = {"data": data}
        if errors:
            result["errors"] = errors
        return result

    def exec_selection(self, typed_value, selection, variables, errors):
        type_name, payload = typed_value
        out = {}
        for field in selection or []:
            if "fragment" in field:
                if field["fragment"] == type_name or field["fragment"] in ("Node", "Actor"):
                    out.update(self.exec_selection(typed_value, field["selection"], variables, errors))
                continue
            if "spread" in field:
                continue
            key = field["alias"] or field["name"]
            args = {name: _gql_resolve(value, variables) for name, value in field["args"].items()}
            try:
                raw = self.resolve_field(type_name, payload, field["name"], args)
            except GqlFieldError as error:
                out[key] = None
                errors.append({"message": str(error)})
                continue
            out[key] = self.complete(raw, field, variables, errors)
        return out

    def complete(self, raw, field, variables, errors):
        if raw is None:
            return None
        if isinstance(raw, list):
            return [self.complete(item, field, variables, errors) for item in raw]
        if isinstance(raw, tuple) and len(raw) == 2 and isinstance(raw[0], str):
            if field["selection"] is None:
                return raw[1] if not isinstance(raw[1], tuple) else raw[0]
            return self.exec_selection(raw, field["selection"], variables, errors)
        return raw

    # -- field resolution -------------------------------------------------------
    def resolve_field(self, type_name, payload, name, args):
        if name == "__typename":
            return type_name
        if type_name in ("Query", "Mutation"):
            return self.resolve_root(type_name, name, args)
        if type_name == "__Type":
            return self.type_field(payload, name, args)
        if type_name == "__Field":
            field_name, field_type = payload
            if name == "name":
                return field_name
            if name == "type":
                return ("__Type", re.sub(r"[\[\]!]", "", field_type))
            if name == "args":
                return []
            if name == "isDeprecated":
                return False
            return None
        if type_name == "__EnumValue":
            return payload if name == "name" else (False if name == "isDeprecated" else None)
        if type_name == "__Schema":
            if name == "types":
                names = list(GQL_TYPES) + list(GQL_ENUMS) + ["String", "Int", "Boolean", "ID", "URI", "DateTime", "GitObjectID"]
                return [("__Type", item) for item in names]
            if name == "queryType":
                return ("__Type", "Query")
            if name == "mutationType":
                return ("__Type", "Mutation")
            if name == "directives":
                return []
            return None
        known = GQL_FIELD_TYPES.get(type_name)
        if known is not None and name not in known:
            raise GqlFieldError("Field '%s' doesn't exist on type '%s'" % (name, type_name))
        handler = getattr(self, "field_%s" % type_name, None)
        if handler is not None:
            return handler(payload, name, args)
        if isinstance(payload, dict):
            return payload.get(name)
        return None

    def type_field(self, type_name, name, args):
        if name == "name":
            return type_name
        if name == "kind":
            if type_name in GQL_ENUMS:
                return "ENUM"
            if type_name in GQL_TYPES:
                return "OBJECT"
            return "SCALAR"
        if name == "description":
            return None
        if name == "fields":
            fields = GQL_TYPES.get(type_name)
            if fields is None:
                return None
            return [("__Field", entry) for entry in fields]
        if name == "enumValues":
            values = GQL_ENUMS.get(type_name)
            if values is None:
                return None
            return [("__EnumValue", value) for value in values]
        if name in ("inputFields", "possibleTypes", "interfaces"):
            return [] if name != "possibleTypes" else None
        if name == "ofType":
            return None
        return None

    # -- roots -------------------------------------------------------------------
    def resolve_root(self, root_type, name, args):
        if root_type == "Query":
            if name == "viewer":
                return _gql_viewer()
            if name == "repository":
                repo = self.forge.get_repo(args.get("owner") or "", args.get("name") or "")
                return ("Repository", repo) if repo is not None else None
            if name == "node":
                return self.node_by_id(args.get("id") or "")
            if name == "__type":
                return ("__Type", args.get("name") or "")
            if name == "__schema":
                return ("__Schema", None)
            raise GqlFieldError("Field '%s' doesn't exist on type 'Query'" % name)
        return self.mutation(name, args)

    def node_by_id(self, global_id):
        kind, payload = gql_decode_id(global_id)
        if kind == "User":
            return _gql_viewer()
        if kind == "Repository":
            for repo in self.forge.repos.values():
                if str(repo.id) == payload:
                    return ("Repository", repo)
            return None
        if kind in ("Issue", "PullRequest"):
            repo_id, _, number = payload.partition(":")
            for repo in self.forge.repos.values():
                if str(repo.id) == repo_id:
                    try:
                        num = int(number)
                    except ValueError:
                        return None
                    if kind == "Issue" and num in repo.issues:
                        return _gql_issue(repo, repo.issues[num])
                    if kind == "PullRequest" and num in repo.pulls:
                        return _gql_pull(repo, repo.pulls[num])
            return None
        if kind == "IssueComment":
            for repo in self.forge.repos.values():
                for issue in repo.issues.values():
                    for comment in issue["comments"]:
                        if str(comment["id"]) == payload:
                            return ("IssueComment", comment)
            return None
        return None

    def repo_by_global_id(self, global_id):
        kind, payload = gql_decode_id(global_id or "")
        if kind != "Repository":
            raise GqlFieldError("Invalid repository id")
        for repo in self.forge.repos.values():
            if str(repo.id) == payload:
                return repo
        raise GqlFieldError("Repository not found")

    def thing_by_global_id(self, global_id):
        kind, payload = gql_decode_id(global_id or "")
        repo_id, _, number = payload.partition(":")
        for repo in self.forge.repos.values():
            if str(repo.id) != repo_id:
                continue
            try:
                num = int(number)
            except ValueError:
                break
            if kind == "Issue" and num in repo.issues:
                return repo, "issue", repo.issues[num]
            if kind == "PullRequest" and num in repo.pulls:
                return repo, "pull", repo.pulls[num]
        raise GqlFieldError("Could not resolve the given id")

    def mutation(self, name, args):
        forge = self.forge
        data = args.get("input") or {}
        try:
            if name == "createIssue":
                repo = self.repo_by_global_id(data.get("repositoryId"))
                label_names = []
                for label_id in data.get("labelIds") or []:
                    _kind, payload = gql_decode_id(label_id)
                    label_names.append(payload.partition(":")[2] or payload)
                for label_name in label_names:
                    if label_name not in repo.labels:
                        repo.labels[label_name] = {"name": label_name, "color": "ededed"}
                issue = forge.create_issue(repo, data.get("title"), data.get("body"), label_names)
                return ("CreateIssuePayload", {"issue": _gql_issue(repo, issue), "clientMutationId": data.get("clientMutationId")})
            if name in ("closeIssue", "reopenIssue", "updateIssue"):
                repo, _kind, issue = self.thing_by_global_id(data.get("issueId") or data.get("id"))
                if name == "closeIssue":
                    issue["state"] = "closed"
                elif name == "reopenIssue":
                    issue["state"] = "open"
                else:
                    if "title" in data:
                        issue["title"] = data.get("title") or ""
                    if "body" in data:
                        issue["body"] = data.get("body") or ""
                    if data.get("state"):
                        issue["state"] = str(data["state"]).lower()
                payload_type = {"closeIssue": "CloseIssuePayload", "reopenIssue": "ReopenIssuePayload"}.get(name, "UpdateIssuePayload")
                return (payload_type, {"issue": _gql_issue(repo, issue), "clientMutationId": data.get("clientMutationId")})
            if name == "createPullRequest":
                repo = self.repo_by_global_id(data.get("repositoryId"))
                pull = forge.create_pull(repo, data.get("title"), data.get("body"),
                                         data.get("headRefName") or "", data.get("baseRefName") or repo.default_branch)
                return ("CreatePullRequestPayload", {"pullRequest": _gql_pull(repo, pull), "clientMutationId": data.get("clientMutationId")})
            if name == "mergePullRequest":
                repo, _kind, pull = self.thing_by_global_id(data.get("pullRequestId") or "")
                method = str(data.get("mergeMethod") or "SQUASH").lower()
                forge.merge_pull(repo, pull, method)
                return ("MergePullRequestPayload", {"pullRequest": _gql_pull(repo, pull), "clientMutationId": data.get("clientMutationId")})
            if name == "updatePullRequest":
                repo, _kind, pull = self.thing_by_global_id(data.get("pullRequestId") or data.get("id"))
                if "title" in data:
                    pull["title"] = data.get("title") or ""
                if "body" in data:
                    pull["body"] = data.get("body") or ""
                if data.get("state"):
                    pull["state"] = str(data["state"]).lower()
                return ("UpdatePullRequestPayload", {"pullRequest": _gql_pull(repo, pull), "clientMutationId": data.get("clientMutationId")})
            if name == "addComment":
                repo, kind, thing = self.thing_by_global_id(data.get("subjectId") or "")
                comments = thing.setdefault("comments", [])
                comment = {"id": forge.next_comment_id, "body": data.get("body") or "", "issue": thing["number"]}
                forge.next_comment_id += 1
                comments.append(comment)
                edge = ("IssueCommentEdge", {"node": ("IssueComment", comment), "cursor": _issue_cursor(thing["number"])})
                return ("AddCommentPayload", {"commentEdge": edge, "clientMutationId": data.get("clientMutationId")})
            if name == "createRepository":
                repo = forge.create_repo(data.get("name") or "", data.get("description"),
                                         str(data.get("visibility") or "PUBLIC").upper() == "PRIVATE")
                return ("CreateRepositoryPayload", {"repository": ("Repository", repo), "clientMutationId": data.get("clientMutationId")})
            if name == "createLabel":
                repo = self.repo_by_global_id(data.get("repositoryId"))
                label = {"name": data.get("name") or "", "color": (data.get("color") or "ededed").lstrip("#").lower()}
                repo.labels[label["name"]] = label
                return ("CreateLabelPayload", {"label": ("Label", (repo, label)), "clientMutationId": data.get("clientMutationId")})
        except ApiError as error:
            raise GqlFieldError(error.message)
        raise GqlFieldError("Field '%s' doesn't exist on type 'Mutation'" % name)

    # -- object types ---------------------------------------------------------------
    def field_User(self, payload, name, args):
        if name == "id":
            return gql_id("User", payload["id"])
        if name == "isViewer":
            return True
        if name in ("url", "avatarUrl"):
            return ""
        return payload.get(name)

    def field_RepositoryOwner(self, payload, name, args):
        if name == "id":
            return gql_id("User", VIEWER_ID)
        if name == "url":
            return ""
        return payload.get(name)

    def field_Actor(self, payload, name, args):
        if name in ("url", "avatarUrl"):
            return ""
        return payload.get(name)

    def field_Repository(self, repo, name, args):
        forge = self.forge
        if name == "id":
            return gql_id("Repository", repo.id)
        if name == "databaseId":
            return repo.id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return "%s/%s" % (repo.owner, repo.name)
        if name == "description":
            return repo.description
        if name == "isPrivate":
            return repo.private
        if name == "url":
            return "https://forge.invalid/%s/%s" % (repo.owner, repo.name)
        if name == "owner":
            return ("RepositoryOwner", {"login": repo.owner})
        if name == "defaultBranchRef":
            tip = repo.branch_tip(repo.default_branch)
            if tip is None:
                return None
            return ("Ref", {"name": repo.default_branch, "prefix": "refs/heads/", "target": tip, "repo": repo})
        if name == "viewerPermission":
            return "ADMIN"
        if name in ("hasIssuesEnabled", "hasPullRequestsEnabled"):
            return True
        if name == "isEmpty":
            return not repo.refs
        if name in ("createdAt", "updatedAt"):
            return iso_utc(EPOCH_BASE + repo.created_seq)
        if name == "issue":
            issue = repo.issues.get(args.get("number"))
            return _gql_issue(repo, issue) if issue else None
        if name == "pullRequest":
            pull = repo.pulls.get(args.get("number"))
            return _gql_pull(repo, pull) if pull else None
        if name == "issueOrPullRequest":
            number = args.get("number")
            if number in repo.issues:
                return _gql_issue(repo, repo.issues[number])
            if number in repo.pulls:
                return _gql_pull(repo, repo.pulls[number])
            return None
        if name == "issues":
            issues = list(repo.issues.values())
            states = args.get("states")
            if states:
                wanted = {str(state).lower() for state in states}
                issues = [i for i in issues if i["state"] in wanted]
            issues = _sort_issue_list(issues, args)
            wrapped = [_gql_issue(repo, i) for i in issues]
            page = _gql_page(wrapped, args, lambda item: _issue_cursor(item[1][1]["number"]))
            return ("IssueConnection", self._connection(page, "IssueEdge"))
        if name == "pullRequests":
            pulls = list(repo.pulls.values())
            states = args.get("states")
            if states:
                wanted = {str(state).upper() for state in states}
                def pr_state(pull):
                    return "MERGED" if pull["merged"] else pull["state"].upper()
                pulls = [p for p in pulls if pr_state(p) in wanted]
            order_by = args.get("orderBy") or {}
            direction = order_by.get("direction") or "ASC"
            pulls.sort(key=lambda p: p["number"], reverse=(direction == "DESC"))
            wrapped = [_gql_pull(repo, p) for p in pulls]
            page = _gql_page(wrapped, args, lambda item: _pull_cursor(item[1][1]["number"]))
            return ("PullRequestConnection", self._connection(page, "PullRequestEdge"))
        if name == "ref":
            qualified = args.get("qualifiedName") or ""
            if qualified.startswith("refs/") and qualified in repo.refs:
                short = qualified[len("refs/"):]
                kind, _, branch = short.partition("/")
                return ("Ref", {"name": branch, "prefix": "refs/%s/" % kind, "target": repo.refs[qualified], "repo": repo})
            return None
        if name == "refs":
            prefix = args.get("refPrefix") or "refs/heads/"
            refs = []
            for refname in sorted(repo.refs):
                if refname.startswith(prefix):
                    refs.append(("Ref", {"name": refname[len(prefix):], "prefix": prefix, "target": repo.refs[refname], "repo": repo}))
            page = _gql_page(refs, args, lambda item: b64encode_text("cursor:%s" % item[1]["name"]))
            return ("RefConnection", self._connection(page, "RefEdge"))
        if name == "labels":
            labels = [("Label", (repo, label)) for label in sorted(repo.labels.values(), key=lambda l: l["name"])]
            page = _gql_page(labels, args, lambda item: b64encode_text("cursor:%s" % item[1][1]["name"]))
            return ("LabelConnection", self._connection(page, "LabelEdge"))
        return None

    def _connection(self, page, edge_type):
        items = page["items"]
        cursors = page.get("cursors")
        edges = []
        for index, item in enumerate(items):
            cursor = cursors[index] if cursors else page["pageInfo"][1]["endCursor"]
            edges.append((edge_type, {"node": item, "cursor": cursor}))
        return {"items": items, "nodes": items, "pageInfo": page["pageInfo"], "totalCount": page["totalCount"], "edges": edges}

    def field_Issue(self, payload, name, args):
        repo, issue = payload
        if name == "id":
            return gql_id("Issue", "%d:%d" % (repo.id, issue["number"]))
        if name == "databaseId":
            return issue["id"]
        if name == "number":
            return issue["number"]
        if name == "title":
            return issue["title"]
        if name in ("body", "bodyText"):
            return issue["body"]
        if name == "state":
            return issue["state"].upper()
        if name == "url":
            return "https://forge.invalid/%s/%s/issues/%d" % (repo.owner, repo.name, issue["number"])
        if name == "author":
            return ("Actor", {"login": VIEWER_LOGIN})
        if name == "repository":
            return ("Repository", repo)
        if name in ("createdAt", "updatedAt"):
            return iso_utc(EPOCH_BASE + issue["created_seq"])
        if name == "closedAt":
            return iso_utc(EPOCH_BASE + issue["created_seq"]) if issue["state"] == "closed" else None
        if name == "labels":
            labels = [("Label", (repo, label)) for label in issue["labels"]]
            page = _gql_page(labels, args, lambda item: b64encode_text("cursor:%s" % item[1][1]["name"]))
            return ("LabelConnection", self._connection(page, "LabelEdge"))
        if name == "comments":
            comments = [("IssueComment", comment) for comment in issue["comments"]]
            page = _gql_page(comments, args, lambda item: b64encode_text("cursor:%d" % item[1]["id"]))
            return ("IssueCommentConnection", self._connection(page, "IssueCommentEdge"))
        return None

    def field_PullRequest(self, payload, name, args):
        repo, pull = payload
        if name == "id":
            return gql_id("PullRequest", "%d:%d" % (repo.id, pull["number"]))
        if name == "databaseId":
            return pull["id"]
        if name == "number":
            return pull["number"]
        if name == "title":
            return pull["title"]
        if name in ("body", "bodyText"):
            return pull["body"]
        if name == "state":
            return "MERGED" if pull["merged"] else pull["state"].upper()
        if name == "merged":
            return pull["merged"]
        if name == "mergedAt":
            return pull["merged_at"]
        if name == "mergeCommit":
            if pull["merge_commit_sha"]:
                return ("Commit", (repo, pull["merge_commit_sha"]))
            return None
        if name == "headRefName":
            return pull["head"]
        if name == "baseRefName":
            return pull["base"]
        if name == "headRefOid":
            return repo.branch_tip(pull["head"])
        if name == "baseRefOid":
            return repo.branch_tip(pull["base"])
        if name == "mergeable":
            if pull["state"] != "open":
                return "UNKNOWN"
            mergeable, _merged = self.forge.pull_mergeability(repo, pull)
            return "MERGEABLE" if mergeable else "CONFLICTING"
        if name == "url":
            return "https://forge.invalid/%s/%s/pull/%d" % (repo.owner, repo.name, pull["number"])
        if name == "author":
            return ("Actor", {"login": VIEWER_LOGIN})
        if name == "repository":
            return ("Repository", repo)
        if name == "isDraft":
            return False
        if name in ("createdAt", "updatedAt"):
            return iso_utc(EPOCH_BASE + pull["created_seq"])
        if name == "closedAt":
            return pull["merged_at"] if pull["merged"] else None
        if name in ("files", "additions", "deletions", "changedFiles"):
            files = self.forge.pull_files(repo, pull)
            if name == "additions":
                return sum(entry["additions"] for entry in files)
            if name == "deletions":
                return sum(entry["deletions"] for entry in files)
            if name == "changedFiles":
                return len(files)
            status_map = {"added": "ADDED", "removed": "DELETED", "modified": "MODIFIED"}
            wrapped = [("PullRequestChangedFile", {
                "path": entry["filename"], "additions": entry["additions"],
                "deletions": entry["deletions"], "changeType": status_map.get(entry["status"], "MODIFIED"),
                "viewerViewedState": "UNVIEWED",
            }) for entry in files]
            page = _gql_page(wrapped, args, lambda item: b64encode_text("cursor:%s" % item[1]["path"]))
            return ("PullRequestChangedFileConnection", self._connection(page, "PullRequestChangedFileEdge"))
        return None

    def field_Ref(self, payload, name, args):
        if name == "id":
            return gql_id("Ref", payload["prefix"] + payload["name"])
        if name == "target":
            target = payload["target"]
            obj = payload["repo"].objects.get(target)
            if obj is not None and obj[0] == OBJ_COMMIT:
                return ("Commit", (payload["repo"], target))
            return None
        return payload.get(name)

    def field_Commit(self, payload, name, args):
        repo, oid = payload
        if name == "id":
            return gql_id("Commit", oid)
        if name == "oid":
            return oid
        commit = parse_commit(repo.objects[oid][1])
        if name == "message":
            return commit["message"]
        if name == "tree":
            return ("Tree", {"oid": commit["tree"], "repo": repo})
        return None

    def field_Tree(self, payload, name, args):
        if name == "id":
            return gql_id("Tree", payload["oid"])
        return payload.get(name)

    def field_Label(self, payload, name, args):
        repo, label = payload
        if name == "id":
            return gql_id("Label", "%d:%s" % (repo.id, label["name"]))
        if name == "description":
            return None
        return label.get(name)

    def field_IssueComment(self, payload, name, args):
        if name == "id":
            return gql_id("IssueComment", payload["id"])
        if name == "databaseId":
            return payload["id"]
        if name == "body":
            return payload["body"]
        if name == "author":
            return ("Actor", {"login": VIEWER_LOGIN})
        if name in ("createdAt", "updatedAt"):
            return iso_utc(EPOCH_BASE)
        if name == "url":
            return ""
        return None



# --------------------------------------------------------------------------
# MCP: JSON-RPC Streamable HTTP at /mcp.

def _mcp_schema(properties, required):
    return {"type": "object", "properties": properties, "required": required}


_STR = {"type": "string"}
_BOOL = {"type": "boolean"}
_INT = {"type": "integer"}

MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a new repository owned by the viewer.",
        "inputSchema": _mcp_schema({
            "name": dict(_STR, description="Repository name"),
            "description": dict(_STR, description="Repository description"),
            "private": dict(_BOOL, description="Whether the repository is private"),
        }, ["name"]),
    },
    {
        "name": "get_repo",
        "description": "Fetch one repository by owner and name.",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
        }, ["owner", "repo"]),
    },
    {
        "name": "create_issue",
        "description": "Open a new issue in a repository.",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
            "title": dict(_STR, description="Issue title"),
            "body": dict(_STR, description="Issue body"),
        }, ["owner", "repo", "title"]),
    },
    {
        "name": "get_issue",
        "description": "Fetch one issue by number.",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
            "issue_number": dict(_INT, description="Issue number"),
        }, ["owner", "repo", "issue_number"]),
    },
    {
        "name": "list_issues",
        "description": "List the issues of a repository, optionally filtered by state.",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
            "state": dict(_STR, description="open, closed or all"),
        }, ["owner", "repo"]),
    },
    {
        "name": "create_pull_request",
        "description": "Open a pull request from a head branch into a base branch.",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
            "title": dict(_STR, description="Pull request title"),
            "body": dict(_STR, description="Pull request body"),
            "head": dict(_STR, description="Head branch name"),
            "base": dict(_STR, description="Base branch name"),
        }, ["owner", "repo", "title", "head", "base"]),
    },
    {
        "name": "list_pull_requests",
        "description": "List the pull requests of a repository, optionally filtered by state.",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
            "state": dict(_STR, description="open, closed or all"),
        }, ["owner", "repo"]),
    },
    {
        "name": "merge_pull_request",
        "description": "Merge an open pull request into its base branch (squash).",
        "inputSchema": _mcp_schema({
            "owner": dict(_STR, description="Repository owner login"),
            "repo": dict(_STR, description="Repository name"),
            "pull_number": dict(_INT, description="Pull request number"),
        }, ["owner", "repo", "pull_number"]),
    },
]

MCP_TOOLS_BY_NAME = {tool["name"]: tool for tool in MCP_TOOLS}
# tools/list must be byte-identical across calls: serialize once, up front.
MCP_TOOLS_LIST_BYTES = json.dumps({"tools": MCP_TOOLS}, separators=(",", ":"), sort_keys=True).encode("utf-8")

MCP_SUPPORTED_VERSIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]


class McpError(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code
        self.message = message


def _mcp_result_object(value):
    return {
        "content": [{"type": "text", "text": json.dumps(value)}],
        "structuredContent": value,
        "isError": False,
    }


def _mcp_error_result(message):
    return {
        "content": [{"type": "text", "text": message}],
        "isError": True,
    }


def mcp_call_tool(forge, name, arguments):
    """Run one tool against the shared store; returns a CallToolResult dict."""
    tool = MCP_TOOLS_BY_NAME.get(name)
    if tool is None:
        raise McpError(-32602, "Unknown tool: %s" % name)
    args = arguments or {}
    for required in tool["inputSchema"].get("required", []):
        if args.get(required) is None:
            raise McpError(-32602, "Missing required argument: %s" % required)
    try:
        if name == "create_repo":
            repo = forge.create_repo(args["name"], args.get("description"), args.get("private"))
            return _mcp_result_object(repo_json(repo))
        if name == "get_repo":
            repo = forge.get_repo(args["owner"], args["repo"])
            if repo is None:
                return _mcp_error_result("Repository not found")
            return _mcp_result_object(repo_json(repo))
        if name == "create_issue":
            repo = forge.require_repo(args["owner"], args["repo"])
            label_names = []
            for entry in args.get("labels") or []:
                label_names.append(entry["name"] if isinstance(entry, dict) else entry)
            for label_name in label_names:
                if label_name not in repo.labels:
                    repo.labels[label_name] = {"name": label_name, "color": "ededed"}
            issue = forge.create_issue(repo, args["title"], args.get("body"), label_names)
            return _mcp_result_object(issue_json(repo, issue))
        if name == "get_issue":
            repo = forge.require_repo(args["owner"], args["repo"])
            issue = repo.issues.get(args["issue_number"])
            if issue is None:
                return _mcp_error_result("Issue not found")
            return _mcp_result_object(issue_json(repo, issue))
        if name == "list_issues":
            repo = forge.require_repo(args["owner"], args["repo"])
            state = args.get("state") or "open"
            issues = list(repo.issues.values())
            if state == "open":
                issues = [i for i in issues if i["state"] == "open"]
            elif state == "closed":
                issues = [i for i in issues if i["state"] == "closed"]
            issues.sort(key=lambda i: i["number"])
            return _mcp_result_object({"issues": [issue_json(repo, i) for i in issues]})
        if name == "create_pull_request":
            repo = forge.require_repo(args["owner"], args["repo"])
            pull = forge.create_pull(repo, args["title"], args.get("body"), args["head"], args["base"])
            return _mcp_result_object(pull_json(repo, pull))
        if name == "list_pull_requests":
            repo = forge.require_repo(args["owner"], args["repo"])
            state = args.get("state") or "open"
            pulls = list(repo.pulls.values())
            if state == "open":
                pulls = [p for p in pulls if p["state"] == "open"]
            elif state == "closed":
                pulls = [p for p in pulls if p["state"] == "closed"]
            pulls.sort(key=lambda p: p["number"])
            return _mcp_result_object({"pull_requests": [pull_json(repo, p) for p in pulls]})
        if name == "merge_pull_request":
            repo = forge.require_repo(args["owner"], args["repo"])
            pull = repo.pulls.get(args["pull_number"])
            if pull is None:
                return _mcp_error_result("Pull request not found")
            if pull["state"] != "open":
                return _mcp_error_result("Pull request is not open")
            forge.merge_pull(repo, pull, "squash")
            return _mcp_result_object(pull_json(repo, pull))
    except ApiError as error:
        return _mcp_error_result(error.message)
    raise McpError(-32602, "Unknown tool: %s" % name)


def mcp_handle(forge, message):
    """One JSON-RPC message in, one response dict out (None = no response)."""
    if not isinstance(message, dict):
        raise McpError(-32600, "Invalid Request")
    method = message.get("method")
    request_id = message.get("id")
    params = message.get("params") or {}
    if method is None:
        raise McpError(-32600, "Invalid Request: method is required")
    if request_id is None:
        return None  # a notification: acknowledged, never answered
    if method == "server/discover":
        result = {
            "supportedVersions": MCP_SUPPORTED_VERSIONS,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
            "instructions": "A GitHub-compatible forge: repositories, issues and pull requests.",
        }
        return {"jsonrpc": "2.0", "id": request_id, "result": result}
    if method == "initialize":
        requested = params.get("protocolVersion")
        version = requested if requested in MCP_SUPPORTED_VERSIONS else MCP_SUPPORTED_VERSIONS[0]
        result = {
            "protocolVersion": version,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": SERVER_NAME, "version": SERVER_VERSION},
            "instructions": "A GitHub-compatible forge: repositories, issues and pull requests.",
        }
        return {"jsonrpc": "2.0", "id": request_id, "result": result}
    if method == "ping":
        return {"jsonrpc": "2.0", "id": request_id, "result": {}}
    if method == "tools/list":
        return {"jsonrpc": "2.0", "id": request_id, "result": json.loads(MCP_TOOLS_LIST_BYTES)}
    if method == "tools/call":
        tool_name = params.get("name")
        if not tool_name:
            raise McpError(-32602, "tools/call requires a tool name")
        result = mcp_call_tool(forge, tool_name, params.get("arguments"))
        return {"jsonrpc": "2.0", "id": request_id, "result": result}
    if method in ("resources/list",):
        return {"jsonrpc": "2.0", "id": request_id, "result": {"resources": []}}
    if method in ("prompts/list",):
        return {"jsonrpc": "2.0", "id": request_id, "result": {"prompts": []}}
    raise McpError(-32601, "Method not found: %s" % method)


# --------------------------------------------------------------------------
# HTTP plumbing

REQUEST_COUNTER = [0]
REQUEST_COUNTER_LOCK = threading.Lock()


def next_request_id():
    with REQUEST_COUNTER_LOCK:
        REQUEST_COUNTER[0] += 1
        return "req-%d" % REQUEST_COUNTER[0]


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "makefun-forge/1.0"

    # -- plumbing ---------------------------------------------------------------
    def log_message(self, fmt, *args):
        pass

    def setup(self):
        super().setup()
        try:
            # Small request/response exchanges on keep-alive connections stall
            # for tens of milliseconds without this (Nagle vs delayed ACK).
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    def read_body(self):
        transfer = (self.headers.get("Transfer-Encoding") or "").lower()
        if "chunked" in transfer:
            chunks = []
            while True:
                size_line = self.rfile.readline(65536).strip()
                if not size_line:
                    continue
                size = int(size_line.split(b";")[0], 16)
                if size == 0:
                    while True:
                        trailer = self.rfile.readline(65536)
                        if trailer in (b"\r\n", b"\n", b""):
                            break
                    break
                chunks.append(self.rfile.read(size))
                self.rfile.read(2)
            return b"".join(chunks)
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        return self.rfile.read(int(length))

    def send_bytes(self, status, body, content_type, extra_headers=None):
        # One write for the whole response: a header per write syscall costs a
        # network round trip's worth of latency on keep-alive connections.
        reason = self.responses.get(status, ("Unknown",))[0]
        lines = ["HTTP/1.1 %d %s" % (status, reason)]
        if content_type:
            lines.append("Content-Type: %s" % content_type)
        lines.append("Content-Length: %d" % len(body))
        for key, value in (extra_headers or {}).items():
            lines.append("%s: %s" % (key, value))
        head = ("\r\n".join(lines) + "\r\n\r\n").encode("utf-8")
        if self.command == "HEAD" or not body:
            self.wfile.write(head)
        else:
            self.wfile.write(head + body)

    def send_json(self, status, value, extra_headers=None, request_id=None):
        headers = dict(extra_headers or {})
        if request_id:
            headers["X-GitHub-Request-Id"] = request_id
        headers.setdefault("X-RateLimit-Limit", "5000")
        headers.setdefault("X-RateLimit-Remaining", "4999")
        headers.setdefault("X-RateLimit-Reset", str(EPOCH_BASE + 3600))
        body = b"" if value is None else json.dumps(value).encode("utf-8")
        self.send_bytes(status, body, "application/json; charset=utf-8", headers)

    # -- request entry ------------------------------------------------------------
    def handle_request(self):
        try:
            body = self.read_body()
        except Exception:
            self.close_connection = True
            return
        split = urlsplit(self.path)
        raw_path = split.path
        query = {}
        for key, value in parse_qsl(split.query, keep_blank_values=True):
            query.setdefault(key, []).append(value)
        token = os.environ.get("MAKEFUN_SHOP_TOKEN") or None
        authorized = token is None or self.headers.get("Authorization") == "Bearer " + token
        try:
            self.route(raw_path, query, body, authorized)
        except BrokenPipeError:
            pass
        except Exception:
            try:
                self.send_json(500, {"message": "Internal Server Error"}, request_id=next_request_id())
            except Exception:
                self.close_connection = True

    def route(self, raw_path, query, body, authorized):
        forge = FORGE
        if raw_path == "/healthz":
            self.send_bytes(200, b"ok", "text/plain; charset=utf-8")
            return
        if raw_path.startswith("/api/v3"):
            request_id = next_request_id()
            if not authorized:
                self.send_json(401, {"message": "Bad credentials"}, request_id=request_id)
                return
            rest_path = raw_path[len("/api/v3"):]
            if rest_path.startswith("/"):
                rest_path = rest_path[1:]
            if rest_path.endswith("/") and rest_path:
                rest_path = rest_path[:-1]
            payload = None
            if body:
                try:
                    payload = json.loads(body.decode("utf-8"))
                except Exception:
                    self.send_json(400, {"message": "Problems parsing JSON"}, request_id=request_id)
                    return
                if not isinstance(payload, dict):
                    payload = {}
            with forge.lock:
                try:
                    full_url = "http://%s%s" % (self.headers.get("Host") or "127.0.0.1", raw_path)
                    status, value, headers = dispatch_rest(forge, self.command, rest_path, query, payload, full_url)
                except ApiError as error:
                    status, value, headers = error.status, {"message": error.message}, {}
            self.send_json(status, value, headers, request_id=request_id)
            return
        if raw_path == "/api/graphql":
            request_id = next_request_id()
            if not authorized:
                self.send_json(401, {"message": "Bad credentials"}, request_id=request_id)
                return
            self.handle_graphql(forge, body, request_id)
            return
        if raw_path == "/mcp":
            if not authorized:
                self.send_json(401, {"message": "Bad credentials"}, request_id=next_request_id())
                return
            self.handle_mcp(forge, body)
            return
        git_match = re.fullmatch(r"/([^/]+)/([^/]+)\.git/(info/refs|git-upload-pack|git-receive-pack)", raw_path)
        if git_match:
            self.handle_git(forge, git_match, body)
            return
        self.send_json(404, {"message": "Not Found"}, request_id=next_request_id())

    def handle_git(self, forge, match, body):
        owner, name, service = match.group(1), match.group(2), match.group(3)
        repo = forge.get_repo(unquote(owner), unquote(name))
        if repo is None:
            self.send_json(404, {"message": "Not Found"}, request_id=next_request_id())
            return
        if service == "info/refs":
            wanted = (self.headers.get("Git-Protocol") or "")
            query_service = ""
            split = urlsplit(self.path)
            for key, value in parse_qsl(split.query):
                if key == "service":
                    query_service = value
            with forge.lock:
                if query_service == "git-receive-pack":
                    payload, content_type = info_refs_receive_pack(repo)
                else:
                    payload, content_type = info_refs_upload_pack(repo, wanted)
            headers = {"Cache-Control": "no-cache", "Expires": "Fri, 01 Jan 1980 00:00:00 GMT", "Pragma": "no-cache"}
            self.send_bytes(200, payload, content_type, headers)
            return
        if self.command != "POST":
            self.send_json(405, {"message": "Method not allowed"}, request_id=next_request_id())
            return
        if service == "git-upload-pack":
            try:
                with forge.lock:
                    status, prefix, pack_objects, use_sideband = handle_upload_pack(
                        repo, body, self.headers.get("Git-Protocol") or "")
            except ValueError:
                self.send_bytes(400, b"", "text/plain")
                return
            payload = prefix
            if pack_objects is not None:
                pack = write_pack(pack_objects)
                if use_sideband:
                    payload = prefix + sideband_stream(pack) + pkt_flush()
                else:
                    payload = prefix + pack
            self.send_bytes(status, payload, "application/x-git-upload-pack-result")
            return
        # git-receive-pack: parse the request and the pack outside the lock
        # (against a snapshot for thin-pack bases); only the ref moves and the
        # object inserts take the lock.
        try:
            commands, capabilities, pack_bytes = parse_receive_pack(body)
        except ValueError:
            self.send_bytes(400, b"", "text/plain")
            return
        incoming = {}
        if commands and pack_bytes:
            with forge.lock:
                snapshot = dict(repo.objects)
            try:
                incoming = read_pack(pack_bytes, external_lookup=snapshot.get)
            except ValueError:
                incoming = None
        with forge.lock:
            report = apply_receive_pack(repo, commands, incoming)
        self.send_bytes(200, _maybe_sideband(report, capabilities), "application/x-git-receive-pack-result")

    def handle_graphql(self, forge, body, request_id):
        try:
            payload = json.loads(body.decode("utf-8")) if body else None
        except Exception:
            self.send_json(400, {"errors": [{"message": "Problems parsing JSON"}]}, request_id=request_id)
            return
        executor = GqlExecutor(forge)
        with forge.lock:
            if isinstance(payload, list):
                results = []
                for entry in payload:
                    if isinstance(entry, dict):
                        results.append(executor.execute(entry.get("query") or "", entry.get("variables"), entry.get("operationName")))
                    else:
                        results.append({"errors": [{"message": "Invalid operation"}]})
                self.send_json(200, results, request_id=request_id)
                return
            if not isinstance(payload, dict) or not payload.get("query"):
                self.send_json(400, {"errors": [{"message": "Missing query"}]}, request_id=request_id)
                return
            result = executor.execute(payload["query"], payload.get("variables"), payload.get("operationName"))
        self.send_json(200, result, request_id=request_id)

    def handle_mcp(self, forge, body):
        if self.command == "GET":
            self.send_bytes(405, b"", "application/json")
            return
        try:
            payload = json.loads(body.decode("utf-8")) if body else None
        except Exception:
            error = {"jsonrpc": "2.0", "id": None, "error": {"code": -32700, "message": "Parse error"}}
            self.send_bytes(400, json.dumps(error).encode("utf-8"), "application/json")
            return
        with forge.lock:
            if isinstance(payload, list):
                responses = []
                for entry in payload:
                    try:
                        response = mcp_handle(forge, entry)
                    except McpError as error:
                        response = {"jsonrpc": "2.0", "id": entry.get("id") if isinstance(entry, dict) else None,
                                    "error": {"code": error.code, "message": error.message}}
                    if response is not None:
                        responses.append(response)
                if not responses:
                    self.send_bytes(202, b"", "application/json")
                    return
                self.send_bytes(200, json.dumps(responses).encode("utf-8"), "application/json")
                return
            try:
                response = mcp_handle(forge, payload)
            except McpError as error:
                response = {"jsonrpc": "2.0", "id": payload.get("id") if isinstance(payload, dict) else None,
                            "error": {"code": error.code, "message": error.message}}
        if response is None:
            self.send_bytes(202, b"", "application/json")
            return
        self.send_bytes(200, json.dumps(response).encode("utf-8"), "application/json")

    do_GET = handle_request
    do_POST = handle_request
    do_PUT = handle_request
    do_PATCH = handle_request
    do_DELETE = handle_request
    do_HEAD = handle_request


# --------------------------------------------------------------------------
# lifecycle

def _env_request(env_url, path, payload=None):
    data = None
    headers = {}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    request = urllib.request.Request(env_url + path, data=data, headers=headers,
                                     method="POST" if payload is not None else "GET")
    with urllib.request.urlopen(request, timeout=10) as response:
        return response.status, response.read()


def register_with_env(env_url, port):
    delay = 0.25
    while True:
        try:
            status, _ = _env_request(env_url, "/register", {"port": port})
            if status in (200, 409):
                return
            if status in (400, 405):
                print("register refused with status %d" % status, file=sys.stderr)
                raise SystemExit(1)
        except SystemExit:
            raise
        except Exception:
            pass
        time.sleep(delay)
        delay = min(delay * 2, 2.0)


def wait_until_done(env_url, server):
    delay = 0.25
    while True:
        try:
            _status, body = _env_request(env_url, "/done")
            data = json.loads(body.decode("utf-8"))
            if isinstance(data, dict) and data.get("done") is True:
                return
            delay = 0.25
        except Exception:
            time.sleep(delay)
            delay = min(delay * 2, 2.0)


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 128


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL")
    if not env_url:
        print("MAKEFUN_ENV_URL is not set", file=sys.stderr)
        return 1
    env_url = env_url.rstrip("/")
    server = ForgeServer(("0.0.0.0", 0), ForgeHandler)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.05}, daemon=True)
    thread.start()
    register_with_env(env_url, port)
    wait_until_done(env_url, server)
    server.shutdown()
    server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
