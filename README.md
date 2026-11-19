# makefun-forge

[![make.fun bounty](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/konzlodon74-dot/github-core-clone-01/rank.svg)](https://make.fun/bounty/github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/konzlodon74-dot/github-core-clone-01/reward.svg)](https://make.fun/bounty/github-core-clone-01)

Entry for the make.fun bounty [Build a GitHub-compatible git forge](https://make.fun/bounty/github-core-clone-01).

A GitHub-core git forge in a single Python file, standard library only.

One process serves, from one in-memory store:

- **git smart HTTP** at `/{owner}/{repo}.git` — upload-pack protocol v2
  (capability advertisement, `ls-refs`, `fetch` with shallow/deepen support)
  and receive-pack v0 with per-ref report-status. Git objects, packfiles and
  deltas are implemented from scratch; no git binary is needed.
- **REST v3** under `/api/v3` — repositories, the contents API, labels,
  issues, comments, branches, commits, git refs and pull requests including
  a file-level three-way squash/merge.
- **GraphQL v4** at `/api/graphql` — queries, mutations and introspection
  over the same store, with opaque global ids and cursor pagination.
- **MCP** at `/mcp` — JSON-RPC Streamable HTTP (`server/discover` plus the
  `initialize` handshake) with tools for repositories, issues and pull
  requests, acting on the same store as REST and GraphQL.

The forge never reads the wall clock for anything it serves: timestamps come
from a fixed epoch plus a monotonic counter, so identical request sequences
produce identical bytes.

## Running

```sh
MAKEFUN_ENV_URL=http://127.0.0.1:9000 MAKEFUN_SHOP_TOKEN=secret python3 main.py
```

The process binds an ephemeral port, registers it with
`POST $MAKEFUN_ENV_URL/register`, answers `GET /healthz`, and polls
`$MAKEFUN_ENV_URL/done` until the trial ends, then exits 0.

API requests authenticate with `Authorization: Bearer $MAKEFUN_SHOP_TOKEN`;
the token's viewer owns every repository. Git clone/push endpoints speak the
plain smart-HTTP protocol so a stock git client works against them.
