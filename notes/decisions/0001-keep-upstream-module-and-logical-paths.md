# 0001. Keep upstream Go module and Rocq logical paths

- **Date:** 2026-09-11
- **Status:** accepted

## Context

`etcd-grove` is a fork of `mit-pdos/perennial`. When setting the fork up, the
obvious sweep is to rename every `mit-pdos/perennial` reference to
`upamanyus/etcd-grove`. Two of those references are not URLs but identifiers
the build depends on:

- the Go module path `github.com/mit-pdos/perennial` in `go.mod`, which Goose
  embeds in its output, so it appears in ~71 files and names three generated
  directory trees (`new/code/github_com/mit_pdos/perennial/...`,
  likewise under `new/generatedproof/`, and `goose/testdata/**/*.gold.v`);
- the Rocq logical paths `Perennial` and `New` in `_RocqProject` and
  `perennial.opam`, which every `From Perennial Require` / `From New Require`
  in the repo depends on.

## Decision

Leave both alone. Rebrand only things that identify *the repository* — README
and its CI badge, `perennial.opam` metadata (homepage, bug-reports, dev-repo,
maintainer, description), `CONTRIBUTING.md`, `docs/`, the flake description,
and the GitHub workflows.

## Alternatives considered

**Rename the Go module to `github.com/upamanyus/etcd-grove`.** Rejected on
cost/benefit. The benefit is zero for the etcd work: the etcd Go code lives in
separate repos and translates to `go_etcd_io/...` paths, so this module path
only ever names Goose's own test fixtures. The cost is real and recurring —
every future `git merge upstream/master` would conflict across all of
`goose/*.go` and every `.gold.v`, since Goose is actively developed upstream.

**Rename the Rocq logical path `Perennial` → `EtcdGrove`.** Rejected outright:
it rewrites the import line of essentially every `.v` file in the repo,
guarantees a conflict on every upstream merge, and buys nothing. The framework
genuinely is Perennial.

Also considered and rejected: renaming `perennial.opam` to `etcd-grove.opam`.
`flake.nix` derives its package name from that filename via opam-nix, and
`etc/install.sh`, the Makefile, CI, and the docs all name it. The package still
installs logpaths `Perennial` and `New`, so the name is not wrong.

## Consequences

- Upstream merges stay mechanical: `git fetch upstream && git merge
  upstream/master` touches only files we actually edited.
- Anyone reading `go.mod` or an import line sees `mit-pdos/perennial` and may
  think the fork is misconfigured. `README.md` says why, and so does this file.
- If the fork ever diverges enough that upstream merges stop happening, this
  becomes cheap to revisit — it is a scripted `sed` plus three `git mv`s plus a
  Goose regeneration. Supersede this record rather than editing it.
