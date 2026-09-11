# etcd-grove: verifying etcd with Perennial

[![CI](https://github.com/upamanyus/etcd-grove/actions/workflows/ci.yml/badge.svg)](https://github.com/upamanyus/etcd-grove/actions/workflows/ci.yml)

etcd-grove is a fork of [Perennial](https://github.com/mit-pdos/perennial)
dedicated to verifying [etcd](https://github.com/etcd-io/etcd), starting with
its Raft implementation.

Perennial is a framework for verifying correctness of systems with both
concurrency and crash-safety requirements, including recovery procedures. It
also includes Grove, an extension for verifying distributed systems. The
program logic is built on top of [Iris](https://iris-project.org/), and
[Goose](https://github.com/goose-lang/goose) is used to translate Go programs
into a model in Rocq.

Everything upstream Perennial provides is still here; this fork adds the etcd
proofs and drops upstream-only release/paper infrastructure. See
[CONTRIBUTING.md](./CONTRIBUTING.md).

## Where the etcd proofs live

Goose translates Go import paths into directory paths, so the etcd material is
in predictable places:

- `new/code/go_etcd_io/` — Goose output for etcd and Raft. **Auto-generated; do
  not edit.**
- `new/generatedproof/go_etcd_io/` — auto-generated boilerplate proofs. **Do not
  edit.**
- `new/proof/go_etcd_io/raft/` — the Raft proof. `v3.v` holds the per-function
  proofs; `v3_proof/` holds the protocol-level development (`base.v`,
  `protocol.v`, `readonly.v`).
- `new/proof/go_etcd_io/etcd/` — proofs for the rest of etcd (client, server,
  api, pkg).

The Go sources being verified are not in this repo. They are tracked in
separate forks, wired up in `new/etc/update-goose-new.py` and
`etc/ci-goose-check.py`:

- [upamanyus/etcd-raft](https://github.com/upamanyus/etcd-raft) (branch `goose`)
- [upamanyus/etcd](https://github.com/upamanyus/etcd) (branch `goose`)

Regenerate the Goose output with `new/etc/update-goose-new.py`; CI checks it is
in sync with `etc/ci-goose-check.py`.

## Notes for humans and agents

Durable project context — current status, design decisions, gotchas, and a
session journal — lives in [`notes/`](./notes/README.md), as plain markdown
with no tooling around it. Read [`notes/STATUS.md`](./notes/STATUS.md) first,
and update the notes when you finish. Coding agents are pointed at the same
place by [`AGENTS.md`](./AGENTS.md).

## Compiling

We develop against the latest stable Rocq and maintain compatibility with Rocq
master.

Install the dependencies with
`opam pin add -n .; opam install --deps-only ./perennial.opam`. Re-run this
command after running `git pull` to get the correct version of the dependencies.
Then, compile with `make`.

See [docs/opam.md](docs/opam.md) for some more details on opam.

Alternatively, if you use `nix`, the flake in this repo replaces the need for an
opam switch. Simply run `nix develop` to get a development shell with all the
correct dependencies. Editor integration can be achieved with a direnv
integration by setting `.envrc` to `use flake`.

## New goose

Perennial is in the process of migrating to "new Goose", a
backwards-incompatible change to Goose. All of the etcd work uses new goose,
which lives in `new/`, with the important caveat that new goose is built on top
of the core `goose_lang/` language and its instantiation.

## Source organization

`src/`

- `program_logic/` The main library that implements the crash safety reasoning
  in Perennial. This includes crash weakest preconditions, crash invariants,
  idempotence, and crash refinement reasoning.

- `goose_lang/` A lambda calculus with memory, concurrency, and an "FFI" to some
  external world, which can be instantiated to provide system calls specified
  using a relation over states.

  This language is the target of Goose and thus models Go and also implements
  the Iris `language` and Perennial `crash_lang` interfaces for proofs using
  Perennial.

- `program_proof/`

  Old-goose proofs about programs. At this point, there are enough that it is
  difficult to keep them documented here.

- `Helpers/`
  - `Integers.v` Wrapper around `coqutil`'s word library for u64, u32, and u8.
  - `Transitions.v` A library for writing relations in a monadic, combinator
    style.
  - other files are generally standard library extensions, like `List.v`.

- `algebra/`, `iris_lib/`, `base_logic/`

  extensions to Iris.

`new/` holds the new-goose development, including all of the etcd work. See
`new/proof/PERENNIAL_PROOF_TUTORIAL.md` for a tutorial on writing program
proofs and `new/proof/PERENNIAL_PROOF_REFERENCE.md` for a reference.

`goose/` is the Goose translator itself (Go source). Note that its Go module
path is still `github.com/mit-pdos/perennial`, which keeps this fork mergeable
with upstream; it has no bearing on the etcd proofs.

## Upstream

To pull in upstream Perennial changes:

```sh
git remote add upstream https://github.com/mit-pdos/perennial.git  # once
git fetch upstream
git merge upstream/master
```

## Publications

Perennial and Grove are described in the following papers from the upstream
project.

Grove (as well as some examples verified using it) is described in
"[Grove: a Separation-Logic Library for Verifying Distributed
Systems](https://pdos.csail.mit.edu/papers/grove:sosp23.pdf)" from SOSP 2023.

"[Verifying vMVCC, a high-performance transaction library
using multi-version concurrency
control](https://pdos.csail.mit.edu/papers/vmvcc:osdi23.pdf)" corresponds to the
proof in `program_proof/mvcc`.

Goose is briefly described in a CoqPL extended abstract and associated talk,
"[Verifying concurrent Go code in Coq with
Goose](https://www.chajed.io/papers/goose:coqpl2020.pdf)". You can also read
chapter 7 of
[Tej Chajed's PhD thesis](https://www.chajed.io/papers/tchajed-thesis.pdf).

The verified interpreter and test framework for Goose is described in Sydney
Gibson's masters thesis,
"[Waddle: A proven interpreter and test framework for a subset of the Go
semantics](https://pdos.csail.mit.edu/papers/gibsons-meng.pdf)".

Perennial 1 is described in the SOSP paper,
"[Verifying concurrent, crash-safe
systems with Perennial](https://www.chajed.io/papers/perennial:sosp2019.pdf)".
