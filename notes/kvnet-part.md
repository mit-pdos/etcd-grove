# The part `KvNet/`: where kvnet's proof lives

Started 2026-11-21 (claim issue #22; `notes/kvnet-proof-plan.md`, decision D2). kvnet
(`examples/raft/kvnet`, a Go module of its own whose `go.mod` replaces raft by `RAFT_NOAX_REV`) needs,
in one import closure:

1. raft-noax's translation, specs and proofs (the part `RaftNoAx/`, itself copied from the main tree);
2. the net extension's bodied `net` (the part `Net/`);
3. the bodied `durable` over the Linux file extension fsExt (the part `WalTester/`);
4. kvnet's and kvcheck's own translations.

Each of 1-3 declares main-tree names (raft's, `net`'s, `durable`'s), so none of them can be imported
beside the main tree's versions or beside each other's copies of shared modules (`os`'s
initializers, `PkgInitExt`). `KvNet/` is a fifth tree holding all of them, made by generators as
`RaftNoAx/` is (`notes/raft-noax-part.md`); nothing outside it imports it.

## How the part is made

1. **Translations** (`etc/goose.py`): project `kvnet` (root `KvNet`, packages `.` and `./kvcheck` of
   `examples/raft/kvnet`, no Goose configuration), and a `Part` into `KvNet` of each project whose
   package it needs: raft-noax (raft's five packages, configured by `KvNet/Code/go_etcd_io/raft/**.toml`),
   net (`net` alone, `KvNet/Code/net.toml`), durable (the bodied translation, as `WalTester/`'s: no
   configuration) and etcd (`walpb`, which raft's `PbSchema` names). kvnet's lean roots send raft,
   `net` and `durable` to `KvNet`, lintest and porcupine to the main tree (`github.com/mit-pdos/etcd-grove=`,
   `github.com/anishathalye/porcupine=`), the file layer (`os`, `path/filepath`, ...) to the main
   tree's, as every project's. Each part translation is its source part's up to the prefix (checked
   2026-11-21: `RaftNoAx.`/`Net.`/`WalTester.` replaced by `KvNet.`, identical).
2. **Copies** (`etc/copy-part.py`, generalized to parts with several source trees): the part's
   sources are `Net/`, `WalTester/`, `RaftNoAx/` and the main tree, in that order; a module path
   means the part's own file if it has one, else the first source tree's. Its roots are its own
   hand-written modules under `KvNet/Spec` and `KvNet/Proof` and gen-init's modules for it. Every module
   of their closure that reaches a seed (a translation of the part, a module of a source part, a
   gen-init module of the part) is copied, imports re-prefixed to `KvNet.`, the source part's own
   copy line replaced by one naming it (`-- The copy for the part `KvNet/` of `RaftNoAx/Spec/...``).
   The trusted code, manual proofs and Goose configuration of a translated package come from the
   source tree whose goose piece translates the same package (`net`: `Net/`; raft and walpb:
   `RaftNoAx/`; `durable`: `WalTester/`, none). A module two source parts both have is a clash: the
   script stops unless gen-init writes it for the part (now: `os`'s initializers and `PkgInitExt`,
   `Net/` and `RaftNoAx/`; `durable`'s initializer, `RaftNoAx/` and `WalTester/`).
3. **Package initializers** (`etc/gen-init.py`, `KVNET_INITS`, `kvnet_inits`): the initializers of
   RaftWitness's list (porcupine, lintest, the protobuf runtime, `os` and its imports), `net`'s
   (`Net/`'s configuration, `NET_SPECIAL`), `durable`'s (the bodied one's, `WT_SPECIAL`) and its
   imports' (`internal/filepathlite`, `path/filepath`), generated from the part's translation and
   copies over the main tree's, and a `PkgInitExt` that is the main tree's with the part's raft.
4. **Links**: none yet (no proof of the part links anything); kvnet's will be `etc/gen-link.py` modes
   as RaftNoAx's.

Also: `lakefile.toml` (lean_lib `KvNet`, a default target), `etc/gates.sh` and CI
(`etc/copy-part.py --check` checks both parts; `etc/goose.py --check` and `etc/gen-init.py --check`
cover the new project, parts and initializers).

To regenerate after a source moves (the order matters on the first run: gen-init reads the copies'
instances, copy-part reads gen-init's imports; a second round is a no-op):

    etc/goose.py --project raft-noax --project net --project durable --project etcd --project kvnet
    etc/copy-part.py --part KvNet
    etc/gen-init.py
    etc/copy-part.py --part KvNet    # (and gen-init again if it changed anything)

A change to a raft file the part copies is made in the main tree (or in `RaftNoAx/`'s own file),
then `etc/copy-part.py` (both parts) carries it here. A part file without the copy line is the
part's own (as in `RaftNoAx/`).

## Decisions taken

- **Reconciling the two `os` initializers.** `Net/Proof/os/Init.lean` and `Proof/os/Init.lean` (and
  `RaftNoAx/`'s copy) prove the same thing; they differ only in which `PkgInitExt` they import
  (`Net/`'s has no raft). The part has one of each, generated, over its own `PkgInitExt` (raft
  included: raft's initializer is an `ExternalInit`). The same for `syscall`, `io/fs`,
  `internal/poll`, `internal/syscall/unix`. `durable`'s is the bodied one's (`WalTester/`'s
  configuration), not `RaftNoAx/`'s (the trusted `durable` over `durableExt`, which kvdurable uses).
- **The protobuf runtime's `IsPkgInit` instances** (`pragma`, `impl`, `protoimpl`, `protoreflect`,
  facts `True`) are in the main tree in etcd cache's `Base.lean`, whose imports reach etcd's
  translation and, through grpc's, the main tree's names-only `net`: a clash with the part's `net`.
  The part declares them itself (`KvNet/Proof/google_golang_org/protobuf/PkgInit.lean`, its own
  file), and gen-init's initializers of those packages name it (the first instance in the part's
  proofs wins). The general fix is to move them in the main tree into a protobuf module that cache's
  `Base` imports; that rebuilds the 7635 modules importing `Base` (`etc/importers.py --count`), so it
  waits for a change that rebuilds them anyway; the part's file then goes. **Follow-up** (accepted
  2026-11-21 by the coordinator, issue #22): move the four instances to a main-tree protobuf module
  when a rebuild of `Base`'s importers is acceptable, then delete the part's file.
- **kvnet's and kvcheck's own initializers and `PkgTable`** are not generated yet: gen-init needs their
  `IsPkgInit` instances (their facts: `StatNames`' array literal), which belong to kvnet's proof. Add
  the packages to `KVNET_INITS` (and the program to a `PkgTable`) when the instances exist.

## What the part holds (2026-11-21)

The closure of the smoke test `KvNet/Proof/.../examples/raft/kvnet/Imports.lean` (kvnet's and
kvcheck's translations, raft-noax's `Spec.go_etcd_io.raft.v3.Api` and `RestartNode` specs, `net.Listen`'s
spec, `durable.Write`'s spec):

| written by | files | lines | what |
|---|---|---|---|
| etc/goose.py | 10 + 14 | 52.6k | `Code/`, `GeneratedProof/`: raft-noax's raft, walpb, `net`, the bodied `durable`, kvnet, kvcheck |
| etc/copy-part.py | 179 (+ 6 `.toml`) | 94.7k | from `RaftNoAx/` 171 (raft's node API and what it stands on: `InvNode*`, `InvApi`, `Protocol/`, the trusted code and manual proofs of raftpb and walpb, ...), from `Net/` 4 (`net`'s trusted code, manual proof, `Base`, `Listen`'s spec), from `WalTester/` 3 (`durable`'s `Defs`, `PkgInit`, `Write`'s spec); none from the main tree |
| etc/gen-init.py | 16 | 1.6k | the initializers listed above and `PkgInitExt` |
| own | 2 | 0.1k | the smoke test `Imports.lean`; `Proof/google_golang_org/protobuf/PkgInit.lean` (above) |

220 modules, 149k lines. **Built** 2026-11-21: `lake build KvNet`, 2627 jobs (the 220 of the part, the
rest the main tree's and Perennial's it imports, up to date), 6m09s wall from a build where only the
part was missing (16 min of CPU; the critical path is raft's invariant chain, 45 compiles, 6m00s:
more cores do not help), peak 2.1 GB per process (`TracedCap`); `.lake/build` grows by 538 MB (379 MB
`lib/lean/KvNet`, 159 MB `ir/KvNet`). No axiom or `sorry` of its own; its copies' axioms are the
generated `opaqueInitsOk` of `path/filepath`'s initializer (as the main tree's) and none other; the part
has no `Link` or `Results`, so `etc/tcb-report.py` has no root in it.

As kvnet's proof grows, its modules become roots (they are the part's own files) and the copies
follow their imports.
