# dsv-hraft: hashicorp/raft from dsverify-lab's hraft-4 (#48)

The plan is `/shared/tmp/ps2/hraft/PLAN.md`, agreed on mit-pdos/etcd-grove#48 by coordinator-E
(comment 7225501351). Its stages are:

- S0: the translation;
- S1: the kit over net/rpc;
- S2/S3: the port of the lab's proof;
- S4: the transport;
- S5/S6: the server machine, linearizability and `hraft_nocrash_robust`;
- S7+: crash and restart.

## Status

**S0 (2026-11-27, branch `hraft-s0/2026-11-27`): done.** The fork is in-tree. It is translated into
the part `Dsverify/` by project `dsv-hraft` (`etc/dsv/hraft.py`), and its two packages' initializers
are generated and proved (`etc/gen-init.py`). There is no proof of any function yet, no `Link` and
no tcb collection: the collection `etc/tcb-collections/dsv-hraft.txt` comes with the first `Link`.

The trust added is none:

- no goose `[[skip]]` or names-only entry (there is no `Dsverify/Code/github_com/hashicorp/**.toml`);
- no `TrustedCode`, axiom, `sorry` or `HYP_INITS`.

**P1-P3 (2026-11-27): the lab's specs and defs ported** ("Port of the lab proof" below); still no proof of a
function, no axiom, `sorry` or premise.

## Provenance

| | |
|---|---|
| Go | `examples/dsverify/hraft/` (Go module `github.com/hashicorp/raft`, MPL-2.0 `LICENSE` kept), copied from dsverify-lab `examples/hraft/fork/raft` at lab `c39f136`: the verification fork at commit `02f88d5` (branch `hr-stage4`), on hashicorp/raft v1.8.0 `0f543c0`. The fork's history is the lab's `examples/hraft/history/fork-raft.bundle`. |
| lab proof | dsverify-lab `examples/hraft/proof/` at `241f27e` (tag `final`, Perennial `4c8617a9`), not yet ported |

## Go changes against the lab fork `02f88d5`

1. **The in-process harness is removed:** `examples/{inproc,recorder,kvmodel,hr3}`. Porcupine is dropped
   from `go.mod`, along with its `replace`. `go.mod` gets a provenance comment.
2. **`examples/snapstore/reader.go`: inproc's `Reader`, `NewReader`, `ReadAll` and `copyBytes` move into
   `snapstore`.** `Store.Open` returned `inproc.NewReader(...)`. The code is unchanged apart from the
   package; S1's transport can use `snapstore.ReadAll`/`NewReader`. The lab's proofs of them
   (`examples/inproc/{NewReader,Reader__Read,Reader__Close,ReadAll}.lean`) move to `snapstore`'s
   namespace in the port.
3. **The goose select-send bug (lab D16/D22; mit-pdos/perennial#713).** goose translates a `select`
   send case's value without converting it to the channel's element type (Perennial
   `goose/goose.go:2448`, `ctx.expr(c.Value)`). The fork already converts explicitly at all five such
   sends (`raft.go`'s `case r.fsmMutateCh <- interface{}(...)`, lab D16). Only their comments change:
   they cited the lab's `verify/notes/decisions.md D16` and now cite the goose bug. The lab's other
   instance (D22, `inproc`'s pipeline on a `chan raft.AppendFuture`) went with inproc. S1's
   transport must convert at every select send to an interface-typed channel. The other select sends
   in raft send a value of the element type exactly (checked: `applyCh`, `verifyCh`, ..., the
   `chan bool`/`chan struct{}` notifications).

The fork's other comments citing `verify/notes/decisions.md` (D17 in `replication.go`, D33 in
`api.go`) refer to the lab's `examples/hraft/proof/notes/decisions.md`.

## Translation

- Project `dsv-hraft`: `local=examples/dsverify/hraft`, `root=Dsverify`, lean root
  `github.com/hashicorp/raft=Dsverify`, packages `.` and `./examples/snapstore`, owned
  `github_com/hashicorp`. S1 adds the kit's packages and Net's roots (craq's list).
- Modules:
  - `Dsverify.Code.github_com.hashicorp.raft`, which re-exports `.chunk0`..`.chunk3`;
  - `Dsverify.GeneratedProof.github_com.hashicorp.raft` (`.chunk1`..`.chunk6`);
  - `Dsverify.{Code,GeneratedProof}.github_com.hashicorp.raft.examples.snapstore`.

  The namespace is `Perennial.github_com.hashicorp.raft` (`.examples.snapstore`), as the lab's.
- Diff against the lab's `HrVerify/Code` with `HrVerify` replaced by `Dsverify`:
  - `raft.lean` and chunks 1–3 are identical;
  - `chunk0` differs only where goose now inlines imported constants (`time.Millisecond`/`time.Second`
    become `#(W64 1000000)`/`#(W64 1000000000)`, 9 places: `DefaultConfig`, `ValidateConfig`,
    `snapshotName`). This is BUMP.md's "goose inlines imported constants": the lab proofs that
    `unfold`/`simp` those constants need fixing;
  - `snapstore` differs by the reader move.

## Package facts and initializers

`Dsverify/Proof/github_com/hashicorp/raft{,/examples/snapstore}/Base.lean` hold the facts; the `Init.lean`
files are generated (`etc/gen-init.py`, configured by `etc/dsv/hraft.py`'s `special`), never edited by hand.

- **raft** (since P3): the lab's `pkgGlobals`, statement unchanged: the error variables hold pairwise distinct
  errors, each `errors.newVar` of its message (`errVals`, `isRaftErr`); the three stable-store keys hold
  read-only bytes; `nextObserverID` is in an invariant. Its proof is the lab's `initialize.lean`, moved into
  `hraft.py`'s `raft_cfg` (the generated steps) and `InitLemmas.lean` (its lemmas: `exclS` keeps three quarters
  of each new `errorString`'s field, so the variables' values are distinct, `exclS_nodup`; `wp_New_excl` also
  returns the persistent quarter, which Perennial's `errors.newVar` now holds).
- **snapstore**: the lab's `isInit` (its two `errors.newVar`s, named), from its `errors.New` variables, as craq's.

## Port of the lab proof (S2/S3)

The port is step by step (`/shared/tmp/ps2/hraft/PLAN.md`, section 2; the drift catalogue
`/shared/tmp/ps2/hraft/DRIFT.md`); every ported file starts with its lab path.

- **P1/P2** (`bc8f931ab5`): `proto/`, `gprot/`, `Threads/` (QTok re-proved over leveled thread tokens).
- **P3** (branch `hraft-p3/2026-11-27`): every spec (`Dsverify/Spec/github_com/hashicorp/raft/`, 171 files:
  the lab's but `initialize`; `examples/snapstore/`: 9 of the lab's, and the 5 of the readers that moved from
  inproc, `NewReader`, `Reader.Read`, `Reader.Close`, `ReadAll`, `copyBytes`, now snapstore's) and the defs
  modules (`EncodingLemmas`, `iface/`, `core/`, `leader/`, `handlers/`, `main/`, `DeferRespond`, the top-level
  `*Base`, `Repl*`, `Snap*`). Statements unchanged. Fixes: channel AUs are `|NC=…` now (`iapply
  ncfupd_of_fupd` before an `iinv`), and `lowMask_8`'s `bv_decide` is a kernel proof. The lab's `KitStd.Spec.io.Copy`
  becomes `Spec/io/Copy.lean` in the main tree (no general `io.Copy` spec existed), still to prove over
  Perennial's `io.Copy` body (P4). Not ported (the dropped harness): `inproc` (but its readers), `recorder`,
  `kvmodel`, porcupine, `hr3`, `Goal`, `DsvStatement`.
- **P4** (next): the 185 code-proof files, in four independent groups (`/shared/tmp/ps2/hraft/P4-SPLIT.md`).
  Two lab axioms are to be proved there: `fmt.wp_Errorf_tnErr` (`FmtErrorf.lean`) and `io.Copy`'s.
