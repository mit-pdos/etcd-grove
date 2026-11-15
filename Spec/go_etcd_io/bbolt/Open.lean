/-
`Open` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Open.lean` (unfinished until bbolt's invariants are designed).
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import Spec.go_etcd_io.bbolt.Options
public import Spec.go_etcd_io.bbolt.Logger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `bolt.Open(path, mode, opts)`: the database the file holds, open, or an error.
- The options are read and given back (`Open` copies what it keeps); options under which the
  specs hold (`OptsM.ok`); a logger bbolt may call.
- On success, the handle `isBolt db γ` and all of the committed data `boltState γ 1 D`: the
  client decides where it lives (a lock, an invariant). The file is the database's until
  `Close` (and not given back: `notes/bbolt-spec-decisions.md`, D9).
- On an error, the file is lost to the caller (`init` may have written part of it).
- The namespace `N` is the caller's (round 2): bbolt's invariants are allocated in it, and the
  database's updates are masked by `⊤ \ ↑N` (`γ.ns = N`). Disjoint from OsFs's `osN` (round 3;
  reason restated in round 4): bbolt's own invariants in `N` stay open across OsFs steps (every
  OsFs spec needs `↑osN ⊆ E`), e.g. the meta's `pwrite` under `metalock`. The commit update itself
  fires just *after* that `pwrite`, still under `metalock` (opening it takes the mask to `∅`),
  which suffices since readers read the meta only under `metalock`.
- The bounds the owner needs (`notes/bounds-plan.md`, B1): fewer than `2 ^ 29` live threads
  (round 2: was `2 ^ 30`): the read transactions, each holding a thread's token, plus one spare
  slot for the writer's `freepages` (`Tx.Commit.spec`) must fit `mmaplock`'s
  `actualMaxReaders = 2 ^ 30 - 1`, which `threadBound ≤ 2 ^ 30 - 1` would already give; `2 ^ 29`
  is a chosen power of two (instance search reaches it from every closed result's `2 ^ 28`), not
  a necessity. Fewer than `2 ^ 62` receipts, so that the commits' txids (below `2 ^ 62` in a file
  `fileHolds` accepts) stay below `2 ^ 63` and do not wrap. -/
abbrev Open.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (N : Namespace) (path : GoString) (mode : w32) (opts : Loc)
    (dq : DFrac) (o : OptsM) (D : Data) (R : Roots) (V : Hist),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osTree (DFrac.own 1) R V ∗ pathHolds R V path D ∗
      optsAt opts dq o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #path)) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dq o ∗
      (∃ V', osTree (DFrac.own 1) R V' ∗ ⌜V' = V ∨ ∃ e, V' = V.push e⌝ ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : BoltName) (i : Ino),
            ⌜γ.ns = N ∧ lookupH R V' path = some (.file i)⌝ ∗ isBolt db γ ∗ boltState γ 1 D) ∨
         ⌜err ≠ GoInterface.nil⌝)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
