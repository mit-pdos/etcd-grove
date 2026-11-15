/-
`Tx.Commit` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Tx__Commit.lean` (unfinished until bbolt's invariants are designed).
-/
module

public import Spec.go_etcd_io.bbolt.Api

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

/-- `tx.Commit()` of a write transaction begun at `D = T.base`, with contents `S = T.cur`: the commit point is
the meta page's write (under `metalock`), where the client's update is fired (`D'` is then `D`:
the transaction held `rwlock`). On success the data `S` is committed (synced unless `NoSync`).
On an error the transaction is rolled back and closed either way, and the commit took effect or
not: it did when the meta page reached the file before the error (a failed `fdatasync` after
it; the fork's `2d39641` keeps the freed pages pending then), and the update was fired; else
the update comes back unfired and the committed data is still `D`. (After a failed remap the
database has no mapping: every later `Begin` fails.) The view is a variable with `⌜T.rw⌝`
(round 2: a caller holds `boltTx tx γ 1 T` with `T` built by `setBkt`/`dropBkt`, not a literal).
**A hidden reader slot** (round 2, review 1 finding 2): with `NoFreelistSync` (etcd's Linux
default) the rollback of a failed commit rebuilds the freelist with `db.freepages()`, which
opens a read transaction (`beginTx`: an `mmaplock` reader slot) and forks a goroutine. The
caller pays nothing: `isBolt` keeps one spare reader slot in `rwlock`'s resource, which only
the writer can reach (`Open.spec`'s thread bound leaves room for it). The forked goroutine's
token comes from the fork. That goroutine runs `recursivelyCheckBucket` over the committed tree,
and `freepages` panics on any report: `fileHolds`'s shape facts (exact branch keys, two-element
branches, sorted keys, no shared page, page types) are why it finds nothing (round 3). Splits
during the spill rest on `splitThresholdOk` (D17). The error post's "took effect or not" rests on
D22 (round 11): a meta write is one aligned OS page (`boltPageSize_eq_osPageSize`), which OsFs
writes all-or-nothing in-process, so after a failed `writeMeta` the page holds the old meta or the
whole new one, never a mix; the fork's `rollback` keeps the new one if it became current. -/
abbrev Tx.Commit.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (T : TxView) (Q : IProp GF),
  {{ boltTx (GF := GF) tx γ 1 T ∗ ⌜T.rw = true⌝ ∗
      AU <{ ∃∃ (D' : Data), boltState γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = T.base⌝ ∗ boltState γ 1 T.cur, COMM Q }> }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err; txDone tx ∗
      ((⌜err = GoInterface.nil⌝ ∗ Q) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗
         (Q ∨ AU <{ ∃∃ (D' : Data), boltState γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
                <{ ⌜D' = T.base⌝ ∗ boltState γ 1 T.cur, COMM Q }>))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
