/-
`Bucket.spill` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U9b; used by U10 (`Commit`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__spill.lean` (a `sorry` until U9b).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Commit.MarkCov
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The dirty pages after the spill** (batch 39 of `notes/bbolt-proof-plan.md`, `Commit`'s
`tx.write` premises): every page of `tx.pages` has its buffer and back (`pm`'s domain is `bufs`'s);
each buffer's header names its id, its length is its extent's, and its extent lies in `[2,
pgid)`; its extent's slots are no tree slots of the committed state `C` and not pending in the
freelist `fl'` (so, below the mapping, `W` slots: `wdbOK`'s `W` clause), (maintainer 12, item 4)
not free in `fl'` (so `commitFreelist`'s allocation does not hand them out again), and in no other
buffer's extent (`tx.write`'s slots `bufSlots` without repeats: `bufSlots_nodup_of_disj`). -/
def spillBufs (X' : WX) (C : CommitSt) (fl' : FLPg) : Prop :=
  (∀ id, (X'.t.pm !! id).isSome = (X'.t.bufs !! id).isSome) ∧
  ∀ id pg, X'.t.bufs !! id = some pg → pageId pg = id.toNat ∧
    pg.length = 4096 * (1 + pageOverflow pg) ∧ 2 ≤ id.toNat ∧
    id.toNat + (1 + pageOverflow pg) ≤ X'.t.mv.pgid'.toNat ∧
    ∀ j < 1 + pageOverflow pg, id.toNat + j ∉ treeSlots C ∧ id.toNat + j ∉ pendSlots fl' ∧
      (∀ x ∈ fl'.free, x.toNat ≠ id.toNat + j) ∧
      ∀ id' pg', X'.t.bufs !! id' = some pg' → ∀ j' < 1 + pageOverflow pg',
        id.toNat + j = id'.toNat + j' → id' = id

/-- **What the spill's start needs of the committed state and the root bucket** (batch 43 of
`notes/bbolt-proof-plan.md`, U9t's `StartFacts`; `Commit` gives it from `txExcl`'s writer facts,
`metaCopyOK` and `treeOK`, and `wtxFrac`'s `gensOK`/`wrFacts`, kept by `rebalance`): the committed
tree well-formed, its high-water mark at most the transaction's, and the root bucket's cached
children not the root and distinct. -/
def spillStartOK (X : WX) (w : WDb) : Prop :=
  treeOK w.C ∧ w.C.hwm ≤ X.t.mv.pgid'.toNat ∧
  ∀ B0, X.t.bs !! X.rl = some B0 → (∀ k c, B0.bm !! k = some c → c ≠ X.rl) ∧
    ∀ k k' c, B0.bm !! k = some c → B0.bm !! k' = some c → k = k'

/-- **`tx.root.spill()`** (design §4.2, spill's post): from records satisfying `spillPre`, on
success the spilled tree (`spillOK`: `treeOK`, the writer's data, dropped base pages pending,
new pages allocated and written in `tx.pages`), possibly after remaps (the view re-based),
and `allocate`'s premises for `commitFreelist`'s (`derefPre`, `liveFresh`, `liveReach`; batch 12;
the high-water mark's pages inside the mapping, batch 29); the records agree with the freelist
(`flViewU`, batch 30: `Commit` holds it through `txExcl`; the frees need it), before (not after, U9x5:
false there, the logical tree no longer reaches the base pages the new tree keeps);
the dirty pages `tx.write` takes (`spillBufs`, batch 39); (batch 44.7) the transaction's fields,
its root bucket (present) and its meta copy but the high-water mark kept, on success and on an
error (U10g's gap 7: the rollback after a failed spill needs `writable`, the root bucket, the txid);
(maintainer 13, for `Commit`'s publish: U10l's defect 1 and D-K) the new tree's slots not pending
(the spill frees only the base pages it rewrites) and every slot from the committed mark to the
new one a dirty page's (`markCov`: `tx.pages` only grows; the start takes it, vacuous at
`beginRWTx`'s mark), and (U9w7, for `Commit`'s freelist write: no dirty page on the freed
freelist page's run) every buffer slot free in the starting freelist (`allocate`'s free case) or
at or above the committed mark (its mark case), and (for `Commit`'s `hwbf`) a writer slot that
does not become pending keeps its bytes (`allocate`'s remap keeps every `W` slot's, the frees
change only the freelist). Its start takes `spillStartOK`
(batch 43) and the writer's txid below `2 ^ 63` (U9x5: the new tree's `treeOK`; from the receipts). On an
error (from `allocate`), a `fmtErrorOk` error, the freelist changed by free and allocation steps
only, and either the mapping intact (`wtxW`, `wdbW`) or lost (`wtxLost`, `wdbLost`). -/
abbrev Bucket.spill.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (P : IProp GF),
  spillPre X w.fl → liveReach X → X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms → flViewU X w.fl →
  spillStartOK X w → X.t.mv.txid'.toNat < 2 ^ 63 → markCov X w.C.hwm →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w ∗ poolR K.B.bq K.N P }}
    (App (Val (tx.[Tx, go!"root"] @!! go.GoType.PointerType Bucket.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; poolR K.B.bq K.N P ∗ (
      (⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗
        ⌜spillOK X X' w.C w.fl w'.fl w.wtxid ∧ w'.C = w.C ∧
          derefPre X' ∧ liveFresh X' ∧ liveReach X' ∧
          X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧
          spillBufs X' w.C w'.fl ∧
          X'.t.t = X.t.t ∧ X'.rl = X.rl ∧ (X'.t.bs !! X'.rl).isSome ∧
          X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' } ∧
          (∀ s ∈ treeSlots (spillC X' w.C.pages), s ∉ pendSlots w'.fl) ∧
          markCov X' w.C.hwm ∧
          (∀ s ∈ bufSlots X'.t.bufs, W64 s ∈ w.fl.free ∨ w.C.hwm ≤ s) ∧
          ∀ s ∈ w.W, s ∉ pendSlots w'.fl → w'.wb s = w.wb s⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧
          X'.v.pages = X.v.pages ∧ X'.t.t = X.t.t ∧ X'.rl = X.rl ∧ (X'.t.bs !! X'.rl).isSome ∧
          X'.t.mv = { X.t.mv with pgid' := X'.t.mv.pgid' }⌝ ∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w')))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
