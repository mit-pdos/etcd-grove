/-
`Commit`'s missing shared facts (U10g of `notes/bbolt-proof-plan.md`), stated as `Commit` needs
them; each is reported to the maintainer (owner in its docstring). A `sorry` here is a gap in a
shared statement, not in `Commit`'s proof.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Shape
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Tx__commitFreelist
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **Gap 1**: a writer's records at `Commit` reach every live object (`rebalance`'s and
`spill`'s premise `liveReach`). Nothing carries it: `wOK` (`liveOK`) says what is live, not that
it is reached from the root bucket through `buckets` and `children`. True of every writer (its
operations only add reached objects: `Bucket.Bucket_w` caches the child in `b.buckets`, `node`
materializes under its parent), so `wOK` (or `wtxFrac`'s facts) should carry it. -/
theorem wOK_liveReach (X : WX) (h : wOK X) : liveReach X := by
  sorry

/-- **The writer's meta copy** (`tx.meta`, `beginRWTx`'s copy of the current meta with the txid
bumped) at `Commit`'s start, as `Commit` uses it: magic, version and page size the committed
meta's (`writeMeta`'s `metaValid`, `commitStep_commit`'s `hps`), the high-water mark and the synced
freelist page the committed state's (`opgid`, the old freelist page freed). -/
def wMetaOK (X : WX) (w : WDb) : Prop :=
  X.t.mv.magic'.toNat = boltMagic ∧ X.t.mv.version'.toNat = boltVersion ∧
  X.t.mv.pageSize'.toNat = 4096 ∧ X.t.mv.pgid'.toNat = w.C.hwm ∧ metaFlpg X.t.mv = w.C.flpg

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Gap 2** (U8, 37.14's "rebalance/spill" corollary of `Inv/ShapeOps.txShape_sub`): the page tokens across
`rebalance` (the records' tokens a sub-multiset of the old: a freed page's dropped). -/
theorem txShape_rebalOK (γ : GName) (X X' : WX) (fl fl' : FLPg) (txid : w64)
    (extra : GMap Nat Unit) (h : rebalOK X X' fl fl' txid) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  sorry

/-- **Gap 3** (U9, 37.14's "rebalance/spill" corollary of `Inv/ShapeOps.txShape_sub`): the page tokens across
`spill` (new pages are no view pages; the view's pages unchanged, `spillOK`). -/
theorem txShape_spillOK (γ : GName) (X X' : WX) (C : CommitSt) (fl fl' : FLPg) (txid : w64)
    (extra : GMap Nat Unit) (h : spillOK X X' C fl fl' txid) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  sorry

/-- **Gap 4**: nothing relates the writer's meta copy `X.t.mv` to the committed state `w.C` (only
its txid: `txClean`). `txExcl`'s writer facts should carry `wMetaOK X w` (true from `beginRWTx`'s
copy until `Commit`: no operation before it writes `tx.meta`). -/
theorem wtx_wMetaOK (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) :
    wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w ⊢ ⌜wMetaOK X w⌝ := by
  sorry

/-- **Gap 5**: nothing says the writer's `tx.commitHandlers` is nil (`beginRWTx`'s zero value;
`OnCommit` is outside the verified API). `Commit` calls each handler after the close: with an
unknown list it would run unknown functions. `wtxFrac`'s facts (or `txClean`) should carry it. -/
theorem wtx_handlers_nil (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜X.t.t.commitHandlers' = slice.nil⌝ := by
  sorry

omit [GooseSemantics] go_gctx hos sem in
/-- The page tokens do not see the transaction's meta copy or dirty pages (`bs`, `v` unchanged). -/
theorem txShape_congr (γ : GName) (X X' : WX) (extra : GMap Nat Unit) (hv : X'.v = X.v)
    (hb : X'.t.bs = X.t.bs) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  unfold txShape; rw [hv, hb]

end res

end bbolt
end EtcdGrove
end Perennial
