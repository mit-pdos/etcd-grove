/-
`TxExclWGap` (what a writer's `Rollback` needs of its exclusive part) and `txExclWGap_holds`, out of
`Tx__Rollback.lean`'s proofs so that the write modules (`Write/DelBktXcl.lean`) import them without
the proofs (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Rollback
public import Spec.go_etcd_io.bbolt.Tx__Rollback_r
public import Proof.go_etcd_io.bbolt.Inv.Ctx

public import Proof.go_etcd_io.bbolt.Txn.WRoll
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Rollback
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **What a writer's `Rollback` needs of its exclusive part** (U5c's finding; batch 34 gave
`txExcl`'s writer branch the missing parts, `txExclWGap_holds`): with the agreed state's half, the
whole agreed state, the `done` half, `rwlock`'s token, the writer side's half of the closed flag,
and the writer side as `Commit` sees it (`wdbW`), with its page tokens, `flViewU` and (batches 43.1,
44.4) `metaCopyOK` and `treeOK`. -/
def TxExclWGap : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (K : BC) (tx : Loc) (r : TxReg) (X : WX) (c : TxViewC), r.db = K.db →
    txExcl (GF := GF) K.B K.p K.sp K.t0 tx r ∗ ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ⊢
      ghostVar r.n.v 1 (c, TxX.wr X) ∗ ghostVar r.n.done (1 : Qp).half false ∗
      sync.ownMutex K.db.[DB, go!"rwlock"] ∗ ghostVar K.B.cls (1 : Qp).half false ∗
      ∃ (w : WDb) (extra : GMap Nat Unit), wdbW K tx X.v w ∗ txShape r.n.pg X extra ∗
        ⌜flViewU X w.fl ∧ metaCopyOK X.t.mv w.C ∧ treeOK w.C⌝
/-- **`TxExclWGap` holds** (batch 34: `txExcl`'s writer branch carries the closed flag's half,
`ws = wLive X.v w.C`, `wdbOK w`, the mapping at the view's base and the view `w.C`'s). -/
theorem txExclWGap_holds : TxExclWGap (GF := GF) := by
  intro _ _ _ K tx r X c hdb
  iintro ⟨Hx, Hv⟩
  iunfold txExcl at Hx
  icases Hx with ⟨%c', %x, Hv', Hd, Hx⟩
  icombine Hv' Hv gives % ⟨_, hx⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  icases Hx with ⟨Hrwl, Hcls, %w, %extra, Hlive, Hshape, %Hok⟩
  ihave Hv := (ghostVar_split_half r.n.v 1 _).2 $$ [Hv' Hv]
  · iframe
  rw [← hdb]
  iframe Hv Hd Hrwl Hcls
  iexists w, extra
  iframe Hshape
  isplitl [Hlive]
  · unfold wdbW
    rw [hdb]
    rw [hdb] at *
    iframe
    ipureintro; exact ⟨Hok.1, Hok.2.1, Hok.2.2.1⟩
  ipureintro; exact Hok.2.2.2

end proof

end bbolt
end EtcdGrove
end Perennial
