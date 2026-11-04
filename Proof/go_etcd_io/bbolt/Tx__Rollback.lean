/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Rollback.lean` (U5, `notes/bbolt-proof-plan.md`): a reader
is `Tx.Rollback_r` on its `rdTxK` (a pool loan: its `threadTok` back); a writer takes its
exclusive part out, rolls the freelist back (`Interface.Rollback`, `store_rollback`) and closes
(`Tx.close_w.spec'`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Rollback
public import Spec.go_etcd_io.bbolt.Tx__Rollback_r
public import Proof.go_etcd_io.bbolt.Inv.Ctx
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A reader's `Rollback`** (the public triple's read case): its `rdTxK` with a pool loan. -/
theorem Tx.Rollback.wp_reader [HasExt osFsExt]
    (wp_Rollback_r : Tx.Rollback_r.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (T : TxView) (hro : T.rw = false) :
    {{ boltTx (GF := GF) tx γ 1 T }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Rollback")) (Val #()))
    {{ RET #GoInterface.nil; txDone tx ∗ (if T.rw then emp else threadTok) }} := by
  iintro %Φ Ht HΦ
  unfold boltTx
  ihave Ht := (boltTx_rdTx _ _ tx 1 T hro).1 $$ Ht
  icases Ht with ⟨%db, Hr, -⟩
  ihave Hr := (rdTx_rdTxK _ _ tx .loan 1 T).1 $$ Hr
  icases Hr with ⟨%K, %v, -, Hr⟩
  iapply wp_Rollback_r K tx .loan T v $$ [Hr]
  · iexact Hr
  inext
  iintro %err ⟨%Herr, Hd, Hb⟩
  subst Herr
  iapply HΦ
  simp only [hro, Bool.false_eq_true, ↓reduceIte]
  unfold txDone pairBack
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
