/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Rollback_r.lean` (U5, `notes/bbolt-proof-plan.md`): the
`managed` assertion and the `db` check on the reader's fields (`rdTxK_flags_acc`), then
`nonPhysicalRollback`, whose reader branch is `close`.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Rollback_r
public import Spec.go_etcd_io.bbolt.Tx__close_r
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Txn.RdInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.nonPhysicalRollback()` of a whole reader: `close`. -/
private theorem Tx.nonPhysicalRollback_r (wp_close : Tx.close_r.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (src : PairSrc) (T : TxView) (v : View) :
    {{ rdTxK (GF := GF) K tx src 1 T v }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"nonPhysicalRollback")) (Val #()))
    {{ RET #(); txDoneDef tx ∗ pairBack K src }} := by
  wp_start as Hrd
  icases rdTxK_flags_acc K tx src 1 T v $$ Hrd with ⟨Hmg, Hdb, Hw, #Hpkg, %Hdbn, Hcl⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  wp_auto
  ihave Hrd := Hcl $$ Hmg Hdb Hw
  wp_apply wp_close K tx src T v $$ [Hrd] as ⟨Hd, Hb⟩
  · iexact Hrd
  iapply HΦ
  iframe

theorem Tx.Rollback_r.wp_proof (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (wp_close : Tx.close_r.spec (GF := GF) (hG := hG)) :
    Tx.Rollback_r.spec (GF := GF) (hG := hG) := by
  intro K tx src T v
  wp_start as Hrd
  icases rdTxK_flags_acc K tx src 1 T v $$ Hrd with ⟨Hmg, Hdb, Hw, #Hpkg, %Hdbn, Hcl⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Assert
  rw [decide_eq_false Hdbn]
  wp_auto
  ihave Hrd := Hcl $$ Hmg Hdb Hw
  wp_apply Tx.nonPhysicalRollback_r wp_close K tx src T v $$ [Hrd] as ⟨Hd, Hb⟩
  · iexact Hrd
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
