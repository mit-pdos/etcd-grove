/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/checkKeyInterval.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyInterval
public import Spec.go_etcd_io.etcd.server.v3.auth.isOpenEnded
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffineInterval

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.checkKeyInterval.wp_proof
    (h_isOpenEnded : auth.isOpenEnded.spec (GF := GF) (hG := hG))
    (h_NewBytesAffineInterval : adt.NewBytesAffineInterval.spec (GF := GF) (hG := hG)) :
    auth.checkKeyInterval.spec (GF := GF) (hG := hG) := by
  intro lg p key re k e dk de pt
  wp_start as ⟨#Hp, Hk, He, %Hpt⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  iunfold permsOk at Hp
  icases Hp with ⟨%Hpnn, %r, %w, #Hr, #Hw, #Hqr, #Hqw⟩
  wp_auto
  wp_apply (h_isOpenEnded re e de) $$ [$He] as %oe He
  wp_if_destruct
  · (try wp_auto)
    wp_apply h_NewBytesAffineInterval
    rcases Hpt with rfl | rfl
    · wp_if_destruct
      · iunfold ivtQuery at Hqr
        icases Hqr with ⟨%ti, %Hti, -, #Hcon⟩
        subst Hti
        wp_auto
        wp_apply Hcon $$ [$Hk $He] as %b ⟨Hk, He⟩
        wp_end
      · exact absurd rfl Hif
    · wp_if_destruct
      · exfalso; revert Hif; word
      · iunfold ivtQuery at Hqw
        icases Hqw with ⟨%ti, %Hti, -, #Hcon⟩
        subst Hti
        wp_auto
        wp_apply Hcon $$ [$Hk $He] as %b ⟨Hk, He⟩
        wp_end
  · (try wp_auto)
    wp_apply h_NewBytesAffineInterval
    rcases Hpt with rfl | rfl
    · wp_if_destruct
      · iunfold ivtQuery at Hqr
        icases Hqr with ⟨%ti, %Hti, -, #Hcon⟩
        subst Hti
        wp_auto
        wp_apply Hcon $$ [$Hk] as %b ⟨Hk, -⟩
        · iapply ownSlice_nil (V := w8) (DFrac.own 1)
        wp_end
      · exact absurd rfl Hif
    · wp_if_destruct
      · exfalso; revert Hif; word
      · iunfold ivtQuery at Hqw
        icases Hqw with ⟨%ti, %Hti, -, #Hcon⟩
        subst Hti
        wp_auto
        wp_apply Hcon $$ [$Hk] as %b ⟨Hk, -⟩
        · iapply ownSlice_nil (V := w8) (DFrac.own 1)
        wp_end

end proof

end EtcdGrove
end Perennial
