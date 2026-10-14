/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/checkKeyPoint.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyPoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffinePoint

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

theorem auth.checkKeyPoint.wp_proof
    (h_NewBytesAffinePoint : adt.NewBytesAffinePoint.spec (GF := GF) (hG := hG)) :
    auth.checkKeyPoint.spec (GF := GF) (hG := hG) := by
  intro lg p key k dk pt
  wp_start as ⟨#Hp, Hk, %Hpt, %Hlen⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  iunfold permsOk at Hp
  icases Hp with ⟨%Hpnn, %r, %w, #Hr, #Hw, #Hqr, #Hqw⟩
  wp_auto
  wp_apply (h_NewBytesAffinePoint key k dk) $$ [$Hk] as %e ⟨Hk, He⟩
  · ipureintro; exact Hlen
  rcases Hpt with rfl | rfl
  · wp_if_destruct
    · iunfold ivtQuery at Hqr
      icases Hqr with ⟨%ti, %Hti, #Hint, -⟩
      subst Hti
      wp_auto
      wp_apply Hint $$ [$Hk $He] as %b ⟨Hk, -⟩
      wp_end
    · exact absurd rfl Hif
  · wp_if_destruct
    · exfalso; revert Hif; word
    · iunfold ivtQuery at Hqw
      icases Hqw with ⟨%ti, %Hti, #Hint, -⟩
      subst Hti
      wp_auto
      wp_apply Hint $$ [$Hk $He] as %b ⟨Hk, -⟩
      wp_end

end proof

end EtcdGrove
end Perennial
