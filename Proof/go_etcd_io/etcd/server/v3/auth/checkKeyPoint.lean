/-
`checkKeyPoint`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.checkKeyPoint.wp_proof
    (h_NewBytesAffinePoint : adt.NewBytesAffinePoint.spec (GF := GF) (hG := hG)) :
    auth.checkKeyPoint.spec (GF := GF) (hG := hG) := by
  intro lg p Lr Lw key k dk pt
  wp_start as ⟨#Hp, Hk, %Hpt, %Hlen⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  iunfold permsAt at Hp
  icases Hp with ⟨%Hpnn, %tr, %tw, #Hr, #Hw, #Htr, #Htw⟩
  wp_auto
  wp_apply (h_NewBytesAffinePoint key k dk) $$ [$Hk] as %e ⟨Hk, He⟩
  · ipureintro; exact Hlen
  rcases Hpt with rfl | rfl
  · wp_if_destruct
    · (try wp_auto)
      wp_apply (adt.intervalTree.wp_Intersects_bytes tr Lr key e k (k ++ [W8 0]) dk (DFrac.own 1)
        .discard) $$ [$Htr $Hk $He] as ⟨-, Hk, -⟩
      first | (iapply HΦ; iframe Hk) | iframe Hk
      ipureintro
      (try simp only [↓reduceIte])
      have hb : ((!decide (adt.stab (k, k ++ [W8 0]) Lr = [])) = true) ↔
          adt.stab (k, k ++ [W8 0]) Lr ≠ [] := by simp
      rw [hb]
      exact adt.stab_point_iff k Lr
    · exact absurd rfl Hif
  · wp_if_destruct
    · exfalso; revert Hif; word
    · (try wp_auto)
      wp_apply (adt.intervalTree.wp_Intersects_bytes tw Lw key e k (k ++ [W8 0]) dk (DFrac.own 1)
        .discard) $$ [$Htw $Hk $He] as ⟨-, Hk, -⟩
      first | (iapply HΦ; iframe Hk) | iframe Hk
      ipureintro
      (try rw [if_neg (by word)])
      have hb : ((!decide (adt.stab (k, k ++ [W8 0]) Lw = [])) = true) ↔
          adt.stab (k, k ++ [W8 0]) Lw ≠ [] := by simp
      rw [hb]
      exact adt.stab_point_iff k Lw

end proof

end EtcdGrove
end Perennial
