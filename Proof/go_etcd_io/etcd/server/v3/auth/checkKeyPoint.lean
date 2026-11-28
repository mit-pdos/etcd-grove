/-
`checkKeyPoint`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.checkKeyPoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffinePoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects_bytes
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
    (h_NewBytesAffinePoint : adt.NewBytesAffinePoint.spec (GF := GF) (hG := hG))
    (h_Intersects_bytes : adt.intervalTree.Intersects_bytes.spec (GF := GF) (hG := hG)) :
    auth.checkKeyPoint.spec (GF := GF) (hG := hG) := by
  intro lg p Tr Tw key k dk pt
  wp_start as ⟨#Hp, Hk, %Hpt, %Hlen⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  iunfold permsAt at Hp
  icases Hp with ⟨%Hpnn, %tr, %tw, #Hr, #Hw, #HtrT, #HtwT⟩
  -- the point query reads the trees' entries
  ihave #Htr := adt.ownIvtTB_B _ _ _ $$ HtrT
  ihave #Htw := adt.ownIvtTB_B _ _ _ $$ HtwT
  wp_auto
  wp_apply (h_NewBytesAffinePoint key k dk) $$ [$Hk] as %e ⟨Hk, He⟩
  · ipureintro; exact Hlen
  rcases Hpt with rfl | rfl
  · wp_if_destruct
    · (try wp_auto)
      wp_apply (h_Intersects_bytes tr Tr.inorder key e k (k ++ [W8 0]) dk (DFrac.own 1)
        .discard) $$ [$Htr $Hk $He] as ⟨-, Hk, -⟩
      first | (iapply HΦ; iframe Hk) | iframe Hk
      ipureintro
      (try simp only [↓reduceIte])
      have hb : ((!decide (adt.stab (k, k ++ [W8 0]) Tr.inorder = [])) = true) ↔
          adt.stab (k, k ++ [W8 0]) Tr.inorder ≠ [] := by simp
      rw [hb]
      exact adt.stab_point_iff k Tr.inorder
    · exact absurd rfl Hif
  · wp_if_destruct
    · exfalso; revert Hif; word
    · (try wp_auto)
      wp_apply (h_Intersects_bytes tw Tw.inorder key e k (k ++ [W8 0]) dk (DFrac.own 1)
        .discard) $$ [$Htw $Hk $He] as ⟨-, Hk, -⟩
      first | (iapply HΦ; iframe Hk) | iframe Hk
      ipureintro
      (try rw [if_neg (by word)])
      have hb : ((!decide (adt.stab (k, k ++ [W8 0]) Tw.inorder = [])) = true) ↔
          adt.stab (k, k ++ [W8 0]) Tw.inorder ≠ [] := by simp
      rw [hb]
      exact adt.stab_point_iff k Tw.inorder

end proof

end EtcdGrove
end Perennial
