/-
`checkKeyInterval`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `Contains` over the open-ended query `[k, "")`, `k` not empty: the coverage of the queried
interval. -/
theorem auth.checkKeyInterval.open_case (L : List adt.Entry) (k e : GoString) (r : Bool)
    (hs : adt.IvSorted L) (ho : auth.isOpenEnded e)
    (Hr : (k = go!"" ∨ adt.affLt k []) → r = adt.containsRes (k, []) L) (hk : k ≠ []) :
    r = true ↔ ∀ x, adt.inIvl (queryIvl k e) x → ∃ z ∈ L, adt.inIvl z.1 x := by
  have hq : queryIvl k e = (k, []) := by unfold queryIvl; simp [ho]
  rw [hq, Hr (Or.inr ⟨hk, Or.inl rfl⟩)]
  exact adt.containsRes_iff (k, []) L hs ⟨hk, Or.inl rfl⟩

/-- `Contains` over the query `[k, e)`, `k` not empty and below `e`: the coverage of the queried
interval. -/
theorem auth.checkKeyInterval.range_case (L : List adt.Entry) (k e : GoString) (r : Bool)
    (hs : adt.IvSorted L) (ho : ¬ auth.isOpenEnded e)
    (Hr : (k = go!"" ∨ adt.affLt k e) → r = adt.containsRes (k, e) L) (hk : k ≠ [])
    (hlt : go.GoStringLt k e) :
    r = true ↔ ∀ x, adt.inIvl (queryIvl k e) x → ∃ z ∈ L, adt.inIvl z.1 x := by
  have hq : queryIvl k e = (k, e) := by unfold queryIvl; simp [ho]
  rw [hq, Hr (Or.inr ⟨hk, Or.inr hlt⟩)]
  exact adt.containsRes_iff (k, e) L hs ⟨hk, Or.inr hlt⟩

theorem auth.checkKeyInterval.wp_proof
    (h_isOpenEnded : auth.isOpenEnded.spec (GF := GF) (hG := hG))
    (h_NewBytesAffineInterval : adt.NewBytesAffineInterval.spec (GF := GF) (hG := hG)) :
    auth.checkKeyInterval.spec (GF := GF) (hG := hG) := by
  intro lg p Lr Lw key re k e dk de pt
  wp_start as ⟨#Hp, Hk, He, %Hpt⟩
  ihave #Hadt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  iunfold permsAt at Hp
  icases Hp with ⟨%Hpnn, %tr, %tw, #Hr, #Hw, #Htr, #Htw⟩
  ihave %Hsr := adt.ownIvtB_sorted _ _ _ $$ Htr
  ihave %Hsw := adt.ownIvtB_sorted _ _ _ $$ Htw
  wp_auto
  wp_apply (h_isOpenEnded re e de) $$ [$He] as He
  wp_if_destruct
  · -- open-ended: the query `[key, nil)`
    have ho : auth.isOpenEnded e := by simpa using Hif
    (try wp_auto)
    wp_apply h_NewBytesAffineInterval
    rcases Hpt with rfl | rfl
    · wp_if_destruct
      · (try wp_auto)
        wp_apply (adt.intervalTree.wp_Contains_bytes tr Lr key slice.nil k [] dk (DFrac.own 1)
          .discard) $$ [$Htr $Hk] as %r ⟨-, Hk, -, %Hres⟩
        · iapply ownSlice_nil (V := w8) (DFrac.own 1)
        first | (iapply HΦ; iframe Hk He) | iframe Hk He
        ipureintro
        intro hk _
        (try simp only [↓reduceIte])
        exact auth.checkKeyInterval.open_case Lr k e r Hsr ho Hres hk
      · exact absurd rfl Hif
    · wp_if_destruct
      · exfalso; revert Hif; word
      · (try wp_auto)
        wp_apply (adt.intervalTree.wp_Contains_bytes tw Lw key slice.nil k [] dk (DFrac.own 1)
          .discard) $$ [$Htw $Hk] as %r ⟨-, Hk, -, %Hres⟩
        · iapply ownSlice_nil (V := w8) (DFrac.own 1)
        first | (iapply HΦ; iframe Hk He) | iframe Hk He
        ipureintro
        intro hk _
        rw [if_neg (by word)]
        exact auth.checkKeyInterval.open_case Lw k e r Hsw ho Hres hk
  · -- the query `[key, rangeEnd)`
    have ho : ¬ auth.isOpenEnded e := by simpa using Hif
    (try wp_auto)
    wp_apply h_NewBytesAffineInterval
    rcases Hpt with rfl | rfl
    · wp_if_destruct
      · (try wp_auto)
        wp_apply (adt.intervalTree.wp_Contains_bytes tr Lr key re k e dk de .discard)
          $$ [$Htr $Hk $He] as %r ⟨-, Hk, He, %Hres⟩
        first | (iapply HΦ; iframe Hk He) | iframe Hk He
        ipureintro
        intro hk hoe
        rcases hoe with h | hlt
        · exact absurd h ho
        (try simp only [↓reduceIte])
        exact auth.checkKeyInterval.range_case Lr k e r Hsr ho Hres hk hlt
      · exact absurd rfl Hif
    · wp_if_destruct
      · exfalso; revert Hif; word
      · (try wp_auto)
        wp_apply (adt.intervalTree.wp_Contains_bytes tw Lw key re k e dk de .discard)
          $$ [$Htw $Hk $He] as %r ⟨-, Hk, He, %Hres⟩
        first | (iapply HΦ; iframe Hk He) | iframe Hk He
        ipureintro
        intro hk hoe
        rcases hoe with h | hlt
        · exact absurd h ho
        rw [if_neg (by word)]
        exact auth.checkKeyInterval.range_case Lw k e r Hsw ho Hres hk hlt

end proof

end EtcdGrove
end Perennial
