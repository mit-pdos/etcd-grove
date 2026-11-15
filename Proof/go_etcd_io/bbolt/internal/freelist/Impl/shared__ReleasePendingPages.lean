/-
`shared.ReleasePendingPages()` (U2 internal), over the code's model `FLPg.releasePendingGo`
(`Lemmas/ReleaseGo.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__release
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__releaseRange
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__readonly
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Sorters

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem releasePendingGo_eq (fl : FLPg) (ro : List w64) : fl.releasePendingGo ro =
    (let m0 : w64 := ((sortPgids ro).head?).getD (W64 (-1))
     let fl1 := if 0 < m0.toNat then fl.release (m0 - 1) else fl
     let acc := (sortPgids ro).foldl (fun (acc : FLPg × w64) t =>
       (acc.1.releaseRangeGo acc.2 (t - 1), t + 1)) (fl1, m0)
     acc.1.releaseRangeGo acc.2 (W64 (-1))) := rfl

abbrev shared.ReleasePendingPages.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (ro : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s I.iface fl ∗ I.own fl.free ∗ roOwn s ro }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"ReleasePendingPages" #s)) (Val #()))
  {{ RET #(); ownSh s I.iface (fl.releasePendingGo ro) ∗ I.own (fl.releasePendingGo ro).free ∗
      roOwn s (sortPgids ro) }}

theorem shared.ReleasePendingPages.wp_proof (I : FLImpl (GF := GF)) (hMS : I.MergeSpansSpec) :
    shared.ReleasePendingPages.spec I := by
  intro s fl ro
  wp_start as ⟨Hsh, Hown, Hro0⟩
  iunfold roOwn at Hro0
  icases Hro0 with ⟨%sl, Hrof, Hro, Hro_cap⟩
  ihave #Hsrt := txIDx_isSorter (GF := GF) sl
  ihave ⟨Hro, %Hrolen⟩ := ownSlice_w64_len _ _ _ $$ Hro
  wp_auto
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  wp_apply (sort.wp_Sort (interface.mk txIDx.ty #sl) (fun l => sl ↦* l) pgLt
      slices.StrictWeakOrder_unsigned_lt ro) $$ [Hro] as %ys ⟨Hro, %Hperm, %Hsorted⟩
  · iframe
    isplitl []
    · iexact Hsrt
    ipureintro; omega
  have Hyseq : ys = sortPgids ro := sort_post_eq Hperm Hsorted
  subst Hyseq
  ihave %Hyl := ownSlice_len _ _ _ $$ Hro
  generalize hys : sortPgids ro = ys at *
  wp_join iprop(minid_ptr ↦ (ys.head?).getD (W64 (-1)) ∗ sl ↦* ys ∗ t_ptr ↦ s ∗
      structFieldRef shared go!"readonlyTXIDs" s ↦ sl)
    with [minid Hro t Hrof] as ⟨minid, Hro, t, Hrof⟩
  · rcases ys with _ | ⟨y0, ys'⟩
    · exfalso; simp only [List.length_nil] at Hyl; word
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by simp only [List.length_cons] at Hyl; word⟩)]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) (y0 :: ys') _ y0 (by decide) $$ [Hro] with Hro
      · iframe; ipureintro; rfl
      try wp_auto
      wp_join_done
  · rcases ys with _ | ⟨y0, ys'⟩
    · iframe
    · exfalso; apply Hif; simp only [List.length_cons] at Hyl; word
  generalize hm0 : (ys.head?).getD (W64 (-1)) = m0
  try wp_auto
  wp_join iprop(ownSh s I.iface (if 0 < m0.toNat then fl.release (m0 - 1) else fl) ∗
      I.own (if 0 < m0.toNat then fl.release (m0 - 1) else fl).free ∗
      minid_ptr ↦ m0 ∗ t_ptr ↦ s)
    with [Hsh Hown minid t] as ⟨Hsh, Hown, minid, t⟩
  · try wp_auto
    wp_apply (shared.release.wp_proof I hMS s fl (m0 - W64 1)) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
    · iframe
    wp_join_done
    rw [if_pos (show 0 < m0.toNat by word)]
    iframe
  · rw [if_neg (show ¬ 0 < m0.toNat by word)]
    iframe
  generalize hμ1 : (if 0 < m0.toNat then fl.release (m0 - 1) else fl) = μ1 at *
  let step : FLPg × w64 → w64 → FLPg × w64 :=
    fun acc t => (acc.1.releaseRangeGo acc.2 (t - 1), t + 1)
  try wp_auto
  ihave IH : iprop(∃ (k tv : w64),
      "i" ∷ i_ptr ↦ k ∗ "tid" ∷ tid_ptr ↦ tv ∗
      "minid" ∷ minid_ptr ↦ ((ys.take (sint.nat k)).foldl step (μ1, m0)).2 ∗
      "Hsh" ∷ ownSh s I.iface ((ys.take (sint.nat k)).foldl step (μ1, m0)).1 ∗
      "Hown" ∷ I.own ((ys.take (sint.nat k)).foldl step (μ1, m0)).1.free ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ys.length : Int)⌝) $$ [i tid minid Hsh Hown]
  · iexists W64 0, _
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.foldl_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < ys.length := by word
    list_elem ys (sint.nat k) as y
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index _ (sint.Z k) ys _ y Hk.1 $$ [Hro] with Hro
    · iframe; ipureintro; exact Hy_lookup
    try wp_auto
    wp_apply (shared.releaseRange.wp_proof I hMS s _ _ (y - W64 1)) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, y
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have hstep : (ys.take (sint.nat (k + W64 1))).foldl step (μ1, m0) =
        step ((ys.take (sint.nat k)).foldl step (μ1, m0)) y := by
      rw [hk1, List.take_add_one, Hy_lookup, Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    rw [hstep]
    iframe
    ipureintro; constructor <;> word
  · have Hall : sint.nat k = ys.length := by word
    rw [Hall, List.take_length] at *
    try wp_auto
    wp_apply (shared.releaseRange.wp_proof I hMS s _ _ (W64 18446744073709551615)) $$ [Hsh Hown]
      as ⟨Hsh, Hown⟩
    · iframe
    try wp_auto
    have hfin : (ys.foldl step (μ1, m0)).1.releaseRangeGo (ys.foldl step (μ1, m0)).2
        (W64 18446744073709551615) = fl.releasePendingGo ro := by
      rw [releasePendingGo_eq]
      simp only []
      rw [hys, hm0, hμ1]
      rfl
    rw [hfin]
    iapply HΦ
    iframe
    iunfold roOwn
    iexists sl
    iframe

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
