module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__ReleasePendingPages
public import Proof.go_etcd_io.bbolt.internal.freelist.ReleaseLemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__release
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__releaseRange
public import Spec.sort.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.ReleasePendingPages.wp_proof (hRel : shared.release.spec (GF := GF) (hG := hG))
    (hRR : shared.releaseRange.spec (GF := GF) (hG := hG))
    (hSort : sort.Sort.spec (GF := GF) (hG := hG)) :
    shared.ReleasePendingPages.spec (GF := GF) (hG := hG) := by
  intro I s σ hMS
  wp_start as ⟨#Hhdl, Hsh, Hown⟩
  unfold ownShared ownSharedC
  icases Hsh with ⟨%sv, %c, Hsh, %Hok⟩
  iNamed Hsh
  wp_auto
  wp_apply (hSort _ _ σ.readonly (Or.inr rfl)) $$ [Hro] as %ys ⟨%Hys, Hro⟩
  · iexact Hro
  have Hyseq : ys = sortedTxids σ.readonly := sortedTxids_eq Hys.1 Hys.2
  ihave %Hyl := ownSlice_len _ _ _ $$ Hro
  try wp_auto
  wp_join iprop(minid_ptr ↦ ys.headD (W64 (2 ^ 64 - 1)) ∗ sv.readonlyTXIDs' ↦* ys ∗ s ↦ sv ∗
      t_ptr ↦ s) with [minid Hro Hs t] as ⟨minid, Hro, Hs, t⟩
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
  generalize hm0 : ys.headD (W64 (2 ^ 64 - 1)) = m0
  ihave HshC : ownSharedC s sv I.iface { σ with readonly := ys } c $$
      [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · unfold ownSharedC; iexists pp; simp only [named]; iframe; ipureintro; exact Hiface
  have Hσ0 : ({ σ with readonly := ys } : FLState).equiv σ :=
    ⟨List.Perm.refl _, Hys.2, rfl, fun _ => Iff.rfl, fun t p q hp hq => by
      simp only at hp; rw [hp] at hq; cases hq; exact Pending.equiv_refl p⟩
  have HPL : PendLen σ := Hok.2.2.2.2.2
  have HPL0 : PendLen ({ σ with readonly := ys } : FLState) := Hok.2.2.2.2.2
  try wp_auto
  wp_join iprop(∃ (τ : FLState), ownSharedC s sv I.iface τ c ∗ I.own s τ.free ∗
      minid_ptr ↦ m0 ∗ t_ptr ↦ s ∗
      ⌜cacheOK c τ ∧ τ.WF ∧ τ.readonly = ys ∧
        τ.equiv (if 0 < uint.Z m0 then σ.release (m0 - W64 1) else σ)⌝)
    with [HshC Hown minid t] as ⟨%τ, HshC, Hown, minid, t, %Hτ⟩
  · try wp_auto
    wp_apply (hRel I s sv c { σ with readonly := ys } (m0 - W64 1) hMS) $$ [HshC Hown]
      as %σ1 ⟨%H1, HshC, %Hok1, Hown⟩
    · iframe
      isplitl []
      · iexact Hhdl
      ipureintro; exact Hok
    wp_join_done
    iexists σ1
    iframe
    ipureintro
    refine ⟨Hok1.1, Hok1.2, H1.2, ?_⟩
    rw [if_pos (show 0 < uint.Z m0 by have := Hif; word)]
    exact FLState.equiv_trans H1.1 (release_congr Hσ0 HPL0 HPL _)
  · iexists { σ with readonly := ys }
    iframe
    ipureintro
    refine ⟨Hok.1, Hok.2, rfl, ?_⟩
    rw [if_neg (show ¬ 0 < uint.Z m0 by have := Hif; word)]; exact Hσ0
  generalize hμ1 : (if 0 < uint.Z m0 then σ.release (m0 - W64 1) else σ) = μ1 at Hτ
  have HPL1 : PendLen μ1 := by
    rw [← hμ1]; split
    · exact release_pendLen HPL _
    · exact HPL
  let step : FLState × w64 → w64 → FLState × w64 :=
    fun acc tid => (acc.1.releaseRange acc.2 (tid - W64 1), tid + W64 1)
  have HPLacc : ∀ (l : List w64) (a : FLState × w64), PendLen a.1 → PendLen (l.foldl step a).1 := by
    intro l
    induction l with
    | nil => intro a h; exact h
    | cons y l ih => intro a h; exact ih _ (releaseRange_pendLen h _ _)
  iunfold ownSharedC at HshC
  iNamed HshC
  try wp_auto
  ihave %Hyl2 := ownSlice_len _ _ _ $$ Hro
  ihave HshC : ownSharedC s sv I.iface τ c $$ [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · unfold ownSharedC; iexists _; simp only [named]; iframe; ipureintro; assumption
  rw [Hτ.2.2.1] at Hyl2
  ihave IH : iprop(∃ (k tv0 mv : w64) (τ' : FLState),
      "i" ∷ i_ptr ↦ k ∗ "tid" ∷ tid_ptr ↦ tv0 ∗ "minid" ∷ minid_ptr ↦ mv ∗
      "HshC" ∷ ownSharedC s sv I.iface τ' c ∗ "Hown" ∷ I.own s τ'.free ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ys.length : Int) ∧ cacheOK c τ' ∧ τ'.WF ∧
        τ'.readonly = ys ∧ τ'.equiv ((ys.take (sint.nat k)).foldl step (μ1, m0)).1 ∧
        mv = ((ys.take (sint.nat k)).foldl step (μ1, m0)).2⌝) $$ [i tid minid HshC Hown]
  · iexists W64 0, _, m0, τ
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl]
    exact ⟨by word, by word, Hτ.1, Hτ.2.1, Hτ.2.2.1, Hτ.2.2.2, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hb : sint.nat k < ys.length := by word
    list_elem ys (sint.nat k) as y
    have Hyr : τ'.readonly[sint.nat k]? = some y := by rw [Hk.2.2.2.2.1]; exact Hy_lookup
    iunfold ownSharedC at HshC
    iNamed HshC
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [Hk.2.2.2.2.1] at *; word))]
    wp_apply wp_load_slice_index _ (sint.Z k) τ'.readonly _ y Hk.1 $$ [Hro] with Hro
    · iframe; ipureintro; exact Hyr
    ihave HshC : ownSharedC s sv I.iface τ' c $$ [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
    · unfold ownSharedC; iexists _; simp only [named]; iframe; ipureintro; assumption
    try wp_auto
    wp_apply (hRR I s sv c τ' mv (y - W64 1) hMS) $$ [HshC Hown] as %τ2 ⟨%H2, HshC, %Hok2, Hown⟩
    · iframe
      isplitl []
      · iexact Hhdl
      ipureintro; exact ⟨Hk.2.2.1, Hk.2.2.2.1⟩
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, y, y + W64 1, τ2
    iframe
    ipureintro
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hk1, List.take_add_one, Hy_lookup, Option.toList_some, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    refine ⟨by word, by word, Hok2.1, Hok2.2, H2.2.trans Hk.2.2.2.2.1, ?_, rfl⟩
    refine FLState.equiv_trans H2.1 ?_
    rw [Hk.2.2.2.2.2.2]
    exact releaseRange_congr Hk.2.2.2.2.2.1 Hk.2.2.2.1.2.2.2.2 (HPLacc _ _ HPL1) _ _
  · have Hall : sint.nat k = ys.length := by word
    rw [Hall, List.take_length] at Hk
    try wp_auto
    wp_apply (hRR I s sv c τ' mv (W64 18446744073709551615) hMS) $$ [HshC Hown]
      as %τf ⟨%Hf, HshC, %Hokf, Hown⟩
    · iframe
      isplitl []
      · iexact Hhdl
      ipureintro; exact ⟨Hk.2.2.1, Hk.2.2.2.1⟩
    try wp_auto
    have Hfin : τf.equiv σ.releasePending := by
      have h1 : τf.equiv ((ys.foldl step (μ1, m0)).1.releaseRange (ys.foldl step (μ1, m0)).2
          (W64 18446744073709551615)) := by
        refine FLState.equiv_trans Hf.1 ?_
        rw [Hk.2.2.2.2.2.2]
        exact releaseRange_congr Hk.2.2.2.2.2.1 Hk.2.2.2.1.2.2.2.2 (HPLacc _ _ HPL1) _ _
      have hro : τf.readonly = ys := Hf.2.trans Hk.2.2.2.2.1
      unfold FLState.releasePending
      dsimp only
      have e : (W64 (2 ^ 64 - 1) : w64) = W64 18446744073709551615 := rfl
      rw [← Hyseq, hm0, hμ1, e]
      exact ⟨h1.1, by rw [hro], h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩
    ispecialize HΦ $$ %τf
    iapply HΦ
    isplitr
    · ipureintro; exact Hfin
    iunfold ownSharedC at HshC
    iNamed HshC
    iframe
    isplitr
    · ipureintro; assumption
    ipureintro; exact Hokf

end proof

end bbolt
end EtcdGrove
end Perennial
