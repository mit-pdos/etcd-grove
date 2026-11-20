/- Lean-first (no Rocq counterpart).

`realEvents.wp_proof` (k8s 7g step 5): the first loop looks for an Error event (a prefix of the read-only
slice, `evsRO_split`); the second, for a watch-list, for a bookmark among the events kept.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realEvents
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section pure
variable [GooseExts]

/-- `realEvents`' first cut: up to the first Error event, included. -/
def cutRs (rs : List REv) : List REv :=
  match rs.findIdx? (fun e => decide (e.ty = evError)) with
  | some i => rs.take (i + 1)
  | none => rs

theorem realEventsL_cut (x : Input) (rs : List REv) :
    realEventsL x rs = if x.SendInit' = W64 2 then
      (if (cutRs rs).any (fun e => decide (e.ty = evBookmark)) then cutRs rs else []) else cutRs rs := rfl

theorem cutRs_none (rs : List REv) (h : ∀ r ∈ rs, r.ty ≠ evError) : cutRs rs = rs := by
  unfold cutRs
  rw [List.findIdx?_eq_none_iff.2 (fun r hr => by simpa using h r hr)]

theorem cutRs_some (rs : List REv) (j : Nat) (r : REv) (h : ∀ r ∈ rs.take j, r.ty ≠ evError)
    (hr : rs[j]? = some r) (he : r.ty = evError) : cutRs rs = rs.take (j + 1) := by
  unfold cutRs
  have hj : j < rs.length := by
    rcases Nat.lt_or_ge j rs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hr; cases hr
  rw [List.findIdx?_eq_some_iff_getElem.2 ⟨hj, ?_, ?_⟩]
  · rw [List.getElem?_eq_getElem hj] at hr; cases hr; simpa using he
  · intro k hk
    have := h rs[k] (List.mem_take_iff_getElem.2 ⟨k, by omega, rfl⟩)
    simpa using this

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option hygiene false in
/-- After the first loop (`cut ↦ c`, `Hc : evsRO c (cutRs rs)`): the watch-list's bookmark test. -/
local macro "re_tail" : tactic => `(tactic| (
  ihave #Hc0 := Hc
  iunfold evsRO at Hc0
  icases Hc0 with ⟨%cvs, #Hcsl, #Hcvs⟩
  ihave %Hclen := ownSlice_len $$ Hcsl
  ihave %Hcl2 := BigSepL2.bigSepL2_length $$ Hcvs
  wp_if_destruct
  · have hS : x.SendInit' = W64 2 := Hif
    (try wp_auto)
    ihave HL2 : (∃ (j2 : w64) (ev2 : k8s_io.apimachinery.pkg.watch.Event),
        "i" ∷ i_ptr ↦ j2 ∗ "ev" ∷ ev_ptr ↦ ev2 ∗
        "%Hj2" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.Z j2 ≤ sint.Z c.len ∧
          ∀ r ∈ (cutRs rs).take (sint.nat j2), r.ty ≠ evBookmark⌝ : IProp GF) $$ [i ev]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]; simp
    wp_for HL2
    wp_if_destruct
    · have Hb2 : 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z c.len := ⟨Hj2.1, by simpa using Hif⟩
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      list_elem cvs (sint.nat j2) as v2
      wp_apply (wp_load_slice_index c (sint.Z j2) cvs DFrac.discard v2 Hj2.1) $$ [Hcsl] as -
      · isplit
        · iexact Hcsl
        · ipureintro; exact Hv2_lookup
      obtain ⟨r2, hr2⟩ : ∃ r, (cutRs rs)[sint.nat j2]? = some r := by
        have : sint.nat j2 < (cutRs rs).length := by rw [← Hcl2]; word
        exact ⟨_, List.getElem?_eq_getElem this⟩
      ihave #Hv2 := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
        Hv2_lookup hr2 $$ Hcvs
      iunfold evRep at Hv2
      icases Hv2 with ⟨%hty2, -⟩
      (try wp_auto)
      have hj21 : sint.nat (j2 + W64 1) = sint.nat j2 + 1 := by word
      by_cases hb2 : r2.ty = evBookmark
      · have hev2 : v2.Type' = go!"BOOKMARK" := by rw [hty2, hb2]; rfl
        simp only [hev2, _root_.decide_true]
        wp_auto
        wp_for_post
        iapply HΦ
        have hany : (cutRs rs).any (fun e => decide (e.ty = evBookmark)) = true :=
          List.any_eq_true.2 ⟨r2, List.mem_of_getElem? hr2, by simpa using hb2⟩
        rw [realEventsL_cut, if_pos hS, if_pos hany]
        iexact Hc
      · have hev2 : v2.Type' ≠ go!"BOOKMARK" := by rw [hty2]; exact hb2
        simp only [decide_eq_false hev2]
        wp_auto
        wp_for_post
        iframe
        iexists j2 + W64 1, v2
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hj21, List.take_add_one, hr2]
        intro r' hr'
        simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hr'
        rcases hr' with hr' | rfl
        · exact Hj2.2.2 r' hr'
        · exact hb2
    · have hjl2 : sint.nat j2 = (cutRs rs).length := by rw [← Hcl2]; word
      have hnone : (cutRs rs).any (fun e => decide (e.ty = evBookmark)) = false := by
        have := Hj2.2.2; rw [hjl2, List.take_length] at this
        exact List.any_eq_false.2 (fun r hr => by simpa using this r hr)
      (try wp_auto)
      iapply HΦ
      rw [realEventsL_cut, if_pos hS, hnone, if_neg Bool.false_ne_true]
      iapply evsRO_nil
  · (try wp_auto)
    iapply HΦ
    rw [realEventsL_cut, if_neg Hif]
    iexact Hc))

theorem realEvents.wp_proof :
    realEvents.spec (GF := GF) (hG := hG) := by
  intro x sl rs
  wp_start as #Hs
  ihave #Hs0 := Hs
  iunfold evsRO at Hs0
  icases Hs0 with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  ihave %Hwf := ownSlice_wf $$ Hsl
  wp_auto
  rename_i iv_ptr
  irename : (iv_ptr ↦ (zero_val w64) : IProp GF) => i0
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ ev ∗ "i0" ∷ iv_ptr ↦ iv ∗ "cut" ∷ cut_ptr ↦ sl ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        ∀ r ∈ rs.take (sint.nat j), r.ty ≠ evError⌝ : IProp GF) $$ [i ev i0 cut]
  · iexists W64 0, _, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  irename «in» => Hin
  wp_for HL
  wp_if_destruct
  · have Hif' : sint.Z j < sint.Z sl.len := by simpa using Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif'⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem vs (sint.nat j) as v
    wp_apply (wp_load_slice_index sl (sint.Z j) vs DFrac.discard v Hj.1) $$ [Hsl] as -
    · isplit
      · iexact Hsl
      · ipureintro; exact Hv_lookup
    obtain ⟨r, hr⟩ : ∃ r, rs[sint.nat j]? = some r := by
      have : sint.nat j < rs.length := by rw [← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave #Hv := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      Hv_lookup hr $$ Hvs
    iunfold evRep at Hv
    icases Hv with ⟨%hty, -⟩
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    by_cases hb : r.ty = evError
    · have hev : v.Type' = go!"ERROR" := by rw [hty, hb]; rfl
      simp only [hev, _root_.decide_true]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by word, by word⟩)]
      wp_auto
      wp_for_post
      icases evsRO_split sl rs (j + W64 1) ⟨by word, by word⟩ $$ Hs with ⟨#Hc, -⟩
      rw [hj1, ← cutRs_some rs _ r Hj.2.2 hr hb]
      generalize slice.slice sl k8s_io.apimachinery.pkg.watch.Event (W64 0) (j + W64 1) = c
      re_tail
    · have hev : v.Type' ≠ go!"ERROR" := by rw [hty]; exact hb
      simp only [decide_eq_false hev]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, v, j
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hj1, List.take_add_one, hr]
      intro r' hr'
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hr'
      rcases hr' with hr' | rfl
      · exact Hj.2.2 r' hr'
      · exact hb
  · have hjl : sint.nat j = rs.length := by rw [← Hl2]; word
    have hpre : ∀ r ∈ rs, r.ty ≠ evError := by
      have := Hj.2.2; rwa [hjl, List.take_length] at this
    ihave #Hc : evsRO sl (cutRs rs) $$ []
    · rw [cutRs_none rs hpre]; iexact Hs
    generalize sl = c
    re_tail

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
