/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `TermConfs.Get`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs__Get
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
/-- `TermFn.get` at the first point of term `t`. -/
theorem TermConfsGet_found {α : Type} (f : TermFn α) (k : Nat) (p0 : Int × α) (t : Int)
    (hk : f[k]? = some p0) (hpre : TermFn.has (f.take k) t = false) (hp : p0.1 = t) :
    f.get t = pure p0.2 := by
  have hl : k < f.length := (List.getElem?_eq_some_iff.1 hk).1
  have hf : f.find? (fun p => p.1 == t) = some p0 := by
    rw [← List.take_append_drop k f, List.find?_append]
    have h0 : (f.take k).find? (fun p => p.1 == t) = none := by
      rw [List.find?_eq_none]; intro x hx
      unfold TermFn.has at hpre; rw [List.any_eq_false] at hpre; exact hpre x hx
    rw [h0, Option.none_or, List.drop_eq_getElem_cons hl]
    rw [(List.getElem?_eq_some_iff.1 hk).2]
    simp [hp]
  unfold TermFn.get; rw [hf]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
/-- `TermFn.get` outside the domain is an error. -/
theorem TermConfsGet_none {α : Type} (f : TermFn α) (t : Int) (x : α)
    (h : TermFn.has f t = false) : f.get t ≠ .ok x := by
  have hf : f.find? (fun p => p.1 == t) = none := by
    rw [List.find?_eq_none]; intro y hy
    unfold TermFn.has at h; rw [List.any_eq_false] at h; exact h y hy
  unfold TermFn.get; rw [hf]; simp [evalError, throw, throwThe, MonadExceptOf.throw]

theorem TermConfs.Get.wp_proof : TermConfs.Get.spec (GF := GF) (hG := hG) := by
  intro sl f t x
  wp_start as ⟨#Hs, %Hx⟩
  iunfold termConfsRO at Hs
  icases Hs with ⟨%gs, #Hgs, #Hb⟩
  ihave %Hlen := ownSlice_len $$ Hgs
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  wp_auto
  ihave IH : iprop(∃ (n : w64) (y : G.TermConf),
      "i" ∷ i_ptr ↦ n ∗ "p" ∷ p_ptr ↦ y ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧ TermFn.has (f.take (sint.nat n)) (sint.Z t) = false⌝) $$ [i p]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · word
    · word
    · rw [show sint.nat (W64 0) = 0 from rfl]; rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < f.length := by rw [← Hl, Hlen.1]; word
    ihave ⟨%y0, %Hy, %HT, #HL⟩ := bigSepL2_at _ gs f (sint.nat n) Hlt $$ Hb
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) gs DFrac.discard y0 Hn.1 $$ [Hgs] as -
    · isplitr
      · iexact Hgs
      ipureintro; exact Hy
    try wp_auto
    obtain ⟨p0, Hp0⟩ : ∃ p, f[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hfp : f[sint.nat n]! = p0 := by simp [Hp0]
    have HT' : sint.Z y0.T' = p0.1 := by rw [HT, Hfp]
    wp_if_destruct
    · try wp_auto
      wp_for_post
      have hxe : x = p0.2 := by
        have h := TermConfsGet_found f (sint.nat n) p0 _ Hp0 Hn.2.2 HT'.symm
        rw [h] at Hx; cases Hx; rfl
      iapply HΦ
      rw [hxe, ← Hfp]
      iexact HL
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨?_, ?_, ?_⟩
      · word
      · word
      · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hp0]
        unfold TermFn.has at Hn ⊢
        rw [List.any_append, Hn.2.2]
        simp only [Option.toList_some, List.any_cons, List.any_nil, Bool.false_or, Bool.or_false,
          beq_eq_false_iff_ne, ne_eq]
        intro h; apply Hif; rw [← HT'] at h; exact BitVec.toInt_inj.mp h
  · exfalso
    have hnx : sint.nat n = f.length := by rw [← Hl, Hlen.1]; word
    have h := Hn.2.2
    rw [hnx, List.take_length] at h
    exact TermConfsGet_none f _ x h Hx

end proof

end AntCheck
end EtcdGrove
end Perennial
