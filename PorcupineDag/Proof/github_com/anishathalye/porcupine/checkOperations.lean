/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/checkOperations.lean` (v1.3.1's, adapted to
PR #46): the `maxClientId` loop (the largest id seen, at least `0`: below the client count the
caller's `ClientIdsOk` bounds, `allocOk_max`); with `noPartition` there is one partition, the whole
history, which `makeEntries` splits into the chains `chainsOf ops (maxClientId + 1)`;
`checkParallel` decides `LinearizableCO` at their order, the client order (`OpsLemmas.lean`).
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.checkOperations
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.checkParallel
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.makeEntries
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.fillDefault
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.OpsLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem checkOperations.wp_proof
    (wp_fillDefault : fillDefault.spec (GF := GF) (hG := hG))
    (wp_makeEntries : makeEntries.spec (GF := GF) (hG := hG))
    (wp_checkParallel : checkParallel.spec (GF := GF) (hG := hG)) :
    checkOperations.spec (GF := GF) (hG := hG) := by
  intro σ S m c sl ops dq verbose dur
  wp_start as ⟨#Hcci, #Hm, #Hlin, Hsl, #Hio, %Hops, %Hcl⟩
  wp_auto
  wp_apply wp_fillDefault σ S m $$ [$Hm] as %m' ⟨#Hmf, #Hpart⟩
  ihave %Hslen := ownSlice_len $$ Hsl
  have hn := Hops.1
  ihave IM : iprop(∃ (n mx : w64) (x : Operation),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ x ∗ "maxClientId" ∷ maxClientId_ptr ↦ mx ∗
      "Hsl" ∷ sl ↦*{dq} ops ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ops.length : Int) ∧ 0 ≤ sint.Z mx ∧
        (∀ (k : Nat) (o : Operation), k < sint.nat n → ops[k]? = some o →
          sint.Z o.ClientId' ≤ sint.Z mx) ∧
        (sint.Z mx = 0 ∨ ∃ o ∈ ops, sint.Z o.ClientId' = sint.Z mx)⌝)
    $$ [i op maxClientId Hsl]
  · iexists W64 0, W64 0, zero_val Operation
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, by word, fun k o hk => by word, Or.inl rfl⟩
  wp_for IM
  wp_if_destruct
  · have Hlt : sint.nat n < ops.length := by word
    obtain ⟨o, Ho⟩ : ∃ o, ops[sint.nat n]? = some o := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index sl (sint.Z n) _ _ o Hn.1 $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; rw [show (sint.Z n).toNat = sint.nat n from rfl]; exact Ho
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, o.ClientId', o
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, by word, fun k o' hk ho' => ?_,
        Or.inr ⟨o, List.mem_of_getElem? Ho, rfl⟩⟩
      rw [Hn1] at hk
      rcases Nat.lt_or_ge k (sint.nat n) with hk' | hk'
      · have := Hn.2.2.2.1 k o' hk' ho'; word
      · have : k = sint.nat n := by omega
        subst this; rw [Ho] at ho'; cases ho'; word
    · wp_for_post
      iframe
      iexists n + W64 1, mx, o
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, Hn.2.2.1, fun k o' hk ho' => ?_, Hn.2.2.2.2⟩
      rw [Hn1] at hk
      rcases Nat.lt_or_ge k (sint.nat n) with hk' | hk'
      · exact Hn.2.2.2.1 k o' hk' ho'
      · have : k = sint.nat n := by omega
        subst this; rw [Ho] at ho'; cases ho'; word
  · -- the client count `nc = maxClientId + 1`
    have Hnend : sint.nat n = ops.length := by word
    have Hmx0 := Hn.2.2.1
    have Hall : ∀ o ∈ ops, sint.Z o.ClientId' ≤ sint.Z mx := by
      intro o ho
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
      exact Hn.2.2.2.1 k _ (by omega) (List.getElem?_eq_getElem hk)
    have Hmxc : (ops = [] ∧ sint.Z mx = 0) ∨
        ∃ o ∈ ops, 0 ≤ sint.Z mx ∧ sint.Z mx ≤ sint.Z o.ClientId' := by
      rcases Hn.2.2.2.2 with h0 | ⟨o, ho, he⟩
      · cases hops : ops with
        | nil => exact Or.inl ⟨rfl, h0⟩
        | cons o os =>
          refine Or.inr ⟨o, List.mem_cons_self, Hmx0, ?_⟩
          have := (Hcl.1 o (by rw [hops]; exact List.mem_cons_self)).1
          omega
      · exact Or.inr ⟨o, ho, Hmx0, by omega⟩
    have Halloc := allocOk_max Hcl.1 Hmxc
    have Hmxs : sint.Z mx < 2 ^ 44 := by
      simp only [AllocOk, maxAllocBytes] at Halloc
      have h6 : (6 : Int) ≤ ((max ops.length 6 : Nat) : Int) := by omega
      have h1 : ((((sint.Z mx).toNat + 1 : Nat) : Int)) * 6 ≤
          ((((sint.Z mx).toNat + 1 : Nat) : Int)) * ((max ops.length 6 : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_left h6 (by omega)
      have h2 : ((((sint.Z mx).toNat + 1 : Nat) : Int)) = sint.Z mx + 1 := by
        push_cast; rw [Int.toNat_of_nonneg Hmx0]
      rw [h2] at h1 Halloc
      generalize (sint.Z mx + 1) * ((max ops.length 6 : Nat) : Int) = X at h1 Halloc
      omega
    have Hnc : sint.Z (mx + W64 1) = sint.Z mx + 1 := by word
    have Hncn : sint.nat (mx + W64 1) = (sint.Z mx).toNat + 1 := by word
    have Hnc0 : 0 ≤ sint.Z (mx + W64 1) := by rw [Hnc]; exact Int.add_nonneg Hmx0 (by decide)
    have Hids : IdsBelow ops (sint.nat (mx + W64 1)) := by
      intro o ho
      refine ⟨(Hcl.1 o ho).1, ?_⟩
      have := Hall o ho
      rw [Hncn]; push_cast; rw [Int.toNat_of_nonneg Hmx0]; omega
    have Hids' : ∀ o ∈ ops, 0 ≤ sint.Z o.ClientId' ∧ sint.Z o.ClientId' < sint.Z (mx + W64 1) := by
      intro o ho
      have := Hids o ho
      refine ⟨this.1, ?_⟩
      rw [Hnc]; have := Hall o ho; omega
    have Halloc' : AllocOk (sint.nat (mx + W64 1)) ops.length := by rw [Hncn]; exact Halloc
    -- one partition
    iunfold noPartitionSpec at Hpart
    wp_apply Hpart $$ [$Hsl] as %psl ⟨Hpsl, Hsl⟩
    ihave %Hplen := ownSlice_len $$ Hpsl
    have Hlen1 : sint.nat psl.len = 1 := by simp at Hplen; omega
    wp_apply wp_slice_make2 (V := GoSlice) psl.len as %lsl ⟨Hlsl, -⟩
    · ipureintro; word
    wp_apply wp_slice_make2 (V := GoSlice) psl.len as %osl ⟨Hosl, -⟩
    · ipureintro; word
    rename_i gi_ptr
    irename : (gi_ptr ↦ zero_val w64 : IProp GF) => gi
    ihave HI : (∃ (j gv : w64) (sh : GoSlice) (ls os : List GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "gi" ∷ gi_ptr ↦ gv ∗ "subhistory" ∷ subhistory_ptr ↦ sh ∗
        "Hlsl" ∷ lsl ↦* ls ∗ "Hosl" ∷ osl ↦* os ∗ "Hsl" ∷ sl ↦*{dq} ops ∗
        "Hst" ∷ (⌜sint.Z j = 0 ∧ ls = [zero_val GoSlice] ∧ os = [zero_val GoSlice]⌝ ∨
          (∃ (esl ohsl : GoSlice),
            ⌜sint.Z j = 1 ∧ ls = [esl] ∧ os = [ohsl]⌝ ∗
            ohistOwn ohsl (histOf ops) (chainsOf ops (sint.nat (mx + W64 1))))) : IProp GF)
      $$ [i gi subhistory Hlsl Hosl Hsl]
    · iexists W64 0, zero_val w64, zero_val GoSlice,
        List.replicate (sint.nat psl.len) (zero_val GoSlice),
        List.replicate (sint.nat psl.len) (zero_val GoSlice)
      iframe
      ileft; ipureintro; rw [Hlen1]; exact ⟨rfl, rfl, rfl⟩
    wp_for HI
    icases Hst with (%H0 | ⟨%esl, %ohsl, %H1, Hoh⟩)
    · obtain ⟨Hj, rfl, rfl⟩ := H0
      wp_if_destruct
      · have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len := ⟨by word, Hif⟩
        simp only [hb, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index psl (sint.Z j) [sl] _ sl hb.1 $$ [Hpsl] as Hpsl
        · iframe; ipureintro; rw [show (sint.Z j).toNat = 0 by word]; rfl
        ihave %Hllen := ownSlice_len $$ Hlsl
        ihave %Holen := ownSlice_len $$ Hosl
        have hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lsl.len := ⟨by word, by simp at Hllen; word⟩
        have hb'' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨by word, by simp at Holen; word⟩
        simp only [hb', and_self, ↓reduceIte]
        wp_auto
        simp only [hb'', and_self, ↓reduceIte]
        wp_auto
        wp_apply wp_makeEntries sl ops dq (mx + W64 1) Hops Hnc0 Halloc' Hids' $$ [$Hsl]
          as %esl %ohsl ⟨-, Hoh, Hsl⟩
        wp_apply wp_store_slice_index lsl (sint.Z j) [zero_val GoSlice] esl $$ [Hlsl] as Hlsl
        · iframe; ipureintro; simp; word
        wp_apply wp_store_slice_index osl (sint.Z j) [zero_val GoSlice] ohsl $$ [Hosl] as Hosl
        · iframe; ipureintro; simp; word
        wp_for_post
        iframe
        iexists j + W64 1, j, sl, _, _
        iframe
        iright
        iexists esl, ohsl
        iframe Hoh
        ipureintro
        refine ⟨by word, ?_, ?_⟩ <;> rw [show (sint.Z j).toNat = 0 by word] <;> rfl
      · exfalso; apply Hif; word
    · wp_if_destruct
      · exfalso; word
      · obtain ⟨-, rfl, rfl⟩ := H1
        ipersist Hosl
        have Hhio : histIoOk S (histOf ops) = opsIoOk S ops := by
          simp only [histIoOk, histOf, opsIoOk, BigSepL.bigSepL_map]; rfl
        wp_apply wp_checkParallel σ S m' c osl [ohsl] [histOf ops]
          [chainsOf ops (sint.nat (mx + W64 1))] lsl verbose dur rfl rfl (by simp)
          $$ [Hoh] as %r %info %Hr
        · iframe #
          iapply BigSepL.bigSepL_cons.2
          isplitl [Hoh]
          · iexists histOf ops, chainsOf ops (sint.nat (mx + W64 1))
            rw [Hhio]
            iframe #
            iframe Hoh
            ipureintro
            refine ⟨rfl, rfl, chainsOk_chainsOf Hids Hcl.2, histWf_histOf Hops, ?_⟩
            rw [chainsOf_length]
            simp only [histOf, List.length_map]
            exact Halloc'
          · iapply BigSepL.bigSepL_nil.2; iempintro
        iapply HΦ
        iframe Hsl
        ipureintro
        have Hone : (∀ (i : Nat) h cs, [histOf ops][i]? = some h →
            [chainsOf ops (sint.nat (mx + W64 1))][i]? = some cs →
            LinearizableCO S.M h (chainOrder cs)) ↔
            LinearizableCO S.M (histOf ops) (clientOrder ops) := by
          rw [← linCO_chains_iff Hids]
          constructor
          · intro H; exact H 0 _ _ rfl rfl
          · intro H i h cs hh hc
            cases i with
            | zero => cases hh; cases hc; exact H
            | succ i => simp at hh
        rw [Hone] at Hr
        exact Hr

end proof

end porcupine
end EtcdGrove
end Perennial
