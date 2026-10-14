/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/checkOperations.lean`: with `noPartition`
there is one partition, the whole history, whose entries `makeEntries` returns.
-/
module

public import Spec.github_com.anishathalye.porcupine.checkOperations
public import Spec.github_com.anishathalye.porcupine.checkParallel
public import Spec.github_com.anishathalye.porcupine.makeEntries
public import Spec.github_com.anishathalye.porcupine.fillDefault

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine
  github_com.anishathalye.porcupine.Theory

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem checkOperations.wp_proof
    (wp_fillDefault : fillDefault.spec (GF := GF) (hG := hG))
    (wp_makeEntries : makeEntries.spec (GF := GF) (hG := hG))
    (wp_checkParallel : checkParallel.spec (GF := GF) (hG := hG)) :
    checkOperations.spec (GF := GF) (hG := hG) := by
  intro σ S m sl ops dq verbose dur Hops
  wp_start as ⟨#Hcci, #Hm, Hsl, #Hio⟩
  wp_auto
  wp_apply wp_fillDefault σ S m $$ [$Hm] as %m' ⟨#Hmf, #Hpart⟩
  iunfold noPartitionSpec at Hpart
  wp_apply Hpart $$ [$Hsl] as %psl ⟨Hpsl, Hsl⟩
  ihave %Hplen := ownSlice_len _ _ _ $$ Hpsl
  wp_apply wp_slice_make2 (V := GoSlice) psl.len as %lsl ⟨Hlsl, -⟩
  · ipureintro; word
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => gi
  have Hlen1 : sint.nat psl.len = 1 := by simp at Hplen; omega
  ihave HI : (∃ (j gv : w64) (sh : GoSlice) (ls : List GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "gi" ∷ gi_ptr ↦ gv ∗ "subhistory" ∷ subhistory_ptr ↦ sh ∗
      "Hlsl" ∷ lsl ↦* ls ∗ "Hsl" ∷ sl ↦*{dq} ops ∗
      "Hst" ∷ (⌜sint.Z j = 0 ∧ ls = [zero_val GoSlice]⌝ ∨
        (∃ (esl : GoSlice) (es : List entry),
          ⌜sint.Z j = 1 ∧ ls = [esl] ∧ EntriesFor (histOf ops) es⌝ ∗ esl ↦*□ es)) : IProp GF)
    $$ [i gi subhistory Hlsl Hsl]
  · iexists W64 0, zero_val w64, zero_val GoSlice,
      List.replicate (sint.nat psl.len) (zero_val GoSlice)
    iframe
    ileft; ipureintro; rw [Hlen1]; exact ⟨rfl, rfl⟩
  wp_for HI
  icases Hst with (%H0 | ⟨%esl, %es, %H1, #Hesl⟩)
  · obtain ⟨Hj, rfl⟩ := H0
    wp_if_destruct
    · have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len := ⟨by word, Hif⟩
      simp only [hb, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index psl (sint.Z j) [sl] _ sl hb.1 $$ [Hpsl] as Hpsl
      · iframe; ipureintro; rw [show (sint.Z j).toNat = 0 by word]; rfl
      wp_apply wp_makeEntries sl ops dq Hops $$ [$Hsl] as %esl ⟨%es, Hesl, %Hes, Hsl⟩
      ipersist Hesl
      ihave %Hllen := ownSlice_len _ _ _ $$ Hlsl
      have hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lsl.len := ⟨by word, by simp at Hllen; word⟩
      simp only [hb', and_self, ↓reduceIte]
      wp_apply wp_store_slice_index lsl (sint.Z j) [zero_val GoSlice] esl $$ [Hlsl] as Hlsl
      · iframe; ipureintro; simp; word
      wp_for_post
      iframe
      iexists j + W64 1, j, sl, _
      iframe
      iright
      iexists esl, es
      iframe Hesl
      ipureintro
      refine ⟨by word, ?_, Hes⟩
      rw [show (sint.Z j).toNat = 0 by word]; rfl
    · exfalso; apply Hif; word
  · wp_if_destruct
    · exfalso; word
    · obtain ⟨-, rfl, Hes⟩ := H1
      ipersist Hlsl
      have Hhio : histIoOk S (histOf ops) = opsIoOk S ops := by
        simp only [histIoOk, histOf, opsIoOk, BigSepL.bigSepL_map]; rfl
      wp_apply wp_checkParallel σ S m' lsl [esl] [histOf ops] verbose dur rfl (by simp)
        $$ [] as %r %info %Hr
      · iframe #
        isplitr
        · iexists histOf ops
          rw [Hhio]
          iframe #
          ipureintro
          refine ⟨rfl, Hes, ?_⟩
          have := Hops.1
          simp only [histOf, List.length_map]; omega
        · iapply BigSepL.bigSepL_nil.2; iempintro
      iapply HΦ
      ipureintro
      intro Hlin
      exact Hr (fun h hh => by simp at hh; subst hh; exact Hlin)

end proof

end porcupine
end EtcdGrove
end Perennial
