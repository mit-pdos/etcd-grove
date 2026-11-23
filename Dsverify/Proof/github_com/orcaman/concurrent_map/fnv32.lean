/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/cmap/fnv32.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.orcaman.concurrent_map

set_option linter.unusedSectionVars false

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [concurrent_map.Assumptions] [sync.Assumptions]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem fnv32F_take_succ (key : GoString) (i : Nat) (b : w8) (h : key[i]? = some b) :
    (key.take (i + 1)).foldl fnv32Step (W32 2166136261) =
      fnv32Step ((key.take i).foldl fnv32Step (W32 2166136261)) b := by
  rw [List.take_add_one, h]
  simp [List.foldl_append]

theorem fnv32.wp_proof : fnv32.spec (GF := GF) := fun key => by
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  ihave HL : (∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "hash" ∷ hash_ptr ↦ (key.take (sint.nat iv)).foldl fnv32Step (W32 2166136261) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ key.length⌝ : IProp GF) $$ [i hash]
  · iexists (W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    iframe; ipureintro; constructor <;> word
  wp_for HL
  wp_if_destruct
  · have hb : sint.Z iv < key.length := by
      have := Hif; simp at this; word
    obtain ⟨b, hb'⟩ : ∃ b, key[sint.nat iv]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left Hi.1, hb']
    wp_auto
    wp_for_post
    iframe
    iexists _
    have hn : sint.nat (iv + W64 1) = sint.nat iv + 1 := by word
    rw [hn, fnv32F_take_succ key _ b hb']
    iframe
    ipureintro; constructor <;> word
  · have he : sint.nat iv = key.length := by
      have := Hif; simp at this; word
    rw [he, List.take_length, show key.foldl fnv32Step (W32 2166136261) = fnv32F key from rfl]
    iapply HΦ; itrivial

end proof

end Perennial.github_com.orcaman.concurrent_map
