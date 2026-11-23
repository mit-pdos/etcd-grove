/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyTCP__NumConns.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/tcp.(*ProxyTCP).ClientSendChan`.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Spec
public import Dsverify.Proof.rabia.internal.tcp.Wg
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [package_sem : rabia.internal.tcp.Assumptions]

set_option goose.wp.extras true

theorem ProxyTCP.NumConns.wp_proof : ProxyTCP.NumConns.spec (GF := GF) := by
  intro γ k p
  wp_start as #Hro
  unfold proxyTcpRO
  icases Hro with ⟨%scs, %cns, %rds, %wrs, #HS, #HC, #HR, #HW, #Hlock⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  iunfold tableInv at Hinv
  icases Hinv with ⟨%chs, %cs, %rs, %ws, Hscs, Hcns, Hrds, Hwrs, %Hlen, #Hents⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcns
  obtain ⟨hl1, hl2, hl3, hl4⟩ := Hlen
  ihave HI : (∃ (i n : w64) (cv : Loc), "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗
      "Hcns" ∷ cns ↦* cs ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z cns.len⌝ : IProp GF)
    $$ [i n c Hcns]
  · iexists _, _, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · list_elem cs (sint.nat i) as x
    simp only [show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cns.len by constructor <;> word, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index cns _ cs _ x Hi.1 $$ [Hcns] with Hcns
    · iframe; ipureintro; exact Hx_lookup
    wp_if_destruct <;>
    · wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; constructor <;> word
  · ihave Hinv : tableInv γ scs cns rds wrs $$ [Hscs Hcns Hrds Hwrs]
    · unfold tableInv
      iexists chs, cs, rs, ws
      iframe
      isplitr
      · ipureintro; exact ⟨hl1, hl2, hl3, hl4⟩
      iexact Hents
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hinv]
    iapply HΦ
    itrivial

end proof

end Perennial.rabia.internal.tcp
