/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyTCP__ClientSendChan.lean`, run `rabia-r1wake-1`.)

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

theorem ProxyTCP.ClientSendChan.wp_proof : ProxyTCP.ClientSendChan.spec (GF := GF) := by
  intro γ k p cid hcid
  wp_start as #Hro
  unfold proxyTcpRO
  icases Hro with ⟨%scs, %cns, %rds, %wrs, #HS, #HC, #HR, #HW, #Hlock⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  iunfold tableInv at Hinv
  icases Hinv with ⟨%chs, %cs, %rs, %ws, Hscs, Hcns, Hrds, Hwrs, %Hlen, #Hents⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcns
  ihave %Hsl := ownSlice_len _ _ _ $$ Hscs
  have hi : sint.Z (W64 (uint.Z cid)) = (cid.toNat : Int) := by
    unfold nC at hcid; word
  obtain ⟨hl1, hl2, hl3, hl4⟩ := Hlen
  have hb : 0 ≤ sint.Z (W64 (uint.Z cid)) ∧ sint.Z (W64 (uint.Z cid)) < sint.Z cns.len := by
    unfold nC at hcid hl2; rw [hi]; constructor <;> word
  have hb' : 0 ≤ sint.Z (W64 (uint.Z cid)) ∧ sint.Z (W64 (uint.Z cid)) < sint.Z scs.len := by
    unfold nC at hcid hl1; rw [hi]; constructor <;> word
  list_elem cs cid.toNat as cl
  list_elem chs cid.toNat as ch
  simp only [hb, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index cns _ cs _ cl hb.1 $$ [Hcns] with Hcns
  · iframe; ipureintro; rw [hi]; simpa using Hcl_lookup
  ihave Hent := (BigSepL.bigSepL_lookup (i := cid.toNat) Hcl_lookup) $$ Hents
  icases Hent with ⟨%ch', %Hch', #Hent⟩
  rw [Hch_lookup] at Hch'
  cases Hch'
  iunfold tableEntry at Hent
  icases Hent with (%Hnull | ⟨#Hc, %γch, #Hbag⟩)
  · subst Hnull
    wp_auto
    ihave Hinv : tableInv γ scs cns rds wrs $$ [Hscs Hcns Hrds Hwrs]
    · unfold tableInv
      iexists chs, cs, rs, ws
      iframe
      isplitr
      · ipureintro; exact ⟨hl1, hl2, hl3, hl4⟩
      iexact Hents
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hinv]
    iapply HΦ
    ileft; ipureintro; rfl
  · wp_if_destruct
    · ihave Hinv : tableInv γ scs cns rds wrs $$ [Hscs Hcns Hrds Hwrs]
      · unfold tableInv
        iexists chs, cs, rs, ws
        iframe
        isplitr
        · ipureintro; exact ⟨hl1, hl2, hl3, hl4⟩
        iexact Hents
      wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hinv]
      iapply HΦ
      ileft; ipureintro; rfl
    · simp only [hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index scs _ chs _ ch hb'.1 $$ [Hscs] with Hscs
      · iframe; ipureintro; rw [hi]; simpa using Hch_lookup
      ihave Hinv : tableInv γ scs cns rds wrs $$ [Hscs Hcns Hrds Hwrs]
      · unfold tableInv
        iexists chs, cs, rs, ws
        iframe
        isplitr
        · ipureintro; exact ⟨hl1, hl2, hl3, hl4⟩
        iexact Hents
      wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $Hinv]
      iapply HΦ
      iright; iexists γch; iexact Hbag

end proof

end Perennial.rabia.internal.tcp
