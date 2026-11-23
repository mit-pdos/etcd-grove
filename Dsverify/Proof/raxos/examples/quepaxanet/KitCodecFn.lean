/-
`Codec()` (`model.go`) meets remote's `codecOk` of the kit's store `qR γ` (`Kit.lean`): its seven
closures, over `KitCodec.lean`'s `EncIn`/`DecIn`/`EncOut`/`DecOut`.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitCodec

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

/-- `DecOut` on nothing fails. -/
theorem wp_DecOut_nil (b : GoSlice) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet ∗ b ↦*{dq} ([] : List w8) }}
      (App (Val (@! raxos.examples.quepaxanet.DecOut)) (Val #b))
    {{ (x : Out), RET (PairV #x #false); True }} := by
  wp_start as Hb
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · iapply HΦ
    itrivial
  · exfalso; revert Hif; have := Hbl.1; simp only [List.length_nil] at this; word

/-- **`Codec()` meets `codecOk`** of the kit's store. -/
theorem codec_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro γ
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk qR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_EncIn as %b Hb
    iapply HΦ'
    rw [show kin (In.mk i.1.put i.1.k i.1.v) = i.1 from rfl]
    iexact Hb
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_DecIn i.1 b dq $$ [Hb]
    · iexact Hb
    iapply HΦ'
    ipureintro
    intro _
    rfl
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨u, f, w, rfl⟩ : ∃ (u f : Bool) (w : GoString), v = outV (Out.mk u f w) := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, _, h⟩
      · exact ⟨_, _, _, h⟩
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_EncOut as %b Hb
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have hlt : (encOutB u f w).length < 2 ^ 63 := by
      have := Hbl.1; simp only at this; rw [this]; word
    rw [encOutV_outV u f w hlt]
    iapply HΦ'
    iexact Hb
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨u, f, w, rfl⟩ : ∃ (u f : Bool) (w : GoString), v = outV (Out.mk u f w) := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, _, h⟩
      · exact ⟨_, _, _, h⟩
    iintro !> %Φ' Hb HΦ'
    by_cases hlt : (encOutB u f w).length < 2 ^ 63
    · rw [encOutV_outV u f w hlt]
      wp_auto
      wp_apply wp_DecOut u f w b dq $$ [Hb]
      · iexact Hb
      iapply HΦ'
      ipureintro
      intro _
      rfl
    · have he : encOutV (outV (Out.mk u f w)) = [] := by
        unfold encOutV
        rw [dif_neg]
        rintro ⟨p, hp, hpl⟩
        have e := outV_inj hp
        simp only [Out.mk.injEq] at e
        obtain ⟨e1, e2, e3⟩ := e
        rw [e1, e2, e3] at hlt
        exact hlt hpl
      rw [he]
      wp_auto
      wp_apply wp_DecOut_nil b dq $$ [Hb] as %x -
      · iexact Hb
      iapply HΦ'
      ipureintro
      intro h; cases h
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    rw [qB_isWrite]
    iapply HΦ'
    itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

end proof

end raxos.examples.quepaxanet
end Perennial
