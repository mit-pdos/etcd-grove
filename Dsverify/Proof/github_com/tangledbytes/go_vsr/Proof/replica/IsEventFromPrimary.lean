/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/IsEventFromPrimary.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`isEventFromPrimary(&e)`: reads the event's type and, for a Prepare, Commit or StartView, its payload's replica id (the type assertions succeed: the payload is the type's).
(Proved.)
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- `r.isEventFromPrimary(ep)`: some bool. -/
theorem replica.wp_isEventFromPrimary (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica) (ms : List ipv4port.IPv4Port)
    (N : Nat) (hN : 0 < N) (ep : Loc) (ne : events.NetworkEvent) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ v.state'.ClusterMembers' ↦*□ ms ∗ ⌜ms.length = N⌝ ∗ ep ↦ ne ∗
        ((∃ m : Msg, events.isEvent ne.Event' m) ∨
          (∃ (t : w8) (d : GoInterface), ne.Event' ↦□ events.Event.mk t d ∗
            ⌜t = W8 100 ∨ t = W8 101⌝)) }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"isEventFromPrimary")) (Val #ep))
    {{ (b : Bool), RET #b; rp ↦ v ∗ ep ↦ ne }} := by
  wp_start as ⟨Hr, #Hms, %Hlen, Hep, Hev⟩
  icases Hev with (⟨%m, #Hev⟩ | ⟨%t, %d, #Hev, %ht⟩)
  · unfold events.isEvent
    icases Hev with ⟨%dat, #Hev, #Hpay⟩
    cases m
    case prepare =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, -⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_potentialPrimary rp v ms N hN) $$ [Hr] as Hr
      · iframe Hr Hms; ipureintro; exact Hlen
      iapply HΦ; iframe Hr Hep
    case commit =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, -⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_potentialPrimary rp v ms N hN) $$ [Hr] as Hr
      · iframe Hr Hms; ipureintro; exact Hlen
      iapply HΦ; iframe Hr Hep
    case startView =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx, -⟩
      obtain ⟨rfl, -⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_potentialPrimary rp v ms N hN) $$ [Hr] as Hr
      · iframe Hr Hms; ipureintro; exact Hlen
      iapply HΦ; iframe Hr Hep
    all_goals
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      iapply HΦ; iframe Hr Hep
  · rcases ht with rfl | rfl <;>
    · iStructNamed Hev
      wp_auto
      iapply HΦ; iframe Hr Hep

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
