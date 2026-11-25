/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/ProcessEvent.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`processEvent(e)`: dispatches on the event's type to its handler (the type assertions succeed: `sqElem`); a ProposeViewChange starts a view change to the next view (unless the view is the largest); other types are logged.
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
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Request
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Prepare
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.PrepareOK
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.InternalPrepareOK
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Commit
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.StartViewChange
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.DoViewChange
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.StartView
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.GetState
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.NewState
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.InitiateViewChange

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section inj
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [sem : go.Semantics]
variable [package_sem : replica.Assumptions]

/-- A struct field's value is determined by the struct's value (its `StructFieldGet` is a
deterministic pure step). -/
theorem replica.field_of_intoVal {V W : Type} [go.IntoValInj W] {U : go.GoType} {f : GoString}
    (proj : V → W)
    (hget : ∀ x : V, go.IsGoStepPureDetTagged under (StructFieldGet U f) #x (Val #(proj x)))
    {x x' : V} (h : (#x : val) = #x') : proj x = proj x' := by
  have h1 := (hget x).isGoStep_det_internal.isGoStep_pure_det
  have h2 := (hget x').isGoStep_det_internal.isGoStep_pure_det
  rw [h] at h1
  rw [h1] at h2
  have h3 := congrFun h2 (Val #(proj x'))
  simp only [eq_iff_iff, iff_true] at h3
  injection h3 with h4
  exact go.intoVal_inj h4

instance replica.intoValInj_DoViewChange : go.IntoValInj events.DoViewChange where
  intoVal_inj := by
    intro x x' h
    have h1 := replica.field_of_intoVal (W := w64) events.DoViewChange.ViewNum'
      events.DoViewChange.TypeAssumptions.get_ViewNum h
    have h2 := replica.field_of_intoVal (W := GoSlice) events.DoViewChange.Logs'
      events.DoViewChange.TypeAssumptions.get_Logs h
    have h3 := replica.field_of_intoVal (W := w64) events.DoViewChange.LastStableViewNum'
      events.DoViewChange.TypeAssumptions.get_LastStableViewNum h
    have h4 := replica.field_of_intoVal (W := w64) events.DoViewChange.OpNum'
      events.DoViewChange.TypeAssumptions.get_OpNum h
    have h5 := replica.field_of_intoVal (W := w64) events.DoViewChange.CommitNum'
      events.DoViewChange.TypeAssumptions.get_CommitNum h
    have h6 := replica.field_of_intoVal (W := w64) events.DoViewChange.ReplicaID'
      events.DoViewChange.TypeAssumptions.get_ReplicaID h
    cases x; cases x'; simp_all

instance replica.intoValInj_StartView : go.IntoValInj events.StartView where
  intoVal_inj := by
    intro x x' h
    have h1 := replica.field_of_intoVal (W := w64) events.StartView.ViewNum'
      events.StartView.TypeAssumptions.get_ViewNum h
    have h2 := replica.field_of_intoVal (W := w64) events.StartView.OpNum'
      events.StartView.TypeAssumptions.get_OpNum h
    have h3 := replica.field_of_intoVal (W := w64) events.StartView.CommitNum'
      events.StartView.TypeAssumptions.get_CommitNum h
    have h4 := replica.field_of_intoVal (W := GoSlice) events.StartView.Logs'
      events.StartView.TypeAssumptions.get_Logs h
    have h5 := replica.field_of_intoVal (W := w64) events.StartView.ReplicaID'
      events.StartView.TypeAssumptions.get_ReplicaID h
    cases x; cases x'; simp_all

end inj

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- A queued event. -/
theorem replica.wp_processEvent (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (ne : events.NetworkEvent) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ replica.sqElem γ tcp ne }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"processEvent")) (Val #ne))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, He⟩
  unfold replica.sqElem
  icases He with (⟨%m, #Hev, #Hfact, #Haddr, Hcap⟩ | ⟨%d, #Hev, #Hfact, #Haddr⟩ | #Hev)
  · unfold events.isEvent
    icases Hev with ⟨%dat, #Hev, #Hpay⟩
    cases m
    case request id cid op =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onRequest H rp γ r tcp ne.Src' x) $$ [Hown] as Hown
      · iframe Hown Haddr Hfact
      iapply HΦ; iexact Hown
    case reply id cid w res =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, -⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      unfold replica.ownR
      icases Hown with ⟨%v, Hr, Hinv⟩
      unfold replica.repInv
      iNamed Hinv
      wp_auto
      wp_log
      close_own
    case prepare w k c e rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      cases e
      obtain ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onPrepare H rp γ r tcp ne.Src' x) $$ [Hown] as Hown
      · iframe Hown Haddr Hfact
      iapply HΦ; iexact Hown
    case prepareOK w k rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onPrepareOK H rp γ r tcp ne.Src' x) $$ [Hown] as Hown
      · iframe Hown Hfact
      iapply HΦ; iexact Hown
    case commit w c rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onCommit H rp γ r tcp ne.Src' x) $$ [Hown] as Hown
      · iframe Hown Haddr Hfact
      iapply HΦ; iexact Hown
    case startViewChange w rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, -⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onStartViewChange H rp γ r tcp ne.Src' x) $$ [Hown] as Hown
      · iframe Hown
      iapply HΦ; iexact Hown
    case doViewChange dvc =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx, #Hlogs⟩
      obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := hx
      unfold events.evCap
      icases Hcap with ⟨%x', #Hev', Hcap⟩
      icombine Hev Hev' gives %hxx
      have hx' : x' = x := by
        simp only [events.typeOf, events.Event.mk.injEq, _root_.true_and] at hxx
        simp at hxx
        exact (go.intoVal_inj hxx).symm
      subst hx'
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onDoViewChange H rp γ r tcp ne.Src' x') $$ [Hown Hcap] as Hown
      · iframe Hown
        unfold replica.dvcOk
        iexists dvc
        iframe Hcap Hlogs Hfact
        ipureintro
        omega
      iapply HΦ; iexact Hown
    case startView w k c logs rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx, #Hlogs⟩
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
      unfold events.evCap
      icases Hcap with ⟨%x', #Hev', Hcap⟩
      icombine Hev Hev' gives %hxx
      have hx' : x' = x := by
        simp only [events.typeOf, events.Event.mk.injEq, _root_.true_and] at hxx
        simp at hxx
        exact (go.intoVal_inj hxx).symm
      subst hx'
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onStartView H rp γ r tcp ne.Src' x' logs) $$ [Hown Hcap] as Hown
      · iframe Hown Hcap Hlogs Hfact
      iapply HΦ; iexact Hown
    case getState w k rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      obtain ⟨rfl, -⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onGetState H rp γ r tcp ne.Src' x) $$ [Hown] as Hown
      · iframe Hown Haddr
      iapply HΦ; iexact Hown
    case newState w logs c k rid =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx, #Hlogs⟩
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hx
      simp only [events.typeOf]
      iStructNamed Hev
      wp_auto
      wp_apply (replica.wp_onNewState H rp γ r tcp ne.Src' x logs) $$ [Hown] as Hown
      · iframe Hown Hlogs Hfact
      iapply HΦ; iexact Hown
    case heartbeat =>
      unfold events.payloadOf
      icases Hpay with ⟨%x, %hx⟩
      subst hx
      simp only [events.typeOf]
      iStructNamed Hev
      unfold replica.ownR
      icases Hown with ⟨%v, Hr, Hinv⟩
      unfold replica.repInv
      iNamed Hinv
      wp_auto
      wp_log
      close_own
  · -- an internal PrepareOK
    iStructNamed Hev
    wp_auto
    wp_apply (replica.wp_onInternalPrepareOK H rp γ r tcp ne.Src' d) $$ [Hown] as Hown
    · iframe Hown Haddr Hfact
    iapply HΦ; iexact Hown
  · -- ProposeViewChange
    iStructNamed Hev
    unfold replica.ownR
    icases Hown with ⟨%v, Hr, Hinv⟩
    wp_auto
    wp_if_destruct
    · iapply HΦ; iexists v; iframe Hr Hinv
    · have hlt : uint.nat v.state'.ViewNumber' < uint.nat (v.state'.ViewNumber' + W64 1) := by
        have : v.state'.ViewNumber' ≠ W64 18446744073709551615 := by simpa using Hif
        have : uint.Z v.state'.ViewNumber' ≠ 18446744073709551615 := fun h => this (by word)
        word
      wp_apply (replica.wp_initiateViewChange H rp γ r tcp v (v.state'.ViewNumber' + W64 1))
        $$ [Hr Hinv] as ⟨%v', Hr, Hinv, -⟩
      · iframe Hr Hinv; ipureintro; exact hlt
      iapply HΦ; iexists v'; iframe Hr Hinv

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
