/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/ConsumeSQ.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`consumeSQ`: pops one event (with its `sqElem`), processes it, and resets the view-change timer if it came from the primary.
(Proved.)
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.Logs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.ProcessEvent
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.IsEventFromPrimary

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

/-- One round's event. -/
theorem replica.wp_consumeSQ (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"consumeSQ")) (Val #()))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as Hown
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (queue.Queue.Pop.wp events.NetworkEvent.ty (replica.sqElem γ tcp) v.internal'.sq')
    $$ [] as %ne %ok Hel
  · iexact Hsq
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    close_own
  simp only [↓reduceIte]
  ihave #HE : iprop((∃ m : Msg, events.isEvent ne.Event' m) ∨
      (∃ (t : w8) (d : GoInterface), ne.Event' ↦□ events.Event.mk t d ∗
        ⌜t = W8 100 ∨ t = W8 101⌝)) $$ [Hel]
  · unfold replica.sqElem
    icases Hel with (⟨%m, #Hev, -⟩ | ⟨%d, #Hev, -⟩ | #Hev)
    · ileft; iexists m; iexact Hev
    · iright; iexists _, _; iframe Hev; ipureintro; right; rfl
    · iright; iexists _, _; iframe Hev; ipureintro; left; rfl
  ihave Hown : replica.ownR rp γ r tcp $$ [Hr Hsender Hrep Hcap Hstore Htbl Hpk Hpks Hsv Hsvs Hdv
      Hdvs Hvct Hct Hgst]
  · unfold replica.ownR
    iexists v
    iframe Hr
    unfold replica.repInv
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  wp_auto
  wp_apply (replica.wp_processEvent H rp γ r tcp ne) $$ [Hown Hel] as Hown
  · iframe Hown Hel
  clear Hid Hmslen Hnet Htime Hstatus Hst Hopnum Hcommit Hmine Htmine Htlog
  iclear Hms Haddrs HisTCP Hprotos Hlogger Hsrv Hcodec Hkit Hsys HregI Hsq Hlog Hcfact Hmlin Hmcom Htres
  clear v lg mine cw mw me C F P ms tbl pk sv dv vst cst
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  try wp_auto
  wp_apply (replica.wp_isEventFromPrimary H rp v ms n (by omega) e_ptr ne) $$ [Hr e] as %b ⟨Hr, e⟩
  · iframe Hr Hms e HE; ipureintro; exact Hmslen
  wp_if_destruct
  · try wp_auto
    close_own
  · ihave ⟨%t, %d, #Hev⟩ : iprop(∃ (t : w8) (d : GoInterface), ne.Event' ↦□ events.Event.mk t d) $$ []
    · icases HE with (⟨%m, #Hev⟩ | ⟨%t, %d, #Hev, -⟩)
      · unfold events.isEvent
        icases Hev with ⟨%d, #Hev, -⟩
        iexists _, _; iexact Hev
      · iexists _, _; iexact Hev
    iStructNamed Hev
    wp_log
    wp_apply time.Timer.Reset.wp $$ [Hvct] as Hvct
    · iexact Hvct
    close_own

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
