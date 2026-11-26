/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/SubmitRun.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`rp.Submit(ev)` (the assertion that the replica is not running, the queue push of a received
event: `sqElem`'s first disjunct) and `rp.Run()` (the assertion, `setIsRunning(true)`, the
deferred `setIsRunning(false)`, `consumeSQ`, `checkTimers`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.ConsumeSQ
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.CheckTimers

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

theorem replica.wp_setIsRunning (rp : Loc) (v : replica.Replica) (b : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"setIsRunning")) (Val #b))
    {{ RET #(); rp ↦ { v with internal' := { v.internal' with running' := b } } }} := by
  wp_start as Hr
  wp_auto
  wp_end

/-- `repInv` does not read the `running` flag. -/
theorem replica.repInv_running (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) (v : replica.Replica)
    (b : Bool) :
    replica.repInv (GF := GF) γ r tcp v ⊢
      replica.repInv γ r tcp { v with internal' := { v.internal' with running' := b } } := by
  have h : replica.repInv (GF := GF) γ r tcp { v with internal' := { v.internal' with running' := b } } =
      replica.repInv γ r tcp v := rfl
  rw [h]

theorem replica.Replica.Submit.wp_proof
    (wp_Assert : assert.Assert.spec (GF := GF) (hG := hG))
    (wp_Push : queue.Queue.Push.spec (GF := GF) (hG := hG)) :
    replica.Replica.Submit.spec (GF := GF) (hG := hG) := by
  intro rp γ r tcp ev
  wp_start as ⟨Hown, ⟨%m, #Hev, #Hf, #Ha, Hecap⟩⟩
  unfold replica.isReplica replica.own
  icases Hown with ⟨%v, Hr, %Hrun, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  rw [Hrun]
  wp_apply wp_Assert
  wp_apply (wp_Push events.NetworkEvent.ty (replica.sqElem γ tcp) v.internal'.sq' ev)
    $$ [Hecap]
  · iframe Hsq
    unfold replica.sqElem
    ileft; iexists m; iframe Hev Hf Ha Hecap
  iapply HΦ
  iexists v
  iframe Hr
  isplitr
  · ipureintro; exact Hrun
  iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
  iFrameNamed
  ipureintro
  exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩

theorem replica.Replica.Run.wp_proof (H : replica.Hyps (GF := GF) (hG := hG)) : replica.Replica.Run.spec (GF := GF) (hG := hG) := by
  intro rp γ r tcp
  wp_start as Hown
  unfold replica.isReplica replica.own
  icases Hown with ⟨%v, Hr, %Hrun, Hinv⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  rw [Hrun]
  wp_apply H.wp_Assert
  wp_apply replica.wp_setIsRunning rp v true $$ [Hr] as Hr
  · iexact Hr
  try wp_auto
  ihave Hown : replica.ownR rp γ r tcp $$ [Hr Hinv]
  · unfold replica.ownR
    iexists _; iframe Hr
    iapply replica.repInv_running $$ Hinv
  wp_apply replica.wp_consumeSQ H rp γ r tcp $$ [Hown] as Hown
  · iexact Hown
  wp_apply replica.wp_checkTimers H rp γ r tcp $$ [Hown] as Hown
  · iexact Hown
  try wp_auto
  unfold replica.ownR
  icases Hown with ⟨%v2, Hr, Hinv⟩
  wp_apply replica.wp_setIsRunning rp v2 false $$ [Hr] as Hr
  · iexact Hr
  try wp_auto
  iapply HΦ
  iexists _
  iframe Hr
  isplitr
  · ipureintro; rfl
  iapply replica.repInv_running $$ Hinv

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
