/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/SendNewState.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`sendNewState`: the NewState of the replica's log after `logsFrom` (`newState_own`; `Logs.After` in the closure).
(Stub: the spec, for parallel proving; `sorry` until proved.)
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

/-- `r.sendNewState(a, k)`. -/
theorem replica.wp_sendNewState (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica) (γ : VsrGhost.Names) (tcp : Loc)
    (C : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (a : ipv4port.IPv4Port) (k : w64) (lg : List Entry) (hk : 0 ≤ sint.Z k)
    (hkl : sint.nat k ≤ lg.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        log.ownLogs v.state'.Logs' DFrac.discard lg ∗
        VsrGhost.fact γ (.msg (.newState (uint.nat v.state'.ViewNumber') (lg.drop (sint.nat k))
          (uint.nat v.state'.CommitNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendNewState")) (Val #a)) (Val #k))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hlog, #Hf⟩
  ihave ⟨%Hlb0, -⟩ := log.ownLogs_bound _ _ _ $$ Hlog
  have Hlb : ∀ e ∈ lg.drop (sint.nat k), e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 :=
    fun e he => Hlb0 e (List.mem_of_mem_drop he)
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.newState (uint.nat v.state'.ViewNumber') (lg.drop (sint.nat k))
      (uint.nat v.state'.CommitNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID')) := by
    msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ logsFrom_ptr ↦ k ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ logsFrom_ptr ↦ k ∗ rp ↦ v))) $$ [Hsnd r logsFrom Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r logsFrom Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, logsFrom, Hr⟩ HΦ'
    wp_auto
    icases typedPointsto_not_null_dup _ _ _ $$ Hr with ⟨Hr, %Hnn⟩
    iStructNamed Hr
    icases typedPointsto_not_null_dup _ _ _ $$ state with ⟨state, %Hnn2⟩
    iStructNamed state
    wp_apply (log.Logs.After.wp_proof _ (DFrac.own 1) v.state'.Logs' lg k hk hkl) $$ [Logs]
      as %sl' ⟨Logs, #Hl'⟩
    · iframe Logs Hlog
    ihave state := typedPointsto_combine _ v.state' (DFrac.own 1) Hnn2 $$ [ID ViewNumber CommitNumber OpNum ClientTable ClusterMembers Logs Status]
    · simp only [TypedPointsto.typedPointstoDef, named]; iframe
    ihave Hr := typedPointsto_combine _ v (DFrac.own 1) Hnn $$ [state network time logger srvhandler heartbeattimeout internal]
    · simp only [TypedPointsto.typedPointstoDef, named]; iframe
    try wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.newState (uint.nat v.state'.ViewNumber') (lg.drop (sint.nat k)) (uint.nat v.state'.CommitNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        isplitl []
        · ipureintro
          refine ⟨rfl, ?_⟩
          simp
        · iexact Hl'
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, logsFrom, Hr⟩ | ⟨%_, r, logsFrom, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
