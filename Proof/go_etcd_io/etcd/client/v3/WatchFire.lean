/-
**A watch's read update, fired** (D47, 2026-10-26). Lean-first (no Rocq counterpart).

* (G2's follow-up, 2026-10-30) the firing itself is the server's law `srvKVCoreM_fire` (until then
  `watch_fire` here, auth off only): with the server's KV core in either auth mode and the start
  log sealed, the caller's persistent read update of the KV state fires at the committed state,
  whose log extends a certified, sealed log `L`.
* `raw_to_state`: a response at the server's level (`client.rawRespOk`: its events a watched
  log's) is a read of the state (`watchStateRespOk`): the update fires at the watched log (the start
  log if none), and the state's events are the log's (`rangeEvents_kvStateOf`,
  `rangeLogEvents_prefix`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## A response at the server's level, as a read of the state -/

section convert
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode

/-- The delivered events of a watched log's events, their key-values fixed, are the events. -/
theorem eventsIs_of_fixed (evs : List mvcc.EvM) (kvs : List Loc) (hkl : kvs.length = evs.length) :
    □ (∀ (k : Nat) (ev : mvcc.EvM) (kv : Loc), ⌜evs[k]? = some ev⌝ → ⌜kvs[k]? = some kv⌝ →
        mvcc.kvPtrFixed (GF := GF) kv ev.kv) ⊢
      eventsIs (List.zipWith client.evModelOf evs kvs) evs := by
  iintro #Hkv
  unfold eventsIs
  isplitr
  · ipureintro; simp [hkl]
  iintro !> %i %e %ev %he %hev
  cases hk : kvs[i]? with
  | none => simp [List.getElem?_zipWith, hev, hk] at he
  | some kv =>
    simp [List.getElem?_zipWith, hev, hk] at he
    subst he
    ihave #Hf := Hkv $$ %i %ev %kv %hev %hk
    ihave ⟨#Hv, -⟩ := client.kvPtrFixed_facts kv ev.kv $$ Hf
    unfold eventIs client.evModelOf
    iframe Hv
    ipureintro
    exact ⟨by unfold mvcc.evType; rfl, rfl, rfl⟩

/-- **A sealed log is a well-formed small log** (D48): the seal's facts (as `idxSealed_pure`'s)
and, with the receipts' bound, its changes' (as `idxSealed_small`'s). -/
theorem sealed_logOk (γ : mvcc.IdxNames) (log : mvcc.Log) (hrb : receiptBound GF ≤ 2 ^ 62) :
    mvcc.idxSealed (GF := GF) γ log ⊢
      ⌜mvcc.LogWf' log ∧ log.length < 2 ^ 63 ∧ txn.LogSmall log⌝ := by
  unfold mvcc.idxSealed
  iintro ⟨-, %Hp, %Hm⟩
  ipureintro
  refine ⟨Hp.1, Hp.2.1, ?_⟩
  unfold txn.LogSmall txn.logChanges; unfold mvcc.logCh at Hm; omega

/-- **A response at the server's level is a read of the state** (see the file header): the caller's
read update fires (`srvKVCoreM_fire`, in the member's auth mode `on`) at the watched log the response's facts are of (the start log if
none), at a state `σ` whose events are that log's, so the response's are `σ`'s; with the receipts'
bound, `σ` is well formed through the position the response moves to (the watched log's state's
prefix, `kvLogOkTo_of_prefix`). -/
theorem raw_to_state (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (γ : KVNames) (hst : γ.st = γr.kv.st)
    (hlog : γr.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (Q : KVState → IProp GF) :
    ⊢ srvKVCoreM on E γr -∗ mvcc.idxSealed E.γ.idx [[], []] -∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) -∗
      posQ o Q c -∗ client.rawRespOk E.γ o c c' v r ={⊤}=∗
      ∃ σ : KVState, □ Q σ ∗ watchStateRespOk o σ c c' v r := by
  have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
  iintro #Hinvs #H0 #Hau #Hpos #Hraw
  -- the update fired at the start log (a certified log of two revisions)
  imod srvKVCoreM_fire on E γr γ hst hlog [[], []] Q $$ Hinvs H0 H0 [] Hau with ⟨%C0, #HQ0, -⟩
  · unfold mvcc.certOk; ileft; ipureintro; simp
  unfold client.rawRespOk
  icases Hraw with (⟨%Herr, #Hse⟩ | %Hne | ⟨%Hp, (%Hle | ⟨%L, #HL, %HLp⟩)⟩ |
    ⟨%Hev, %L, %kvs, #HL, %HLe, #Hkv⟩)
  · imodintro; iexists kvStateOf C0; iframe HQ0
    unfold watchStateRespOk; ileft; iframe Hse; ipureintro; exact Herr
  · imodintro; iexists kvStateOf C0; iframe HQ0
    unfold watchStateRespOk; iright; ileft; ipureintro; exact Hne
  · -- at the cursor: the watch's start, or a state the update fired at before (`posQ`)
    obtain ⟨hv, hpn, hc0, hcl, hc', -⟩ := Hp
    iunfold posQ at Hpos
    icases Hpos with (%Hst | ⟨%σ', #HQ', %Hσ'⟩)
    · imodintro; iexists kvStateOf C0; iframe HQ0
      unfold watchStateRespOk; iright; iright; ileft; ipureintro
      exact ⟨hv, hpn, hc0, hcl, hc', Or.inl ⟨Hle, Hst⟩⟩
    · imodintro; iexists σ'; iframe HQ'
      unfold watchStateRespOk; iright; iright; ileft; ipureintro
      obtain ⟨-, hle', hok'⟩ := Hσ'
      have hn' : sint.nat r.hdrRev = sint.nat c := by simp only [hn]; omega
      refine ⟨hv, hpn, hc0, hcl, hc', Or.inr ⟨by omega, ?_, by rw [hn']; exact hok'⟩⟩
      unfold KVState.rangeEvents; rw [hn']; simp
  · imod srvKVCoreM_fire on E γr γ hst hlog L Q $$ Hinvs H0 [HL] [HL] Hau with ⟨%C, #HQ, %HLC⟩
    · iapply mvcc.evLog_sealed $$ HL
    · iapply mvcc.evLog_certOk $$ HL
    ihave #HLs := mvcc.evLog_sealed _ _ $$ HL
    ihave %Hlk := sealed_logOk _ _ hrb $$ HLs
    ihave #HLc := mvcc.evLog_certOk _ _ $$ HL
    imod srvKVCoreM_keys on E γr [[], []] L (by decide) (mvcc.LogKeysLe.empties _)
      $$ Hinvs H0 HLs HLc with %Hk
    imodintro; iexists kvStateOf C; iframe HQ
    unfold watchStateRespOk; iright; iright; ileft; ipureintro
    obtain ⟨hv, hpn, hc0, hcl, hc', -⟩ := Hp
    obtain ⟨hpl, hnone⟩ := HLp
    have hCl := HLC.length_le
    refine ⟨hv, hpn, hc0, hcl, hc', Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [kvStateOf_rev]; omega
    · rw [rangeEvents_kvStateOf C o _ _ (by omega) (by simp only [hn]; omega),
        ← rangeLogEvents_prefix HLC o (by simp only [hn]; omega)]
      exact hnone
    · exact kvLogOkTo_of_prefix HLC Hlk.1 Hlk.2.2 Hlk.2.1 (by simp only [hn]; omega) Hk
  · imod srvKVCoreM_fire on E γr γ hst hlog L Q $$ Hinvs H0 [HL] [HL] Hau with ⟨%C, #HQ, %HLC⟩
    · iapply mvcc.evLog_sealed $$ HL
    · iapply mvcc.evLog_certOk $$ HL
    obtain ⟨hv, hne, hc0, hcc, hlast⟩ := Hev
    obtain ⟨hcl, hkl, hre⟩ := HLe
    have hCl := HLC.length_le
    have hevs : (kvStateOf C).rangeEvents o (sint.nat c + 1) (sint.nat c' + 1) =
        rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1) := by
      rw [rangeEvents_kvStateOf C o _ _ (by omega) (by simp only [hn]; omega),
        ← rangeLogEvents_prefix HLC o (by simp only [hn]; omega)]
    ihave #HLs := mvcc.evLog_sealed _ _ $$ HL
    ihave %Hlk := sealed_logOk _ _ hrb $$ HLs
    ihave #HLc := mvcc.evLog_certOk _ _ $$ HL
    imod srvKVCoreM_keys on E γr [[], []] L (by decide) (mvcc.LogKeysLe.empties _)
      $$ Hinvs H0 HLs HLc with %Hk
    imodintro; iexists kvStateOf C; iframe HQ
    unfold watchStateRespOk; iright; iright; iright
    isplitr
    · ipureintro
      refine ⟨hv, hne, hc0, hcc, ?_, hlast,
        kvLogOkTo_of_prefix HLC Hlk.1 Hlk.2.2 Hlk.2.1 (by simp only [hn]; omega) Hk⟩
      rw [kvStateOf_rev]; omega
    rw [hevs, hre]
    iapply eventsIs_of_fixed _ kvs hkl $$ Hkv

end convert

end EtcdGrove
end Perennial
