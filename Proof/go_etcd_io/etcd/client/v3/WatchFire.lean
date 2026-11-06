/-
**A watch's read update, fired** (D47, 2026-10-26). Lean-first (no Rocq counterpart).

* (G2's follow-up, 2026-10-30) the firing itself is the server's law `srvKVCoreM_fire` (until then
  `watch_fire` here, auth off only): with the server's KV core in either auth mode, the caller's
  persistent read update of the KV state fires at the committed state, whose log extends a
  witnessed log `L` (strict M1: `srvKVFacts_fire`, at a member's certified lower bound `histLb`,
  which extends to a witnessed one by `srvKVFacts`' tie; `srvKVFacts_fire0`, at some witnessed
  log, in place of the start log's seal).
* `raw_to_state`: a response at the server's level (`client.rawRespOk`: its events a watched
  log's) is a read of the state (`watchStateRespOk`): the update fires at the watched log (some
  witnessed log if none), and the state's events are the log's (`rangeEvents_kvStateOf`,
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

/-- **The server's KV core in a mode has its witness at the mode's model** (`E.Nx` is
`srvApi.kvNx γr on`: `kvNxOff`/`kvNxOn` at the start auth state, by definition). -/
theorem srvKVCoreM_Nx (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVCoreM on E γr ⊢ ⌜E.Nx = srvApi.kvNx γr on⌝ := by
  cases on
  · rw [srvKVCoreM_false]
    iintro #H
    iunfold srvKVInvs at H
    icases H with ⟨-, -, -, -, -, %h⟩
    ipureintro; rw [h]; rfl
  · rw [srvKVCoreM_true]
    iintro #H
    icases H with ⟨-, -, -, -, -, %h⟩
    ipureintro; rw [h]; rfl

/-- **Some log has the server's witness** (the KV model of a committed raft log the KV
certificates' invariant holds), at which a read update can fire (in place of mvcc's start-log
seal `idxSealed [[], []]`). -/
theorem srvKVCoreM_someNx (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVCoreM on E γr ⊢ |={⊤}=> ∃ L : mvcc.Log, E.Nx L := by
  iintro #H
  ihave %HNx := srvKVCoreM_Nx on E γr $$ H
  rw [HNx]
  cases on
  · rw [srvKVCoreM_false]
    iunfold srvKVInvs at H
    icases H with ⟨-, #Hci, -⟩
    iunfold kvCertInv at Hci
    imod inv_acc (E := ⊤) (show ↑kvcN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hci
      with ⟨Hi, Hclose⟩
    icases Hi with ⟨%C, %hi, %Lb, >HC, >Hhi', >#HLb, >%Hok⟩
    imod Hclose $$ [HC Hhi'] with -
    · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
    imodintro
    iexists kvModelM false γr.kv Lb
    iunfold srvApi.kvNx
    iexists Lb
    iframe HLb
    ipureintro; rfl
  · rw [srvKVCoreM_true]
    icases H with ⟨-, #Hci, -⟩
    iunfold kvCertInvOn at Hci
    imod inv_acc (E := ⊤) (show ↑kvcN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hci
      with ⟨Hi, Hclose⟩
    icases Hi with ⟨%C, %hi, %Lb, >HC, >Hhi', >#HLb, >%Hok⟩
    imod Hclose $$ [HC Hhi'] with -
    · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
    imodintro
    iexists kvModelM true γr.kv Lb
    iunfold srvApi.kvNx
    iexists Lb
    iframe HLb
    ipureintro; rfl

/-- **A member's read update fires at a watched log** (strict M1, `srvKVFacts`' ties): the
member's certified lower bound `L` extends to a witnessed log (`srvApi.histLb`'s), at which the
caller's update fires (`srvKVCoreM_fire`), at the state of a log `C` extending `L`. -/
theorem srvKVFacts_fire (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst) (L : mvcc.Log)
    (Q : KVState → IProp GF) :
    client.srvKVFacts V ∗ □ V.W.histLb L ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) ⊢
      |={⊤}=> ∃ C : mvcc.Log, □ Q (kvStateOf C) ∗ ⌜L <+: C⌝ := by
  iintro ⟨#Hk, #HL, #Hau⟩
  iunfold client.srvKVFacts at Hk
  icases Hk with ⟨%on, %γr, #Hc, %Hp, -, %Ht⟩
  ihave %HNx := srvKVCoreM_Nx on V.R.E γr $$ Hc
  irevert HL
  rw [Ht.1]
  iintro #HL
  iunfold srvApi.histLb at HL
  icases HL with ⟨-, %L', %HL', #Hx, -⟩
  ihave Hx' : V.R.E.Nx L' $$ []
  · rw [HNx]; iexact Hx
  imod srvKVCoreM_fire on V.R.E γr γ (by rw [hst, Hp.1]) L' Q $$ Hc Hx' Hau with ⟨%C, #HQ, %HC⟩
  imodintro
  iexists C
  iframe HQ
  ipureintro; exact HL'.1.trans HC

/-- **A member's read update fires** (at some witnessed log). -/
theorem srvKVFacts_fire0 (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst)
    (Q : KVState → IProp GF) :
    client.srvKVFacts V ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) ⊢
      |={⊤}=> ∃ C : mvcc.Log, □ Q (kvStateOf C) := by
  iintro ⟨#Hk, #Hau⟩
  ihave #Hk' := Hk
  iunfold client.srvKVFacts at Hk'
  icases Hk' with ⟨%on, %γr, #Hc, %Hp, -, -⟩
  imod srvKVCoreM_someNx on V.R.E γr $$ Hc with ⟨%L, Hx⟩
  imod srvKVCoreM_fire on V.R.E γr γ (by rw [hst, Hp.1]) L Q $$ Hc Hx Hau with ⟨%C, #HQ, -⟩
  imodintro
  iexists C
  iexact HQ

/-- **A response at the server's level is a read of the state** (see the file header): the caller's
read update fires (`srvKVFacts_fire`, in the member's auth mode) at the watched log the response's
facts are of (at some witnessed log if none), at a state `σ` whose events are that log's, so the
response's are `σ`'s; `σ` is well formed through the position the response moves to (the watched
log's state's prefix, `kvLogOkTo_of_prefix`, its model facts `srvWLaws`'). Strict M1: at the
member's watch facts `V.W` (the server's `histLb`, `srvKVFacts`' tie), in place of mvcc's sealed
`evLog` and the start log's seal. -/
theorem raw_to_state (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst) (o : OpFull)
    (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (Q : KVState → IProp GF) :
    ⊢ client.srvKVFacts V -∗ client.srvWLaws V.W -∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) -∗
      posQ o Q c -∗ client.rawRespOk V.W o c c' v r ={⊤}=∗
      ∃ σ : KVState, □ Q σ ∗ watchStateRespOk o σ c c' v r := by
  have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
  iintro #Hk #Hl #Hau #Hpos #Hraw
  -- the update fired at some witnessed log
  imod srvKVFacts_fire0 V γ hst Q $$ [Hk Hau] with ⟨%C0, #HQ0⟩
  · iframe #
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
  · imod srvKVFacts_fire V γ hst L Q $$ [Hk HL Hau] with ⟨%C, #HQ, %HLC⟩
    · iframe #
    ihave %Hlk := client.srvWLaws_model V.W L $$ [$Hl $HL]
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
    · exact kvLogOkTo_of_prefix HLC Hlk.1 Hlk.2.2.1 Hlk.2.1 (by simp only [hn]; omega) Hlk.2.2.2
  · imod srvKVFacts_fire V γ hst L Q $$ [Hk HL Hau] with ⟨%C, #HQ, %HLC⟩
    · iframe #
    obtain ⟨hv, hne, hc0, hcc, hlast⟩ := Hev
    obtain ⟨hcl, hkl, hre⟩ := HLe
    have hCl := HLC.length_le
    have hevs : (kvStateOf C).rangeEvents o (sint.nat c + 1) (sint.nat c' + 1) =
        rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1) := by
      rw [rangeEvents_kvStateOf C o _ _ (by omega) (by simp only [hn]; omega),
        ← rangeLogEvents_prefix HLC o (by simp only [hn]; omega)]
    ihave %Hlk := client.srvWLaws_model V.W L $$ [$Hl $HL]
    imodintro; iexists kvStateOf C; iframe HQ
    unfold watchStateRespOk; iright; iright; iright
    isplitr
    · ipureintro
      refine ⟨hv, hne, hc0, hcc, ?_, hlast,
        kvLogOkTo_of_prefix HLC Hlk.1 Hlk.2.2.1 Hlk.2.1 (by simp only [hn]; omega) Hlk.2.2.2⟩
      rw [kvStateOf_rev]; omega
    rw [hevs, hre]
    iapply eventsIs_of_fixed _ kvs hkl $$ Hkv

end convert

end EtcdGrove
end Perennial
