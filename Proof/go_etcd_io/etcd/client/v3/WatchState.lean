/-
**A watch as repeated reads of etcd's KV state** (D46, 2026-10-25; a candidate, for audit before the
watch proofs are ported to it). Lean-first (no Rocq counterpart).

The client's KV specs (`kv.Get`, `kv.Put`, ..., `KVService.lean`) are stated over etcd's KV state
`σ` (`etcdKV γ σ`, `KVState`: the store at the compaction revision and each later revision's
changes, in order). A watch is about the same state: the caller gives a persistent read update of
`σ` (as a linearizable `Get` does), and each response the watch delivers is one firing of it, at a
state `σ` at least as recent as everything the response reports (`□ Q σ`). What the response
reports is computed from `σ` as etcd computes it from its key bucket:

* `KVState.revEvents σ r`: revision `r`'s events, one per change in order, as
  `watchableStoreTxnWrite.End`/`kvsToEvents` make them (`mvcc.evsOfRevM`: a put's event carries
  the key-value the put wrote, a delete's the key with `ModRevision = r`);
* `KVState.rangeEvents σ o lo hi`: the events of the revisions `[lo, hi)` whose key is in the
  watched range, in revision order (`rangeEvents`/`kvsToEvents`' filter; `mvcc.watchEvents`);
* `watchStateRespOk o σ c c' v r`: a response `v` (modelled by `r`), received when the stream is
  at revision `c` and leaving it at `c'`, is an error (position kept), a response without events
  that is not a progress notification (position kept), a progress notification at `p ≤ σ.rev`
  (no event in `(c, p]`; position `max c p`), or events: exactly `rangeEvents σ o (c + 1) (c' + 1)`
  for some `c < c' ≤ σ.rev` (`eventsIs`: each event's type, key, revision and key-value).

`rangeEvents_kvStateOf` ties the events to the server's: at a log's state they are mvcc's watch
events of the log (`mvcc.logEvents`, filtered by the range), so the server's watch proof
(`dispatch_content`) can discharge the contract from the events it sends.

**The candidate triple** (`watcher.Watch.specσ`): a prefix watch (a non-empty key not all `0xff`,
as the current completeness promise, `cplCond`) from a revision `rev ≥ 1`, with the caller's
persistent read update of `γ`'s state, returns an SPSC channel whose `i`-th response satisfies
`watchStateElem`: the update's `□ Q σ` at some state `σ` and `watchStateRespOk` at the positions
`i` and `i + 1` of the watch's cursor (`γw.cur`, from `rev - 1`).

Not yet decided (for the port): `isKvWatcher w γ` here is the client watcher at an environment whose
server runs the KV at `γ`'s state variable, over one member (`isClientWatcher`'s `V.R`); the
multi-member form mirrors `isKv` (D43). `srvNoDupKeys` and `startOk` are not premises: the events
are `σ`'s, whatever a revision's changes are, and the events between the cursor and the reply's
revision are defined whatever the start was.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## Firing the caller's read update at a watched log -/

section fire
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

open Iris.ProofMode in
/-- **A read update fired at a certified log** (`kv_cert_floor`'s, with the state): with the
server's KV invariants, the start log sealed (`NewStore`'s `[[], []]`, the KV's start log), and a
sealed log `L` the server certified, the caller's persistent read update of `γ`'s state (the KV
invariant's state variable) fires at the committed state, the state of a log `C` that `L` is a
prefix of: `L` is the model of a committed raft prefix (`kv_cert_read`, `srvRLog_lb`) or has at
most two revisions (then a prefix of the start log, the sealed logs being in prefix order). -/
theorem watch_fire (E : apply.AEnv GF) (γr : ReadNames) (γ : KVNames) (hst : γ.st = γr.kv.st)
    (hlog : γr.kv.log0 = [[], []]) (L : mvcc.Log) (Q : KVState → IProp GF) :
    ⊢ srvKVInvs E γr -∗ mvcc.idxSealed E.γ.idx [[], []] -∗ mvcc.idxSealed E.γ.idx L -∗
      mvcc.certOk E.γ L -∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) ={⊤}=∗
      ∃ C : mvcc.Log, □ Q (kvStateOf C) ∗ ⌜L <+: C⌝ := by
  have Hsub : ((⊤ \ ↑srvRaftN) \ ↑kvN : CoPset) ⊆ ⊤ \ ↑kvN := by
    intro p hp
    rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff] at hp
    rw [Iris.Std.LawfulSet.mem_diff]
    exact ⟨CoPset.mem_full, hp.2⟩
  iintro #Hinvs #H0 #HL #Hc #Hau
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, %Hcok⟩
  imod kv_cert_read γr.raft γr.kv E.γ Hcok ⊤ (fun _ _ => CoPset.mem_full) L $$ HcI Hc with Hcase
  ihave %Hp0 := mvcc.idxSealed_prefix E.γ.idx [[], []] L $$ [H0 HL]
  · iframe H0 HL
  iunfold kvInv at HkI
  iinv HkI with >Hi Hclose
  icases Hi with ⟨%Lf, HLf, Hσ', %Hok', #Hw⟩
  -- `L` is a prefix of the committed log's model
  ihave Hp : iprop(|={⊤ \ ↑kvN}=> srvRLog γr.raft Lf ∗ ⌜L <+: kvModel γr.kv Lf⌝) $$ [HLf Hcase]
  · icases Hcase with (%hl | ⟨%A, #HA, %hA⟩)
    · imodintro
      iframe HLf
      ipureintro
      have hb : [[], []] <+: kvModel γr.kv Lf := by
        have := kvRaftOf_extends γr.kv.c0 γr.kv.ch0 γr.kv.log0 Lf
        unfold kvModel; rw [← hlog]; exact this
      rcases Hp0 with h | h
      · have hl2 : ([[], []] : mvcc.Log).length = L.length := by
          have := h.length_le; simp at this ⊢; omega
        rw [← h.eq_of_length hl2]; exact hb
      · exact h.trans hb
    · imod srvRLog_lb γr.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
        Lf A $$ HrI HLf HA with ⟨HLf, -, %Hp⟩
      imodintro
      iframe HLf
      ipureintro
      rw [← hA]
      unfold kvModel
      exact kvRaftOf_prefix _ _ _ A Lf Hp
  imod Hp with ⟨HLf, %HpL⟩
  -- the update, fired at the committed state
  imod (fupd_mask_subseteq Hsub) with Hback
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%σ, Hc', Hucl⟩
  iunfold etcdKV at Hc'
  ihave Hc2 : ghostVar (GF := GF) γr.kv.st (1 : Qp).half σ $$ [Hc']
  · rw [← hst]; iexact Hc'
  ihave %Hag := ghostVar_agree γr.kv.st _ _ _ _ $$ Hσ' Hc2
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [Hc2] with #HQ0
  · iunfold etcdKV; rw [hst]; iexact Hc2
  imod Hback with -
  imod Hclose $$ [HLf Hσ'] with -
  · inext; iexists Lf; iframe HLf Hσ' Hw; ipureintro; exact Hok'
  imodintro
  iexists kvModel γr.kv Lf
  rw [Hag]
  iframe HQ0
  ipureintro; exact HpL

end fire

/-! ## A response at the server's level, as a read of the state -/

section convert
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- **A response at the server's level is a read of the state** (see the file header): the caller's
read update fires (`watch_fire`) at the watched log the response's facts are of (the start log if
none), at a state `σ` whose events are that log's, so the response's are `σ`'s. -/
theorem raw_to_state (E : apply.AEnv GF) (γr : ReadNames) (γ : KVNames) (hst : γ.st = γr.kv.st)
    (hlog : γr.kv.log0 = [[], []]) (o : OpFull) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (Q : KVState → IProp GF) :
    ⊢ srvKVInvs E γr -∗ mvcc.idxSealed E.γ.idx [[], []] -∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) -∗
      client.rawRespOk E.γ o c c' v r ={⊤}=∗
      ∃ σ : KVState, □ Q σ ∗ watchStateRespOk o σ c c' v r := by
  have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
  iintro #Hinvs #H0 #Hau #Hraw
  -- the update fired at the start log (a certified log of two revisions)
  imod watch_fire E γr γ hst hlog [[], []] Q $$ Hinvs H0 H0 [] Hau with ⟨%C0, #HQ0, -⟩
  · unfold mvcc.certOk; ileft; ipureintro; simp
  unfold client.rawRespOk
  icases Hraw with (⟨%Herr, #Hse⟩ | %Hne | ⟨%Hp, (⟨%Hlt, %L, #HL, %HLp⟩ | %Hle)⟩ |
    ⟨%Hev, %L, %kvs, #HL, %HLe, #Hkv⟩)
  · imodintro; iexists kvStateOf C0; iframe HQ0
    unfold watchStateRespOk; ileft; iframe Hse; ipureintro; exact Herr
  · imodintro; iexists kvStateOf C0; iframe HQ0
    unfold watchStateRespOk; iright; ileft; ipureintro; exact Hne
  · imod watch_fire E γr γ hst hlog L Q $$ Hinvs H0 [HL] [HL] Hau with ⟨%C, #HQ, %HLC⟩
    · iapply mvcc.evLog_sealed $$ HL
    · iapply mvcc.evLog_certOk $$ HL
    imodintro; iexists kvStateOf C; iframe HQ
    unfold watchStateRespOk; iright; iright; ileft; ipureintro
    obtain ⟨hv, hpn, hp0, -⟩ := Hp
    obtain ⟨hcp, hc', hc0⟩ := Hlt
    obtain ⟨hpl, hnone⟩ := HLp
    have hCl := HLC.length_le
    refine ⟨hv, hpn, hp0, fun _ => ⟨hc', ?_, ?_⟩, fun h => absurd h (by omega)⟩
    · rw [kvStateOf_rev]; omega
    · rw [rangeEvents_kvStateOf C o _ _ (by omega) (by simp only [hn]; omega),
        ← rangeLogEvents_prefix HLC o (by simp only [hn]; omega)]
      exact hnone
  · imodintro; iexists kvStateOf C0; iframe HQ0
    unfold watchStateRespOk; iright; iright; ileft; ipureintro
    obtain ⟨hv, hpn, hp0, -⟩ := Hp
    exact ⟨hv, hpn, hp0, fun h => absurd h (by omega), fun _ => Hle.2⟩
  · imod watch_fire E γr γ hst hlog L Q $$ Hinvs H0 [HL] [HL] Hau with ⟨%C, #HQ, %HLC⟩
    · iapply mvcc.evLog_sealed $$ HL
    · iapply mvcc.evLog_certOk $$ HL
    obtain ⟨hv, hne, hc0, hcc, hlast⟩ := Hev
    obtain ⟨hcl, hkl, hre⟩ := HLe
    have hCl := HLC.length_le
    have hevs : (kvStateOf C).rangeEvents o (sint.nat c + 1) (sint.nat c' + 1) =
        rangeLogEvents L o (sint.nat c + 1) (sint.nat c' + 1) := by
      rw [rangeEvents_kvStateOf C o _ _ (by omega) (by simp only [hn]; omega),
        ← rangeLogEvents_prefix HLC o (by simp only [hn]; omega)]
    imodintro; iexists kvStateOf C; iframe HQ
    unfold watchStateRespOk; iright; iright; iright
    isplitr
    · ipureintro
      refine ⟨hv, hne, hc0, hcc, ?_, hlast⟩
      rw [kvStateOf_rev]; omega
    rw [hevs, hre]
    iapply eventsIs_of_fixed _ kvs hkl $$ Hkv

end convert

/-! ## A client watcher of etcd's KV -/

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A client watcher of etcd's KV `γ`** (persistent; see the file header: one member, its watch
server's apply environment running the KV at `γ`'s state variable). -/
def isKvWatcher (w : Loc) (γ : KVNames) : IProp GF :=
  iprop(∃ (V : client.WEnv GF) (γr : ReadNames), client.isClientWatcher V w ∗
    srvKVInvs V.R.E γr ∗ ⌜γr.kv.st = γ.st⌝)

instance isKvWatcher_persistent (w : Loc) (γ : KVNames) : Persistent (isKvWatcher (GF := GF) w γ) := by
  unfold isKvWatcher; infer_instance

end resp

/-! ## The candidate triple -/

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.Watch(ctx, key, opts...)`, as repeated reads of etcd's KV `γ`** (the candidate; see the
file header): a prefix watch (`opts` the models of the Go options, `optsAt` tying the slice `opts_sl`
to them) of a non-empty key not all `0xff`, from a revision `rev ≥ 1`, with the caller's persistent
read update of `γ`'s state, returns a channel whose responses are reads of the state
(`watchStateElem`), with the consumer's side and the cursor at `rev - 1`. -/
abbrev watcher.Watch.specσ : Prop :=
  ∀ (w : Loc) (γ : KVNames) (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF))
    (key : GoString) (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (rev : w64)
    (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isKvWatcher w γ ∗
      context.isContext ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜(opWatchModel key opts).isRangeWatch rev = true ∧ ¬ opWatchPanics key opts ∧
        1 ≤ sint.Z rev ∧ (opWatchModel key opts).key ≠ [] ∧
        (opWatchModel key opts).base.rangeEnd = prefixRangeEnd (opWatchModel key opts).key ∧
        prefixRangeEnd (opWatchModel key opts).key ≠ [W8 0]⌝ ∗
      □ (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>) }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
        go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
      isSpsc γw.spsc ch (watchStateElem γw (opWatchModel key opts) Q) (fun _ => iprop(True)) ∗
      spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γw.cur 0 (rev - W64 1) }}

end spec

end EtcdGrove
end Perennial
