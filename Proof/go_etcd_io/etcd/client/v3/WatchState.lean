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
public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The events of the state (pure) -/

section pure
variable [ext : FfiSyntax]

/-- **Revision `r`'s events in the state `σ`**: one per change of the revision, in order, each the
key-value the change wrote at `r` (a put's, from the store before the revision and the changes up
to it) or the deleted key with `ModRevision = r` (`mvcc.evsOfRevM`, as
`watchableStoreTxnWrite.End` and `kvsToEvents` make them). -/
def KVState.revEvents (σ : KVState) (r : Nat) : List mvcc.EvM :=
  mvcc.evsOfRevM r (σ.at (r - 1)).kvs (σ.changesAt r)

/-- **The events of the revisions `[lo, hi)` in the range of `o`**, in revision order (etcd's
`rangeEvents` over the key bucket, filtered by the watcher's range). -/
def KVState.rangeEvents (σ : KVState) (o : OpFull) (lo hi : Nat) : List mvcc.EvM :=
  (((List.range' lo (hi - lo)).map σ.revEvents).flatten).filter
    fun ev => inRange o.key o.base.rangeEnd ev.kv.key

/-- At a log's state, a later revision's events are the log's (mvcc's watch events of it). -/
theorem revEvents_kvStateOf (l : mvcc.Log) (r : Nat) (h0 : 0 < r) (hr : r ≤ l.length - 1) :
    (kvStateOf l).revEvents r = mvcc.evsOfRevM r (mvcc.stateAt l (r - 1)) (l.getD r []) := by
  unfold KVState.revEvents
  rw [kvStateOf_at_kvs l (r - 1) (by omega), kvStateOf_changesAt l r h0]

/-- **At a log's state, the range's events are mvcc's watch events of the log** (its revisions
from `lo ≥ 1` below `hi ≤ l.length`), filtered by the range: what the server sends. -/
theorem rangeEvents_kvStateOf (l : mvcc.Log) (o : OpFull) (lo hi : Nat) (h0 : 0 < lo)
    (hh : hi ≤ l.length) :
    (kvStateOf l).rangeEvents o lo hi =
      (mvcc.logEvents l lo hi).filter fun ev => inRange o.key o.base.rangeEnd ev.kv.key := by
  unfold KVState.rangeEvents mvcc.logEvents
  congr 2
  apply List.map_congr_left
  intro m hm
  rw [List.mem_range'] at hm
  rw [revEvents_kvStateOf l m (by omega) (by omega)]

end pure

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

/-! ## A response of a watch, as a read of the state -/

section resp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A delivered event is the state's event `ev`** (persistent): its type (`PUT` `0`, `DELETE`
`1`), key and revision, and its `*KeyValue`'s fields `ev`'s (a delete's the key and `ModRevision`
alone, the others empty, as etcd sends them). -/
def eventIs (e : EvModel) (ev : mvcc.EvM) : IProp GF :=
  iprop(⌜e.typ = (if ev.del then W32 1 else W32 0) ∧ e.key = ev.kv.key ∧ e.rev = ev.kv.modRev⌝ ∗
    kvValAt e.kv ev.kv)

instance eventIs_persistent (e : EvModel) (ev : mvcc.EvM) : Persistent (eventIs (GF := GF) e ev) := by
  unfold eventIs; infer_instance

/-- **The delivered events are the state's events `evs`**, one by one. -/
def eventsIs (es : List EvModel) (evs : List mvcc.EvM) : IProp GF :=
  iprop(⌜es.length = evs.length⌝ ∗
    □ ∀ (i : Nat) (e : EvModel) (ev : mvcc.EvM), ⌜es[i]? = some e⌝ -∗ ⌜evs[i]? = some ev⌝ -∗
      eventIs e ev)

instance eventsIs_persistent (es : List EvModel) (evs : List mvcc.EvM) :
    Persistent (eventsIs (GF := GF) es evs) := by
  unfold eventsIs; infer_instance

/-- **A watch's response `v` (modelled by `r`) as a read of the state `σ`**, received when the
stream is at revision `c` and leaving it at `c'` (see the file header): an error, with a close
error grpc's `status` accepts; a response without events that is not a progress notification; a
progress notification at `p ≤ σ.rev` after which nothing in the range changed up to `p`; or events,
exactly the range's events of `σ` from `c + 1` to `c' ≤ σ.rev`, the last at `c'`. -/
def watchStateRespOk (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) : IProp GF :=
  iprop((⌜watchErr v ∧ c' = c⌝ ∗ statusErrOk v.closeErr') ∨
    ⌜¬ watchErr v ∧ r.events = [] ∧ r.isProgressNotify = false ∧ c' = c⌝ ∨
    ⌜¬ watchErr v ∧ r.isProgressNotify = true ∧ 0 ≤ sint.Z r.hdrRev ∧
      sint.Z r.hdrRev ≤ (σ.rev : Int) ∧
      (sint.Z c < sint.Z r.hdrRev → c' = r.hdrRev ∧
        σ.rangeEvents o (sint.nat c + 1) (sint.nat r.hdrRev + 1) = []) ∧
      (sint.Z r.hdrRev ≤ sint.Z c → c' = c)⌝ ∨
    (⌜¬ watchErr v ∧ r.events ≠ [] ∧ 0 ≤ sint.Z c ∧ sint.Z c < sint.Z c' ∧
        sint.Z c' ≤ (σ.rev : Int) ∧
        (r.events.getLast?.map EvModel.rev) = some c'⌝ ∗
      eventsIs r.events (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))))

instance watchStateRespOk_persistent (o : OpFull) (σ : KVState) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (watchStateRespOk (GF := GF) o σ c c' v r) := by
  unfold watchStateRespOk; infer_instance

/-- **The `i`-th response `v` of a watch of `o` with the read update's `Q`**: modelled by some `r`
(`respAt`: its events, header and flags), the update's `□ Q σ` at the state `σ` it fired at, and
`watchStateRespOk` at the positions `i` and `i + 1` of the watch's cursor. -/
def watchStateElem (γw : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF) (i : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (σ : KVState) (c c' : w64), respAt v r ∗ □ Q σ ∗
    monoListIdxOwn γw.cur i.toNat c ∗ monoListIdxOwn γw.cur (i.toNat + 1) c' ∗
    watchStateRespOk o σ c c' v r)

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
