/-
The results of etcd's gRPC KV service (`server/v3/etcdserver/api/v3rpc`: the handlers of
`key.go`, the request checks, the response header, `togRPCError`), restated at top level, with
the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart); plan: `notes/decisions.md`, "The request path".

Unit 1 (2026-10-12): every function of `key.go` but `kvServer.RangeStream` and
`kvServer.Compact`, of `header.go` and `util.go`'s `togRPCError` specified and proved
(`Link.lean`). The results:
* **`check_gives_nodup`** (`CheckNodup.lean`; `intervalsOkCheckStmt_holds`): a branch passing
  `checkRequestOp` (non-empty keys) and `checkIntervals` with no from-key delete and no nested put a later sibling deletes, run by the server, writes each key at most
  once; with the txn package's `keys_nodup_iff_check`, `checkIntervals_nodup` below: the changes'
  keys are distinct (`NoDupKeysPerRev`'s per-transaction part). The two exclusions are the
  code's findings (`issues/etcd-txn-delete-then-ignore-put.md`,
  `issues/etcd-txn-check-intervals-sibling.md`).
* **`checkRequestOp_nonempty`**: a transaction passing `checkTxnRequest` has no empty
  operation at any depth (the txn package's `etcd-txn-empty-requestop` precondition discharged at
  the API).
* **`checkTxnRequest_ok`**: `checkTxnRequest` purely.
* **`put_handler`**: `kvServer.Put`'s answer is the server's `Put` answer (`A.ok`, units 2/3's)
  with the header filled, or the check's error, or the server's error through `togRPCError`; the
  same for `Range`, `DeleteRange` and `Txn` (`range_handler`, `deleteRange_handler`,
  `txn_handler`).

Unit 3a (2026-10-12): the server's contract discharged for `Put` and `DeleteRange`
(`ServerKV.lean`: `srvKVAns`; since stage 4 `ServerKVOn.lean`'s `raftKV_of_serverM`, from the linked
`EtcdServer.Put`/`DeleteRange`):
* **`put_end_to_end`**, **`deleteRange_end_to_end`**: the gRPC handler's `(resp, nil)` is the
  apply thread's application of the request at the log the entry met (`putAppliedOk`/
  `deleteAppliedOk`: `applyStep … (.dispatched (.applied l false) skip)`, the outcome's answer,
  `kvLogLb` and the witness `E.Nx` of the log after) with the header filled (`hdrFilled`, `hdrRevOut`); an error is the
  apply's or the proposal's (`putErrOk`/`deleteErrOk`). Premises: `isServerReq` (the raft contract,
  the wait registry, the ids, the auth store's request side), the `*kvServer` (`kvServerAt`), and
  the read side's conjuncts of `raftKV` (unit 3b's).
* **`put_end_to_end_model`**, **`deleteRange_end_to_end_model`** (pure): through the
  uber-applier's chain, such a put appends the client's put change to the log (a delete commits
  its changes), no alarm raised.

**The replies' size** (2026-10-31, `notes/reply-size.md`): the served results here that take a
server token (`grpcServerAt`: the auth service served) are conditional, through it, on the workload
premise `grpcRepliesFit`, which the single-process start (`grpc.start'`), the token's only producer,
takes; their statements do not show it. (Since phase 7's switch, SW1, the watch stream is registered
by the start itself, from `etcd_watch_served`'s run contract.)
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeAuth
public import Proof.go_etcd_io.etcd.client.v3.GrpcTys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.PerTypeWatch
public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientPortTable
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckNodup
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunAdapt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRevoke

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI

/-- **`checkIntervals` gives distinct keys** (see `check_gives_nodup`): a branch `ops` passing
`checkRequestOp` and `checkIntervals`, with no from-key delete and no nested put a later sibling deletes, run by the
server whose deletes are of present keys (`DelsPresent`, which a run gives), changes each key at
most once. -/
theorem checkIntervals_nodup (n : Int) (ops : List ReqOp) (tops : List TxnOp) (s0 s : List EtcdKv)
    (r : w64) (hops : ReqOp.toTxnOps ops = some tops) (hck : opsCheck n ops = none)
    (hfk : ReqOp.noFromKeyDelL ops)
    (hsib : ReqOp.siblingSafeL ops) (hiv : intervalsOk ops)
    (hdel : txn.DelsPresent r s (txn.srvOps s0 r s tops).1) :
    ((txn.srvOps s0 r s tops).1.map mvcc.Change.key).Nodup :=
  (txn.keys_nodup_iff_check _ s hdel).2 (check_gives_nodup n ops tops s0 s r hops hck hfk hsib hiv)

/-- **An empty operation is rejected** at any depth: a transaction passing `checkTxnRequest`
has the txn package's model (no empty `RequestOp`, the `etcd-txn-empty-requestop` precondition). -/
theorem checkRequestOp_nonempty {n : Int} {cs : List CmpModel} {ts es : List ReqOp}
    (h : txnReqOk n cs ts es) :
    ∃ ts' es', ReqOp.toTxnOps ts = some ts' ∧ ReqOp.toTxnOps es = some es' :=
  txnCheck_toTxnOps h

/-- **`checkTxnRequest`, purely**: passes iff the widest of the comparisons and branches is
within the budget, every comparison has a key, and every operation passes at the budget less
that width. -/
theorem checkTxnRequest_ok (n : Int) (cs : List CmpModel) (ts es : List ReqOp) :
    txnReqOk n cs ts es ↔
      (txnWidth cs ts es : Int) ≤ n ∧ (∀ c ∈ cs, c.key ≠ []) ∧
        (∀ u ∈ ts, requestOpOk (n - txnWidth cs ts es) u) ∧
        (∀ u ∈ es, requestOpOk (n - txnWidth cs ts es) u) :=
  txnCheck_ok_iff n cs ts es

section handlers
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`kvServer.Put`**: the server's `Put` answer with the header filled (`kvOut`), or the
check's error. -/
theorem put_handler : EtcdGrove.v3rpc.kvServer.Put.spec (GF := GF) (hG := hG) :=
  kvServer.wp_Put

theorem range_handler : EtcdGrove.v3rpc.kvServer.Range.spec (GF := GF) (hG := hG) :=
  kvServer.wp_Range

theorem deleteRange_handler : EtcdGrove.v3rpc.kvServer.DeleteRange.spec (GF := GF) (hG := hG) :=
  kvServer.wp_DeleteRange

end handlers

/-! ## End to end: the gRPC KV service through the server (units 3a and 3b)

Each handler's linked spec with the server's contract `raftKV` discharged
(`raftKV_of_serverM`, from the server's linked `EtcdServer.Put`/`DeleteRange`/`Range`/`Txn` and
the getters), at the server's parameters `srvKVAns s E ρ γr c`. Premises: the server's
request-path fields and invariants (`isServerReq`: the raft contract, the wait registry, the id
generator, the auth store's request side, ...), its read side's (`isServerRead`: the read
loop's contract, the bare store, the lessor and auth store's contracts, the store stays small),
and the handler's `*kvServer` (`kvServerAt`: what `NewKVServer(s)` built). A call needs the
request's context, one id credit, a reader slot of `s.leadTimeMu` (`srvCall`), and the read
call's resources (`srvRdCall`: the store's reader slots, the logger's, the committed index `c`
the caller knew of); every resource but a write's id credit comes back with any answer. The
answer: the check's error; or `(resp, nil)` with the response header filled with the cluster's
and member's ids (`hdrFilled`) and its revision kept (`hdrRevOut`: not `0`), and the server's
answer (`A.ok`): for a write, the apply thread's application of the request at the log the entry
met; for a read, the txn package's at a certified log, after the read index unless serializable;
or `nil` and an error (`A.err`: the apply's or the proposal's for a write). -/

section endToEnd
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-- **The server's contract in its auth mode, discharged** (`raftKV_of_serverM` at the linked
results; the auth component's stage 4). -/
theorem raftKV_serverM (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : v3rpc.KVDep GF) (na : Nat) (tok : Option GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ⌜E.authMode ≠ .any⌝ ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ⊢
      raftKV s (srvKVAnsM E.authOn s E ρ γr c F d na tok) :=
  raftKV_of_serverM EtcdServer.wp_Put EtcdServer.wp_DeleteRange EtcdServer.wp_Range
    EtcdServer.wp_Txn EtcdServer.wp_KV mvcc.api.mvccApi_shapes_law
    mvcc.api.mvccApi_persistent_law_holds mvcc.api.mvccApi_mvccState_reachable_law_holds
    EtcdServer.wp_Cluster
    membership.RaftCluster.wp_ID EtcdServer.wp_MemberID EtcdServer.wp_Term EtcdServer.wp_Leader
    s E ρ γr c F d na tok

/-- **The server's contract, discharged** (`raftKV_serverM` with auth off, then the bridge
`raftKV_srvKVAnsM_false`: the off server's answers are the merged ones with the gated rows dropped). -/
theorem raftKV_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : v3rpc.KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      raftKV s (srvKVAns s E ρ γr c F d) := by
  iintro ⟨#Hp, #Hq, #Hd⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hq
  have hM : E.authMode = .off := by
    unfold apply.AEnv.authOn at hon
    cases hM : E.authMode <;> simp_all [auth.AuthMode.isOn]
  ihave #Hlb := srvAuthLb_off s E ρ $$ Hq
  ihave #HM := raftKV_serverM s E ρ γr c F d 0 none $$ []
  · rw [hon, isServerReqM_false, isServerReadM_false]
    iframe #
    ipureintro; rw [hM]; simp
  rw [hon]
  iapply raftKV_srvKVAnsM_false $$ HM

/-- **`put_end_to_end`** (see the section header). -/
theorem put_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : v3rpc.KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ txn.putRequestIs r o ∗ kvDepOwn ρ γr d ∗
        ⌜kvDepPre d (.put o)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Put")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match putCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
              hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗ srvRdCall s E γr c ∗
              putAppliedOk s E ρ.rd F o (opDepQ d) resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ putErrOk s E ρ F o e) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #HF, #Hr, Hdep, %Hpre⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c F d $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Put p s (srvKVAns s E ρ γr c F d) cid mid n ctx r o) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0 Hdep HF; ipureintro; exact ⟨trivial, Hpre⟩
  inext
  iintro %resp %err ⟨Hpost, -⟩
  iapply HΦ
  cases hc : putCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- **`deleteRange_end_to_end`** (as `put_end_to_end`, for `DeleteRange`: the answer's request is
the one the proposed data decode to, `deleteAppliedOk`). -/
theorem deleteRange_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ txn.deleteRangeRequestIs r o ∗
        kvDepOwn ρ γr d ∗ ⌜kvDepPre d (.deleteRange o)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"DeleteRange")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match deleteCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ deleteAppliedOk s E ρ.rd F o (opDepQ d) resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ deleteErrOk s E ρ F o e) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #HF, #Hr, Hdep, %Hpre⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c F d $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_DeleteRange p s (srvKVAns s E ρ γr c F d) cid mid n ctx r o) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0 Hdep HF; ipureintro; exact ⟨trivial, Hpre⟩
  inext
  iintro %resp %err ⟨Hpost, -⟩
  iapply HΦ
  cases hc : deleteCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- **`range_end_to_end`**: the gRPC `Range`'s `(resp, nil)` is the txn package's range at a
certified log of at least two revisions (`rangeAnsOk`: `rangeResult` of the server's selection
at the revision read, the header's revision the log's last), read after the read index unless
serializable (`readLogOk γr c log`: the applied index reached the committed index `c` the caller
knew of, and `log` extends the log applied through an index at least `c`; unit 4b), the header
filled; the id credit and the reader slot back. -/
theorem range_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ txn.rangeRequestIs r o ∗
        kvDepOwn ρ γr d ∗ ⌜kvDepPre d (.range o)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Range")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match rangeCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
              rangeAnsOk E γr c F o resp rv (rangeDepQ γr.kv d)) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ _e : GoInterface,
            srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #HF, #Hr, Hdep, %Hpre⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c F d $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Range p s (srvKVAns s E ρ γr c F d) cid mid n ctx r o) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0 Hdep HF; ipureintro; exact ⟨trivial, Hpre⟩
  inext
  iintro %resp %err ⟨Hpost, -⟩
  iapply HΦ
  cases hc : rangeCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- **`txn_end_to_end`**: the gRPC `Txn`, for a request whose read-only gets are within
the txn package's model (`txnInModel`): the check's error, or `(resp, nil)` with the header
filled and, for the checked request's model `t`: if read-only, the server's run of `t` at a
certified log after the read index unless serializable (`txnReadAns`; the id credit back), else
the apply thread's application of the request the proposed data decode to (`txnAppliedAns`,
possibly with header-only ranges: `SkipRangeExecution`); or `nil` and an error (for a writing
`t`, `txnErrOk`: the apply's or the proposal's). -/
theorem txn_end_to_end
    (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (cs : List CmpModel)
    (ts es : List ReqOp) (F : mvcc.Log) (d : KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ txnReqIs r cs ts es ∗ txnReqWire r ts es ∗
        ⌜txnInModel cs ts es⌝ ∗ kvDepOwn ρ γr d ∗ ⌜kvDepPre d (.txn cs ts es)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Txn")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match txnAllCheck (sint.Z n) cs ts es with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
              ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
                if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗ txnReadAns E γr c F t (rangeDepQ γr.kv d) resp rv)
                else txnAppliedAns E ρ.rd F t (opDepQ d) resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
            ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
              if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #HF, #Hr, #Hw, %Hin, Hdep, %Hpre⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c F d $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Txn p s (srvKVAns s E ρ γr c F d) cid mid n
    ctx r cs ts es) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0 Hdep HF; ipureintro; exact ⟨Hin, Hpre⟩
  inext
  iintro %resp %err ⟨Hpost, -⟩
  iapply HΦ
  cases hc : txnAllCheck (sint.Z n) cs ts es with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- **`put_end_to_end` in the server's auth mode** (the auth component's stage 4; `srvKVAnsM` at the
caller's token): `put_end_to_end`'s, and with auth on the grant (`writeGrantOn`). Off it gives
`put_end_to_end`. Leases admitted with auth on at the
revocable lease mode (`kvDepPreML`; auth-lease S4 item 5). -/
theorem put_end_to_endML (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (cid mid n : w64) (ctx : GoInterface) (tok : Option GoString) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : v3rpc.KVDep GF) (na : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        ⌜E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
        kvServerAt p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode na ∗ txn.putRequestIs r o ∗ kvDepOwnM E.authOn s E ρ γr tok d ∗
        ⌜kvDepPreML E.authOn ρ.kv.lm d (.put o)⌝ ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Put")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (match putCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM E.authOn s E ρ γr tok d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
              hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗ srvRdCall s E γr c ∗
              putAppliedOk s E ρ.rd F o (opDepQ d) resp rv ∗
              (⌜E.authOn = true⌝ → writeGrantOn (srvTLSId s) E ρ tok (irrPut o))) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ putErrOk s E ρ F o e)) ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }} := by
  iintro %Φ ⟨#Pv, #Ps, %Hany, #Hsrv, #Hsrd, #Hlb, #Hat, Hc, Hc0, #HF, #Hna, #Hr, Hdep, %Hpre, #HtokC⟩ HΦ
  ihave #HKV := raftKV_serverM s E ρ γr c F d na tok $$ []
  · iframe #; ipureintro; exact Hany
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Put p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ctx r o) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAnsM]; iframe Hc Hc0 Hdep HF Hna HtokC; ipureintro
    first | exact ⟨trivial, Hpre⟩ | exact ⟨fun _ => rfl, trivial, Hpre⟩ | exact ⟨trivial, trivial, Hpre⟩ | exact ⟨fun _ => trivial, trivial, Hpre⟩
  inext
  iintro %resp %err ⟨Hpost, #HSe⟩
  iapply HΦ
  iframe HSe
  cases hc : putCheck o with
  | some e =>
    simp only [hc, srvKVAnsM]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -, -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAnsM]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- `put_end_to_endML`'s at a request of `kvDepPreM` (no lease, plain transactions). -/
theorem put_end_to_endM (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (cid mid n : w64) (ctx : GoInterface) (tok : Option GoString) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : v3rpc.KVDep GF) (na : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        ⌜E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
        kvServerAt p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode na ∗ txn.putRequestIs r o ∗ kvDepOwnM E.authOn s E ρ γr tok d ∗
        ⌜kvDepPreM E.authOn d (.put o)⌝ ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Put")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (match putCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM E.authOn s E ρ γr tok d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
              hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗ srvRdCall s E γr c ∗
              putAppliedOk s E ρ.rd F o (opDepQ d) resp rv ∗
              (⌜E.authOn = true⌝ → writeGrantOn (srvTLSId s) E ρ tok (irrPut o))) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ putErrOk s E ρ F o e)) ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }} := by
  iintro %Φ ⟨#Pv, #Ps, %Hany, #Hsrv, #Hsrd, #Hlb, #Hat, Hc, Hc0, #HF, #Hna, #Hr, Hdep, %Hpre, #HtokC⟩ HΦ
  iapply (put_end_to_endML p s E ρ γr c cid mid n ctx tok r o F d na) $$ [Hc Hc0 Hdep] HΦ
  iframe #
  iframe Hc Hc0 Hdep
  ipureintro; first | exact kvDepPreML_of_M _ _ _ _ Hpre | exact ⟨Hany, kvDepPreML_of_M _ _ _ _ Hpre⟩ | exact ⟨Hin, kvDepPreML_of_M _ _ _ _ Hpre⟩ | exact ⟨Hany, Hin, kvDepPreML_of_M _ _ _ _ Hpre⟩

/-- **`deleteRange_end_to_end` in the server's auth mode** (`put_end_to_endM`'s, for
`DeleteRange`). -/
theorem deleteRange_end_to_endM (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (tok : Option GoString) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : KVDep GF) (na : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        ⌜E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
        kvServerAt p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode na ∗ txn.deleteRangeRequestIs r o ∗
        kvDepOwnM E.authOn s E ρ γr tok d ∗ ⌜kvDepPreM E.authOn d (.deleteRange o)⌝ ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"DeleteRange")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (match deleteCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM E.authOn s E ρ γr tok d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ deleteAppliedOk s E ρ.rd F o (opDepQ d) resp rv ∗
              (⌜E.authOn = true⌝ → writeGrantOn (srvTLSId s) E ρ tok (irrDeleteRange o))) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ deleteErrOk s E ρ F o e)) ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }} := by
  iintro %Φ ⟨#Pv, #Ps, %Hany, #Hsrv, #Hsrd, #Hlb, #Hat, Hc, Hc0, #HF, #Hna, #Hr, Hdep, %Hpre, #HtokC⟩ HΦ
  ihave #HKV := raftKV_serverM s E ρ γr c F d na tok $$ []
  · iframe #; ipureintro; exact Hany
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_DeleteRange p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ctx r o) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAnsM]; iframe Hc Hc0 Hdep HF Hna HtokC; ipureintro
    first | exact ⟨trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩ | exact ⟨fun _ => rfl, trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩ | exact ⟨trivial, trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩ | exact ⟨fun _ => trivial, trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩
  inext
  iintro %resp %err ⟨Hpost, #HSe⟩
  iapply HΦ
  iframe HSe
  cases hc : deleteCheck o with
  | some e =>
    simp only [hc, srvKVAnsM]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -, -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAnsM]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- **`range_end_to_end` in the server's auth mode** (the auth component's stage 4): the read at the
mode's model (`rangeAnsOkM`), with auth on the read's check (`rangeAuthed`). -/
theorem range_end_to_endM (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (tok : Option GoString) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : KVDep GF) (na : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        ⌜E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
        kvServerAt p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode na ∗ txn.rangeRequestIs r o ∗
        kvDepOwnM E.authOn s E ρ γr tok d ∗ ⌜kvDepPreM E.authOn d (.range o)⌝ ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Range")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (match rangeCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM E.authOn s E ρ γr tok d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
              rangeAnsOkM E.authOn E γr c F o resp rv (rangeDepQM E.authOn γr.kv d) ∗
              (⌜E.authOn = true⌝ → rangeAuthed (srvTLSId s) E γr c na tok o)) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗
            srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
            rangeErrDesc E.authOn E γr c F o (rangeDepQM E.authOn γr.kv d) err)) ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }} := by
  iintro %Φ ⟨#Pv, #Ps, %Hany, #Hsrv, #Hsrd, #Hlb, #Hat, Hc, Hc0, #HF, #Hna, #Hr, Hdep, %Hpre, #HtokC⟩ HΦ
  ihave #HKV := raftKV_serverM s E ρ γr c F d na tok $$ []
  · iframe #; ipureintro; exact Hany
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Range p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ctx r o) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAnsM]; iframe Hc Hc0 Hdep HF Hna HtokC; ipureintro
    first | exact ⟨trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩ | exact ⟨fun _ => rfl, trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩ | exact ⟨trivial, trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩ | exact ⟨fun _ => trivial, trivial, (kvDepPreML_of_M _ _ _ _ Hpre)⟩
  inext
  iintro %resp %err ⟨Hpost, #HSe⟩
  iapply HΦ
  iframe HSe
  cases hc : rangeCheck o with
  | some e =>
    simp only [hc, srvKVAnsM]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -, -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAnsM]
    icases Hpost with (Hok | ⟨%Herr, %e, %Hne, ⟨Hcr, Hid, Hlt, #HrO⟩, #Hgo⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iframe Hcr Hid Hlt
    -- (k8s etcd3 7c-2 part 2, S4/S5) what the gRPC error says of the read
    ihave #Pm : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
    · iPkgInit
    ihave #Pa : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
    · iPkgInit
    ihave #Pe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
    · iPkgInit
    iapply rangeErrDesc_of_grpcErrOut _ _ _ _ _ _ _ e err Hne $$ Pv Pm Pa Pe HrO Hgo

/-- **`txn_end_to_end` in the server's auth mode** (the auth component's stage 4): at the mode's
model (`txnReadAnsM`), with auth on a read-only transaction's checks (`txnAuthed`) and a writing
one's grant. Leases admitted with auth on at the
revocable lease mode (`kvDepPreML`; auth-lease S4 item 5). -/
theorem txn_end_to_endML
    (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (tok : Option GoString) (r : Loc) (cs : List CmpModel)
    (ts es : List ReqOp) (F : mvcc.Log) (d : KVDep GF) (na : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        ⌜E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
        kvServerAt p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode na ∗ txnReqIs r cs ts es ∗ txnReqWire r ts es ∗
        ⌜txnInModel cs ts es⌝ ∗ kvDepOwnM E.authOn s E ρ γr tok d ∗ ⌜kvDepPreML E.authOn ρ.kv.lm d (.txn cs ts es)⌝ ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Txn")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (match txnAllCheck (sint.Z n) cs ts es with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM E.authOn s E ρ γr tok d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
              ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
                if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
                  txnReadAnsM E.authOn E γr c F t (rangeDepQM E.authOn γr.kv d) resp rv ∗
                  (⌜E.authOn = true⌝ → txnAuthed (srvTLSId s) E γr c na tok t))
                else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp rv ∗
                  (⌜E.authOn = true⌝ → ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
                    writeGrantOn (srvTLSId s) E ρ tok (irrTxn tw)))) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
            ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
              if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e)) ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }} := by
  iintro %Φ ⟨#Pv, #Ps, %Hany, #Hsrv, #Hsrd, #Hlb, #Hat, Hc, Hc0, #HF, #Hna, #Hr, #Hw, %Hin, Hdep, %Hpre, #HtokC⟩ HΦ
  ihave #HKV := raftKV_serverM s E ρ γr c F d na tok $$ []
  · iframe #; ipureintro; exact Hany
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Txn p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n
    ctx r cs ts es) $$ [Hc Hc0 Hdep]
  · iframe #; simp only [srvKVAnsM]; iframe Hc Hc0 Hdep HF Hna HtokC; ipureintro
    first | exact ⟨Hin, Hpre⟩ | exact ⟨fun _ => rfl, Hin, Hpre⟩ | exact ⟨trivial, Hin, Hpre⟩ | exact ⟨fun _ => trivial, Hin, Hpre⟩
  inext
  iintro %resp %err ⟨Hpost, #HSe⟩
  iapply HΦ
  iframe HSe
  cases hc : txnAllCheck (sint.Z n) cs ts es with
  | some e =>
    simp only [hc, srvKVAnsM]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -, -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAnsM]
    icases Hpost with (Hok | ⟨%Herr, %e, -, HA, -⟩)
    · ileft; iexact Hok
    iright
    isplitr
    · ipureintro; exact Herr
    iexists e
    iexact HA

/-- `txn_end_to_endML`'s at a request of `kvDepPreM` (no lease, plain transactions). -/
theorem txn_end_to_endM
    (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (tok : Option GoString) (r : Loc) (cs : List CmpModel)
    (ts es : List ReqOp) (F : mvcc.Log) (d : KVDep GF) (na : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        ⌜E.authMode ≠ .any⌝ ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
        kvServerAt p s (srvKVAnsM E.authOn s E ρ γr c F d na tok) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode na ∗ txnReqIs r cs ts es ∗ txnReqWire r ts es ∗
        ⌜txnInModel cs ts es⌝ ∗ kvDepOwnM E.authOn s E ρ γr tok d ∗ ⌜kvDepPreM E.authOn d (.txn cs ts es)⌝ ∗
        □ (⌜E.authOn = true⌝ → auth.ctxToken ctx tok) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Txn")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (match txnAllCheck (sint.Z n) cs ts es with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwnM E.authOn s E ρ γr tok d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.api.mvccReaders E.γ 1) h rv rv' ∗
              srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
              ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
                if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗
                  txnReadAnsM E.authOn E γr c F t (rangeDepQM E.authOn γr.kv d) resp rv ∗
                  (⌜E.authOn = true⌝ → txnAuthed (srvTLSId s) E γr c na tok t))
                else iprop(txnAppliedAns E ρ.rd F t (opDepQ d) resp rv ∗
                  (⌜E.authOn = true⌝ → ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗
                    writeGrantOn (srvTLSId s) E ρ tok (irrTxn tw)))) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
            ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
              if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ F t e)) ∗
        go_etcd_io.etcd.cache.v3.srvErrOk err }} := by
  iintro %Φ ⟨#Pv, #Ps, %Hany, #Hsrv, #Hsrd, #Hlb, #Hat, Hc, Hc0, #HF, #Hna, #Hr, #Hw, %Hin, Hdep, %Hpre, #HtokC⟩ HΦ
  iapply (txn_end_to_endML p s E ρ γr c cid mid n ctx tok r cs ts es F d na) $$ [Hc Hc0 Hdep] HΦ
  iframe #
  iframe Hc Hc0 Hdep
  ipureintro; first | exact kvDepPreML_of_M _ _ _ _ Hpre | exact ⟨Hany, kvDepPreML_of_M _ _ _ _ Hpre⟩ | exact ⟨Hin, kvDepPreML_of_M _ _ _ _ Hpre⟩ | exact ⟨Hany, Hin, kvDepPreML_of_M _ _ _ _ Hpre⟩

/-- **What a successful gRPC `Put` applied** (pure; with `put_end_to_end`'s `putAppliedOk`):
through the uber-applier's chain `alarmChain on ns cr`, the put was applied by the client model:
the log after is the log the entry met with the put's one change (`putChangeOf`, the client's
`putTxnOp`), neither the corrupt nor the space alarm raised (`put_applied_model`). -/
theorem put_end_to_end_model (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (l : mvcc.Log) (skip on ns cr : Bool) (hc : x.chain = apply.alarmChain on ns cr)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    x'.log = x.log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter x.log))]] ∧
      ns = false ∧ cr = false := by
  obtain ⟨hlog, ha⟩ := put_applied_model o hm x x' _ skip on ns cr hc h
  simp only [apply.Outcome.logAfter] at hlog
  unfold apply.alarmPut at ha
  cases cr <;> cases ns <;> simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_or] at ha
  obtain ⟨o', hm', hq⟩ := ha
  unfold apply.quotaAfter at hq
  rcases hq with hq | ⟨l', -, hq⟩
  · subst hq
    unfold apply.putModel at hm'
    rcases hm' with ⟨-, hm'⟩ | ⟨-, -, hm'⟩ | hm'
    · cases hm'
    · cases hm'
    · cases hm'; exact ⟨hlog, rfl, rfl⟩
  · cases hq

/-- **What a successful gRPC `DeleteRange` applied** (pure; with `deleteRange_end_to_end`'s
`deleteAppliedOk`): through `alarmChain on ns cr`, the delete `op'` of the decoded request was
applied by the client model: the log after commits its changes (`delChanges`, none if nothing
matched), the corrupt alarm not raised (`deleteRange_applied_model`). -/
theorem deleteRange_end_to_end_model (op op' : OpFull) (hm : apply.HeaderModel)
    (rq' : apply.IRRModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip on ns cr : Bool)
    (hc : x.chain = apply.alarmChain on ns cr)
    (hw : irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq')
    (hop : rq'.deleteRange = some op')
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    x'.log = mvcc.commitLog x.log (txn.delChanges (mvcc.stateAfter x.log) op') ∧ cr = false := by
  obtain ⟨hlog, ha⟩ := deleteRange_applied_model op op' hm rq' x x' _ skip on ns cr hc hw hop h
  simp only [apply.Outcome.logAfter] at hlog
  unfold apply.alarmDelete at ha
  cases cr <;> simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_or] at ha
  unfold apply.deleteModel at ha
  rcases ha with ha | ⟨-, ha⟩
  · cases ha; exact ⟨hlog, rfl⟩
  · cases ha

/-- **`AuthServer.AuthEnable` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the handler's
contract discharged by the server's `AuthEnable` with auth on (`server_auth_enable_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem authEnable_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF))
    (Qa : List auth.AuthState → IProp GF) (r : Loc) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ ⌜r ≠ null⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok irrAuthEnable Qa) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"AuthEnable"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ tok irrAuthEnable F (adminQh ρ.kv irrAuthEnable Qa)
          etcdserverpb.AuthEnableResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, %Hr, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"AuthEnable" (GoInterface.ok ctx) r
      iprop(⌜r ≠ null⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok irrAuthEnable Qa))
      (adminOutOn s E ρ tok irrAuthEnable F (adminQh ρ.kv irrAuthEnable Qa) etcdserverpb.AuthEnableResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨%Hr', HP'⟩ HΨ
    iapply (server_auth_enable_on s E ρ ctx tok cd Qa r F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_AuthEnable p s ctx r iprop(⌜r ≠ null⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok irrAuthEnable Qa))
      (adminOutOn s E ρ tok irrAuthEnable F (adminQh ρ.kv irrAuthEnable Qa) etcdserverpb.AuthEnableResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **`AuthServer.RoleAdd` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the handler's
contract discharged by the server's `RoleAdd` with auth on (`server_role_add_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem roleAdd_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF))
    (Qa : List auth.AuthState → IProp GF) (r : Loc) (name : GoString) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ apply.authRoleAddIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrRoleAdd name) Qa) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleAdd"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ tok (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name) Qa)
          etcdserverpb.AuthRoleAddResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hreq, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"RoleAdd" (GoInterface.ok ctx) r
      iprop(apply.authRoleAddIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrRoleAdd name) Qa))
      (adminOutOn s E ρ tok (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name) Qa) etcdserverpb.AuthRoleAddResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨#Hreq', %Hn', HP'⟩ HΨ
    iapply (server_role_add_on s E ρ ctx tok cd Qa r name F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_RoleAdd p s ctx r iprop(apply.authRoleAddIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrRoleAdd name) Qa))
      (adminOutOn s E ρ tok (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name) Qa) etcdserverpb.AuthRoleAddResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **`AuthServer.UserGrantRole` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the handler's
contract discharged by the server's `UserGrantRole` with auth on (`server_user_grant_role_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem userGrantRole_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF))
    (Qa : List auth.AuthState → IProp GF) (r : Loc) (user role : GoString) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ apply.authUserGrantRoleIs r (user, role) ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrUserGrantRole user role) Qa) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGrantRole"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ tok (irrUserGrantRole user role) F (adminQh ρ.kv (irrUserGrantRole user role) Qa)
          etcdserverpb.AuthUserGrantRoleResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hreq, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"UserGrantRole" (GoInterface.ok ctx) r
      iprop(apply.authUserGrantRoleIs r (user, role) ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrUserGrantRole user role) Qa))
      (adminOutOn s E ρ tok (irrUserGrantRole user role) F (adminQh ρ.kv (irrUserGrantRole user role) Qa) etcdserverpb.AuthUserGrantRoleResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨#Hreq', %Hn', HP'⟩ HΨ
    iapply (server_user_grant_role_on s E ρ ctx tok cd Qa r user role F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_UserGrantRole p s ctx r iprop(apply.authUserGrantRoleIs r (user, role) ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrUserGrantRole user role) Qa))
      (adminOutOn s E ρ tok (irrUserGrantRole user role) F (adminQh ρ.kv (irrUserGrantRole user role) Qa) etcdserverpb.AuthUserGrantRoleResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **`AuthServer.RoleGrantPermission` with auth on, end to end** (the auth plan's E3z, 2026-10-27): the handler's
contract discharged by the server's `RoleGrantPermission` with auth on (`server_role_grant_permission_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem roleGrantPermission_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF))
    (Qa : List auth.AuthState → IProp GF) (r : Loc) (name : GoString) (w : Option auth.PermW) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ apply.authRoleGrantPermissionIs r (name, w) ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrRoleGrantPermission name w) Qa) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleGrantPermission"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ tok (irrRoleGrantPermission name w) F (adminQh ρ.kv (irrRoleGrantPermission name w) Qa)
          etcdserverpb.AuthRoleGrantPermissionResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hreq, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"RoleGrantPermission" (GoInterface.ok ctx) r
      iprop(apply.authRoleGrantPermissionIs r (name, w) ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrRoleGrantPermission name w) Qa))
      (adminOutOn s E ρ tok (irrRoleGrantPermission name w) F (adminQh ρ.kv (irrRoleGrantPermission name w) Qa) etcdserverpb.AuthRoleGrantPermissionResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨#Hreq', %Hn', HP'⟩ HΨ
    iapply (server_role_grant_permission_on s E ρ ctx tok cd Qa r name w F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_RoleGrantPermission p s ctx r iprop(apply.authRoleGrantPermissionIs r (name, w) ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (adminHistAu s E ρ tok (irrRoleGrantPermission name w) Qa))
      (adminOutOn s E ρ tok (irrRoleGrantPermission name w) F (adminQh ρ.kv (irrRoleGrantPermission name w) Qa) etcdserverpb.AuthRoleGrantPermissionResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **What `AuthServer.UserAdd` with auth on answers** (the server's error and response, before
`togRPCError`): the hashing's error, nothing proposed (`adminPreOn` back), or the server's answer to
the proposed request (`userAddOutOn`). -/
def userAddAnsOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) (name : GoString) (b : Bool)
    (Qa : List auth.AuthState → IProp GF) (l : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜l = null ∧ err ≠ GoInterface.nil⌝ ∗
      adminPreOn s E ρ ctx tok cd F (userAddHistAu s E ρ tok name b Qa)) ∨
    userAddOutOn s E ρ tok F name b Qa l err)

/-- **`AuthServer.UserAdd` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the
handler's contract discharged by the server's `UserAdd` with auth on (`server_user_add_on`), the
password hashed by `bcrypt` (whose error is one `togRPCError` takes, since E3y): on `(resp, nil)`,
some model of the request (its name `name`, its password choice `b`) applied at the committed
prefix before its entry, its admin step succeeding there (`userAddOutOn`'s `appliedOkM true`,
`adminDoneM`); an error is `togRPCError`'s of the hashing's (nothing proposed), the apply thread's
or the proposal's (`authWrapOut`, `userAddAnsOn`). -/
theorem userAdd_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF))
    (Qa : List auth.AuthState → IProp GF) (ast : GoInterfaceOk) (r : Loc) (name pw hpw : GoString)
    (o : Loc) (b : Bool) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        ⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" r ↦□ name ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" r ↦□ o ∗ auth.userOptsAt o b ∗
        ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx tok cd F (userAddHistAu s E ρ tok name b Qa) }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserAdd"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (userAddAnsOn s E ρ ctx tok cd F name b Qa) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hast, #Hcost, %Hr, #HN, Hpw, Hhpw, #Ho, #Hopts, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"UserAdd" (GoInterface.ok ctx) r
      iprop(structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
        adminPreOn s E ρ ctx tok cd F (userAddHistAu s E ρ tok name b Qa))
      (userAddAnsOn s E ρ ctx tok cd F name b Qa) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨Hpw', Hhpw', HP'⟩ HΨ
    iapply (server_user_add_on s E ρ ctx tok cd Qa ast r name pw hpw o b F) $$ [Hpw' Hhpw' HP']
    · iframe # Hpw' Hhpw' HP'
      try (ipureintro; first | assumption | exact ⟨Hr, Hn⟩)
    inext
    iintro %resp %err Hpost
    iapply HΨ
    icases Hpost with (⟨%Hre, #Ha, HP2⟩ | ⟨#Ha, Hout⟩)
    · iframe Ha
      iunfold authEntryOut
      iright
      isplitr
      · ipureintro; exact Hre
      iunfold userAddAnsOn
      ileft
      iframe HP2
      ipureintro; exact ⟨rfl, Hre.2⟩
    · iframe Ha
      iunfold authEntryOut at Hout
      iunfold authEntryOut
      iunfold userAddAnsOn
      icases Hout with (⟨%He, HQ⟩ | ⟨%Hre, HQ⟩)
      · ileft
        isplitr
        · ipureintro; exact He
        iright; iexact HQ
      · iright
        isplitr
        · ipureintro; exact Hre
        iright; iexact HQ
  iapply (AuthServer.wp_UserAdd p s ctx r iprop(structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
        adminPreOn s E ρ ctx tok cd F (userAddHistAu s E ρ tok name b Qa))
      (userAddAnsOn s E ρ ctx tok cd F name b Qa)) $$ [Hpw Hhpw HP] HΦ
  iframe # Hpw Hhpw HP

/-- `UserAdd`'s answer (`authWrapOut` of `userAddAnsOn`, the password choice `false`): the run's
slot back and, on `nil`, the reply (`userAddReplied`). -/
theorem authWrapOut_userAdd (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) (name : GoString)
    (Qa : List auth.AuthState → IProp GF) (resp : Loc)
    (err : GoInterface) :
    v3rpc.authWrapOut (userAddAnsOn s E ρ ctx tok cd F name false Qa) resp err ⊢
      authSlot s E ∗
        (⌜err = GoInterface.nil⌝ -∗ userAddReplied (srvTLSId s) E ρ tok name Qa) := by
  iintro H
  iunfold v3rpc.authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, -, %e0, %He0, H⟩)
  · subst He
    iunfold userAddAnsOn at H
    icases H with (⟨%Hc, -⟩ | H)
    · exact absurd rfl Hc.2
    iunfold userAddOutOn at H
    icases H with ⟨%um, %Hum, H⟩
    ihave ⟨Hs, Hrep⟩ := adminOutOn_reply s E ρ tok (irrUserAdd um) Qa F _ resp GoInterface.nil $$ H
    iframe Hs
    iintro -
    unfold userAddReplied
    iexists um
    isplitr
    · ipureintro; exact Hum
    iapply Hrep
    ipureintro; rfl
  · iunfold userAddAnsOn at H
    icases H with (⟨-, HP⟩ | H)
    · iunfold adminPreOn at HP
      icases HP with ⟨-, -, Hlt, Hrd, -⟩
      unfold authSlot
      iframe Hlt Hrd
      iintro %He
      exact absurd He Hr.2
    · iunfold userAddOutOn at H
      icases H with ⟨%um, -, H⟩
      ihave ⟨Hs, -⟩ := adminOutOn_reply s E ρ tok (irrUserAdd um) Qa F _ null e0 $$ H
      iframe Hs
      iintro %He
      exact absurd He Hr.2

/-- **`AuthServer.UserAdd`'s answer is not `nil` without an error** (`adminOutOn_nn`). -/
theorem authWrapOut_userAdd_nn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) (name : GoString)
    (Qa : List auth.AuthState → IProp GF) (resp : Loc) (err : GoInterface) :
    v3rpc.authWrapOut (userAddAnsOn s E ρ ctx tok cd F name false Qa) resp err ⊢
      ⌜err = GoInterface.nil → resp ≠ null⌝ := by
  iintro H
  iunfold v3rpc.authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, -⟩)
  · subst He
    iunfold userAddAnsOn at H
    icases H with (⟨%Hc, -⟩ | H)
    · exact absurd rfl Hc.2
    iunfold userAddOutOn at H
    icases H with ⟨%um, -, H⟩
    ihave %Hn := v3rpc.adminOutOn_nn s E ρ tok (irrUserAdd um) F _ _ resp rfl $$ H
    ipureintro; intro _; exact Hn
  · ipureintro; intro He; exact absurd He Hr.2

/-- **`*AuthServer` implements `pb.AuthServer`** (a method-set fact, from the method sets goose
emits; `RegisterAuthServer`'s `grpcImplements`). -/
theorem authServer_isAuthServer :
    go.typeSetContains (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty)
      etcdserverpb.AuthServer.ty = true := by
  go_type_set

/-- **etcd's `UserAdd`, as the service runs it** (`grpcHandlerOwnOk`; the auth plan's E3za): the
`*AuthServer` `p` of the server `s` with auth on (`isServerReqM true`, the id budget
`□ |==> idCred ρ.ids 1`), whose auth store hashes at a valid cost (`bcryptCostOk`): given the run's
slot (`authSlot`), the decoded request (its `Password` and `HashedPassword` the run's own) and
`etcdUserAddSpec`, its slot back and on success the reply (`userAddReplied`). -/
theorem etcd_userAddHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ast : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ⊢
      grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserAdd")
        (authSlot s E) (etcdUserAddSpec (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR, #Hast, #Hcost⟩
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Ho, Hspec⟩ HΨ
  simp only [pbAuthUserAddRequest]
  icases Hr with ⟨%Hrn, #HN, %o, #Ho', #Hopts⟩
  iunfold userOptsFalse at Hopts
  icases Ho with ⟨Hpw, Hhpw⟩
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold grpcSpecAt at Hspec
  icases Hspec with ⟨%md, #Hmd, Hspec⟩
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  iunfold etcdUserAddSpec, etcdUserAddSpecW at Hspec
  icases Hspec with ⟨#HΨe, %Qa, %Hn, #Hu, Hk⟩
  ihave #Hu' : iprop(□ userAddHistAu s E ρ (auth.mdTokenOf md) m.name false Qa) $$ []
  · unfold userAddHistAu
    iintro !> %um %Hum
    iapply adminHistAu_of_tok
    iapply Hu
    ipureintro; exact Hum
  ihave Hu := HNR
  imod Hu with Hid
  imod (v3rpc.kvLogLb_nil (GF := GF) E.γs) with #HF
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrc
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrc
  iapply (userAdd_end_to_end_on p s E ρ ci (auth.mdTokenOf md) cd Qa ast r m.name m.pw [] o false []) $$
    [Hpw Hhpw Hlt Hrd Hid]
  · unfold adminPreOn
    iframe; iframe #
    try (ipureintro; exact ⟨Hrn, Hn⟩)
  inext
  iintro %resp %err Hout
  ihave ⟨#HSe, Hout⟩ := v3rpc.authWrapOut_srvErrOk _ resp err $$ Hout
  ihave %Hrn := authWrapOut_userAdd_nn s E ρ ci (auth.mdTokenOf md) cd [] m.name Qa resp err $$ Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_userAdd s E ρ ci (auth.mdTokenOf md) cd [] m.name Qa resp err $$ Hout
  ihave Hed := handlerErrOut_allSrv (GF := GF) Ψe err $$ HΨe HSe
  iapply HΨ
  iframe Hed
  iframe Hs
  iframe HSe
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthUserAddResponse]; ipureintro; exact Hrn He
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `RoleAdd`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_roleAddHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleAdd")
        (authSlot s E) (etcdRoleAddSpec (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hspec⟩ HΨ
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold grpcSpecAt at Hspec
  icases Hspec with ⟨%md, #Hmd, Hspec⟩
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  iunfold etcdRoleAddSpec, etcdRoleAddSpecW at Hspec
  icases Hspec with ⟨#HΨe, %Qa, %Hn, #Hha, Hk⟩
  ihave #Hha' := adminHistAu_of_tok s E ρ (auth.mdTokenOf md) _ Qa $$ Hha
  ihave Hu := HNR
  imod Hu with Hid
  imod (v3rpc.kvLogLb_nil (GF := GF) E.γs) with #HF
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrc
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrc
  iapply (roleAdd_end_to_end_on p s E ρ ci (auth.mdTokenOf md) cd Qa r m []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    simp only [apply.authRoleAddIs, auth.roleAddReqIs, pbAuthRoleAddRequest]
    iframe; iframe #
    ipureintro; exact Hn
  inext
  iintro %resp %err Hout
  ihave ⟨#HSe, Hout⟩ := v3rpc.authWrapOut_srvErrOk _ resp err $$ Hout
  ihave %Hrn := v3rpc.authWrapOut_admin_nn s E ρ (auth.mdTokenOf md) (irrRoleAdd m) _ [] _ resp err rfl $$ Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (auth.mdTokenOf md) (irrRoleAdd m) Qa [] _ resp err $$ Hout
  ihave Hed := handlerErrOut_allSrv (GF := GF) Ψe err $$ HΨe HSe
  iapply HΨ
  iframe Hed
  iframe Hs
  iframe HSe
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthRoleAddResponse]; ipureintro; exact Hrn He
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `UserGrantRole`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_userGrantRoleHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGrantRole")
        (authSlot s E) (etcdUserGrantRoleSpec (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hspec⟩ HΨ
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold grpcSpecAt at Hspec
  icases Hspec with ⟨%md, #Hmd, Hspec⟩
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  iunfold etcdUserGrantRoleSpec, etcdUserGrantRoleSpecW at Hspec
  icases Hspec with ⟨#HΨe, %Qa, %Hn, #Hha, Hk⟩
  ihave #Hha' := adminHistAu_of_tok s E ρ (auth.mdTokenOf md) _ Qa $$ Hha
  ihave Hu := HNR
  imod Hu with Hid
  imod (v3rpc.kvLogLb_nil (GF := GF) E.γs) with #HF
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrc
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrc
  iapply (userGrantRole_end_to_end_on p s E ρ ci (auth.mdTokenOf md) cd Qa r m.1 m.2 []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    simp only [apply.authUserGrantRoleIs, pbAuthUserGrantRoleRequest]
    iframe; iframe #
    ipureintro; exact Hn
  inext
  iintro %resp %err Hout
  ihave ⟨#HSe, Hout⟩ := v3rpc.authWrapOut_srvErrOk _ resp err $$ Hout
  ihave %Hrn := v3rpc.authWrapOut_admin_nn s E ρ (auth.mdTokenOf md) (irrUserGrantRole m.1 m.2) _ [] _ resp err rfl $$ Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (auth.mdTokenOf md) (irrUserGrantRole m.1 m.2) Qa [] _ resp err $$ Hout
  ihave Hed := handlerErrOut_allSrv (GF := GF) Ψe err $$ HΨe HSe
  iapply HΨ
  iframe Hed
  iframe Hs
  iframe HSe
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthUserGrantRoleResponse]; ipureintro; exact Hrn He
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `RoleGrantPermission`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_roleGrantPermissionHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleGrantPermission")
        (authSlot s E) (etcdRoleGrantPermissionSpec (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hspec⟩ HΨ
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold grpcSpecAt at Hspec
  icases Hspec with ⟨%md, #Hmd, Hspec⟩
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  iunfold etcdRoleGrantPermissionSpec, etcdRoleGrantPermissionSpecW at Hspec
  icases Hspec with ⟨#HΨe, %Qa, %Hn, #Hha, Hk⟩
  ihave #Hha' := adminHistAu_of_tok s E ρ (auth.mdTokenOf md) _ Qa $$ Hha
  ihave Hu := HNR
  imod Hu with Hid
  imod (v3rpc.kvLogLb_nil (GF := GF) E.γs) with #HF
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrc
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrc
  iapply (roleGrantPermission_end_to_end_on p s E ρ ci (auth.mdTokenOf md) cd Qa r m.1 (some m.2) []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    simp only [apply.authRoleGrantPermissionIs, pbAuthRoleGrantPermissionRequest]
    iframe; iframe #
    ipureintro; exact Hn
  inext
  iintro %resp %err Hout
  ihave ⟨#HSe, Hout⟩ := v3rpc.authWrapOut_srvErrOk _ resp err $$ Hout
  ihave %Hrn := v3rpc.authWrapOut_admin_nn s E ρ (auth.mdTokenOf md) (irrRoleGrantPermission m.1 (some m.2)) _ [] _ resp err rfl $$ Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (auth.mdTokenOf md) (irrRoleGrantPermission m.1 (some m.2)) Qa [] _ resp err $$ Hout
  ihave Hed := handlerErrOut_allSrv (GF := GF) Ψe err $$ HΨe HSe
  iapply HΨ
  iframe Hed
  iframe Hs
  iframe HSe
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthRoleGrantPermissionResponse]; ipureintro; exact Hrn He
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `AuthEnable`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_authEnableHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"AuthEnable")
        (authSlot s E) (etcdAuthEnableSpec (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hk⟩ HΨ
  simp only [pbAuthEnableRequest] at *
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold grpcSpecAt at Hk
  icases Hk with ⟨%md, #Hmd, Hk⟩
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  iunfold etcdAuthEnableSpec, etcdAuthEnableSpecW at Hk
  icases Hk with ⟨#HΨe, %Qa, #Hha, Hk⟩
  ihave #Hha' := adminHistAu_of_tok s E ρ (auth.mdTokenOf md) _ Qa $$ Hha
  ihave Hu := HNR
  imod Hu with Hid
  imod (v3rpc.kvLogLb_nil (GF := GF) E.γs) with #HF
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrc
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrc
  iapply (authEnable_end_to_end_on p s E ρ ci (auth.mdTokenOf md) cd Qa r []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    iframe; iframe #
  inext
  iintro %resp %err Hout
  ihave ⟨#HSe, Hout⟩ := v3rpc.authWrapOut_srvErrOk _ resp err $$ Hout
  ihave %Hrn := v3rpc.authWrapOut_admin_nn s E ρ (auth.mdTokenOf md) irrAuthEnable _ [] _ resp err rfl $$ Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (auth.mdTokenOf md) irrAuthEnable Qa [] _ resp err $$ Hout
  ihave Hed := handlerErrOut_allSrv (GF := GF) Ψe err $$ HΨe HSe
  iapply HΨ
  iframe Hed
  iframe Hs
  iframe HSe
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthEnableResponse]; ipureintro; exact Hrn He
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `UserAdd`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodMd`): the generated
`_Auth_UserAdd_Handler` on the `*AuthServer` `p` whose `UserAdd` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_userAddMethodOk (p : Loc) (Spec : GrpcSpecMd (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserAdd")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_UserAdd_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %D %Got %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, HD, #Hdec, #Hch⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthUserAddRequest) -∗
      (pbAuthUserAddRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthUserAddRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ (l : Loc) m, (pbAuthUserAddRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserAddRequest.ty) #l)) $$ []
  · iintro !> %l %_ -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthUserAddRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_UserAdd_Handler pbAuthUserAddRequest pbAuthUserAddResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk D Got ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HD]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hout⟩
  iapply HΨ
  iframe

/-- **etcd's `RoleAdd`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodMd`): the generated
`_Auth_RoleAdd_Handler` on the `*AuthServer` `p` whose `RoleAdd` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_roleAddMethodOk (p : Loc) (Spec : GrpcSpecMd (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleAdd")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_RoleAdd_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %D %Got %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, HD, #Hdec, #Hch⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthRoleAddRequest) -∗
      (pbAuthRoleAddRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthRoleAddRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ (l : Loc) m, (pbAuthRoleAddRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthRoleAddRequest.ty) #l)) $$ []
  · iintro !> %l %_ -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthRoleAddRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_RoleAdd_Handler pbAuthRoleAddRequest pbAuthRoleAddResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk D Got ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HD]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hout⟩
  iapply HΨ
  iframe

/-- **etcd's `UserGrantRole`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodMd`): the generated
`_Auth_UserGrantRole_Handler` on the `*AuthServer` `p` whose `UserGrantRole` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_userGrantRoleMethodOk (p : Loc) (Spec : GrpcSpecMd (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGrantRole")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_UserGrantRole_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %D %Got %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, HD, #Hdec, #Hch⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthUserGrantRoleRequest) -∗
      (pbAuthUserGrantRoleRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthUserGrantRoleRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ (l : Loc) m, (pbAuthUserGrantRoleRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserGrantRoleRequest.ty) #l)) $$ []
  · iintro !> %l %_ -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthUserGrantRoleRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_UserGrantRole_Handler pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk D Got ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HD]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hout⟩
  iapply HΨ
  iframe

/-- **etcd's `RoleGrantPermission`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodMd`): the generated
`_Auth_RoleGrantPermission_Handler` on the `*AuthServer` `p` whose `RoleGrantPermission` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_roleGrantPermissionMethodOk (p : Loc) (Spec : GrpcSpecMd (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleGrantPermission")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_RoleGrantPermission_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %D %Got %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, HD, #Hdec, #Hch⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthRoleGrantPermissionRequest) -∗
      (pbAuthRoleGrantPermissionRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthRoleGrantPermissionRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ (l : Loc) m, (pbAuthRoleGrantPermissionRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthRoleGrantPermissionRequest.ty) #l)) $$ []
  · iintro !> %l %_ -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthRoleGrantPermissionRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_RoleGrantPermission_Handler pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk D Got ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HD]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hout⟩
  iapply HΨ
  iframe

/-- **etcd's `AuthEnable`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodMd`): the generated
`_Auth_AuthEnable_Handler` on the `*AuthServer` `p` whose `AuthEnable` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_authEnableMethodOk (p : Loc) (Spec : GrpcSpecMd (GF := GF) pbAuthEnableRequest pbAuthEnableResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOkMd (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"AuthEnable")
        iprop(S ∗ [∗list] R ∈ Rs, R) Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOkMd (@! etcdserverpb._Auth_AuthEnable_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOkMd
  iintro %D %Got %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, HD, #Hdec, #Hch⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthEnableRequest) -∗
      (pbAuthEnableRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthEnableRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ (l : Loc) m, (pbAuthEnableRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthEnableRequest.ty) #l)) $$ []
  · iintro !> %l %_ -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthEnableRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_AuthEnable_Handler pbAuthEnableRequest pbAuthEnableResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk D Got ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HD]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hout⟩
  iapply HΨ
  iframe

end endToEnd

/-! ## The Auth service over gRPC (the auth plan's E3za, 2026-10-27)

The five admin methods `examples/etcd/auth`'s `SetUp` calls, as grpc runs them (`etcd_*MethodOk`, from
each handler's E3y result, `etcd_*HandlerOk`), and served at an address (`etcd_auth_served`), with
etcd's specs (`AuthService.lean`). -/

section authGrpc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-- An owning metadata-indexed service method meeting `Spec` with `S` meets it with more (`S ∗ R`,
`R` given back; as `grpcHandlerOwnOk_frame`). -/
theorem grpcHandlerOwnOkMd_frame {Req Rep : ProtoMsg GF} (h : val) (S R : IProp GF)
    (Spec : GrpcSpecMd Req Rep) :
    grpcHandlerOwnOkMd h S Spec ⊢ grpcHandlerOwnOkMd h iprop(S ∗ R) Spec := by
  iintro #Hh
  unfold grpcHandlerOwnOkMd
  iintro %m %Φ %Ψe %ci %cd %r !> %Ψ ⟨⟨HS, HR⟩, #Hctx, #Hrc, #Hr, Hown, HSpec⟩ HΨ
  iapply Hh $$ %m %Φ %Ψe %ci %cd %r [HS Hown HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's Auth methods** as registered, with etcd's specs. -/
def etcdAuthMethods (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Auth/UserAdd", pbAuthUserAddRequestT, pbAuthUserAddResponseT, etcdUserAddSpec (srvTLSId s) E ρ,
     (functions etcdserverpb._Auth_UserAdd_Handler []), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p, pbAuthUserAddRequestT_reg, pbAuthUserAddResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Auth/UserGrantRole", pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleResponseT, etcdUserGrantRoleSpec (srvTLSId s) E ρ,
     (functions etcdserverpb._Auth_UserGrantRole_Handler []), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p, pbAuthUserGrantRoleRequestT_reg, pbAuthUserGrantRoleResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Auth/RoleAdd", pbAuthRoleAddRequestT, pbAuthRoleAddResponseT, etcdRoleAddSpec (srvTLSId s) E ρ,
     (functions etcdserverpb._Auth_RoleAdd_Handler []), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p, pbAuthRoleAddRequestT_reg, pbAuthRoleAddResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Auth/RoleGrantPermission", pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionResponseT, etcdRoleGrantPermissionSpec (srvTLSId s) E ρ,
     (functions etcdserverpb._Auth_RoleGrantPermission_Handler []), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p, pbAuthRoleGrantPermissionRequestT_reg, pbAuthRoleGrantPermissionResponseT_reg⟩,
   ⟨go!"/etcdserverpb.Auth/AuthEnable", pbAuthEnableRequestT, pbAuthEnableResponseT, etcdAuthEnableSpec (srvTLSId s) E ρ,
     (functions etcdserverpb._Auth_AuthEnable_Handler []), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p, pbAuthEnableRequestT_reg, pbAuthEnableResponseT_reg⟩]

/-- **etcd's server serves its Auth methods** (the auth plan's E3za; as `etcd_kv_served`;
per-type stage B3: each run on a fork of grpc's, `grpc.serve`): the gRPC server at `addr` (with the streams `sms`) built
with the chain `ics` of transparent interceptors (with their per-run resources `Rs`), with the Auth
service registered on the `*AuthServer` `p` (`v3rpc.authRegs p` among the registered methods), its
runs borrowing from the server's built pools and run pool (`srvRevokeBuilt`, `srvRunPool`, with
`srvLevels`) a bundle that holds `authSlot` and the interceptors' resources (`h1`, `h2`), registers
etcd's specs of `UserAdd`, `UserGrantRole`, `RoleAdd`, `RoleGrantPermission` and `AuthEnable` at
`addr` (`isGrpcRpcMd`, metadata-indexed: 5b). Premises: the server's with auth on (`isServerReqM
true`, the id budget `□ |==> idCred ρ.ids 1`), the `*AuthServer` over it (`authServerIs`: what
`NewAuthServer(s)` returns), its auth store's bcrypt cost (`bcryptCostOk`), the interceptors'
contracts, the packages'. -/
theorem etcd_auth_served (addr : GoString) (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (ast : GoInterfaceOk) (ics : List GoFunc) (Rs : List (IProp GF))
    (regs : List (GoString × GoFunc × GoInterface)) (sms : List (GrpcStreamMethod GF)) (F : IProp GF)
    (h1 : srvRunBundle s E γr ⊢ iprop(authSlot s E ∗ [∗list] R ∈ Rs, R) ∗ F)
    (h2 : iprop(authSlot s E ∗ [∗list] R ∈ Rs, R) ∗ F ⊢ srvRunBundle s E γr)
    (hregs : ∀ x ∈ v3rpc.authRegs p, x ∈ regs) (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ∗
        grpcServerAt addr ics regs etcdTys sms ∗ srvRevokeBuilt s E ∗ srvRunPool s E γr ⊢
      |={⊤}=> isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserAdd" (etcdUserAddSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/UserGrantRole" (etcdUserGrantRoleSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleAdd" (etcdRoleAddSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/RoleGrantPermission" (etcdRoleGrantPermissionSpec (srvTLSId s) E ρ) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.Auth/AuthEnable" (etcdAuthEnableSpec (srvTLSId s) E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR, #Hast, #Hcost, #Hics, #Hl, #Hb, #Hrp⟩
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hu := etcd_userAddHandlerOk p s E ρ ast $$ []
  · iframe #
  ihave #Hg := etcd_userGrantRoleHandlerOk p s E ρ $$ []
  · iframe #
  ihave #Hr := etcd_roleAddHandlerOk p s E ρ $$ []
  · iframe #
  ihave #Hp := etcd_roleGrantPermissionHandlerOk p s E ρ $$ []
  · iframe #
  ihave #He := etcd_authEnableHandlerOk p s E ρ $$ []
  · iframe #
  ihave #Hu' := grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ Rs, R) _ $$ Hu
  ihave #Hg' := grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ Rs, R) _ $$ Hg
  ihave #Hr' := grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ Rs, R) _ $$ Hr
  ihave #Hp' := grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ Rs, R) _ $$ Hp
  ihave #He' := grpcHandlerOwnOkMd_frame _ _ iprop([∗list] R ∈ Rs, R) _ $$ He
  ihave #Hmu := etcd_userAddMethodOk p _ _ ics Rs $$ [Hu' Ppb Hics]
  · iframe #
  ihave #Hmg := etcd_userGrantRoleMethodOk p _ _ ics Rs $$ [Hg' Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_roleAddMethodOk p _ _ ics Rs $$ [Hr' Ppb Hics]
  · iframe #
  ihave #Hmp := etcd_roleGrantPermissionMethodOk p _ _ ics Rs $$ [Hp' Ppb Hics]
  · iframe #
  ihave #Hme := etcd_authEnableMethodOk p _ _ ics Rs $$ [He' Ppb Hics]
  · iframe #
  ihave #Hmu' := grpcMethodOkMd_slot _ _ _ _ (srvRunBundle s E γr) F _ h1 h2 $$ Hmu
  ihave #Hmg' := grpcMethodOkMd_slot _ _ _ _ (srvRunBundle s E γr) F _ h1 h2 $$ Hmg
  ihave #Hmr' := grpcMethodOkMd_slot _ _ _ _ (srvRunBundle s E γr) F _ h1 h2 $$ Hmr
  ihave #Hmp' := grpcMethodOkMd_slot _ _ _ _ (srvRunBundle s E γr) F _ h1 h2 $$ Hmp
  ihave #Hme' := grpcMethodOkMd_slot _ _ _ _ (srvRunBundle s E γr) F _ h1 h2 $$ Hme
  ihave #Hku := srvRunOk_of_pools s E γr (@! etcdserverpb._Auth_UserAdd_Handler)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p) ics _ HL $$ [Hmu']
  · iframe #
  ihave #Hkg := srvRunOk_of_pools s E γr (@! etcdserverpb._Auth_UserGrantRole_Handler)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p) ics _ HL $$ [Hmg']
  · iframe #
  ihave #Hkr := srvRunOk_of_pools s E γr (@! etcdserverpb._Auth_RoleAdd_Handler)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p) ics _ HL $$ [Hmr']
  · iframe #
  ihave #Hkp := srvRunOk_of_pools s E γr (@! etcdserverpb._Auth_RoleGrantPermission_Handler)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p) ics _ HL $$ [Hmp']
  · iframe #
  ihave #Hke := srvRunOk_of_pools s E γr (@! etcdserverpb._Auth_AuthEnable_Handler)
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p) ics _ HL $$ [Hme']
  · iframe #
  imod (grpc.serve addr ics regs etcdTys sms (etcdAuthMethods p s E ρ)
    (by
      intro x hx
      apply hregs
      simp only [etcdAuthMethods, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [v3rpc.authRegs])
    (by
      intro x hx
      simp only [etcdAuthMethods, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)) $$ [] with Hrpcs
  · iframe Hl
    imodintro
    unfold etcdAuthMethods
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcRunOkMd (Req := pbAuthUserAddRequest) (Rep := pbAuthUserAddResponse) _ _ _ _)
      iexact Hku
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcRunOkMd (Req := pbAuthUserGrantRoleRequest) (Rep := pbAuthUserGrantRoleResponse) _ _ _ _)
      iexact Hkg
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcRunOkMd (Req := pbAuthRoleAddRequest) (Rep := pbAuthRoleAddResponse) _ _ _ _)
      iexact Hkr
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcRunOkMd (Req := pbAuthRoleGrantPermissionRequest) (Rep := pbAuthRoleGrantPermissionResponse) _ _ _ _)
      iexact Hkp
    iapply bigSepL_cons_intro'
    isplitl []
    · change Iris.ProofMode.Entails' _ (grpcRunOkMd (Req := pbAuthEnableRequest) (Rep := pbAuthEnableResponse) _ _ _ _)
      iexact Hke
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdAuthMethods, pbAuthUserAddRequestT, pbAuthUserAddResponseT, pbAuthUserGrantRoleRequestT, pbAuthUserGrantRoleResponseT, pbAuthRoleAddRequestT, pbAuthRoleAddResponseT, pbAuthRoleGrantPermissionRequestT, pbAuthRoleGrantPermissionResponseT, pbAuthEnableRequestT, pbAuthEnableResponseT]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, #H5, -⟩
  imodintro
  iframe #

end authGrpc

/-! ## The vertical slice, unit V1 (2026-10-13): the clients' model implemented

`ClientModel.lean`: the clients' class `EtcdModel` (`cache/v3/EtcdModel.lean`, fourteen axioms
until V1) instantiated by the server (`etcdModelOfServer`), each law a theorem; what the
server's answers give the model (`etcdState_of_range`, `etcdState_of_txnRead`,
`etcdReached_of_hdr`, `revToken_of_put`). (V1's wire, the generated stub's four axioms and
`isKVClient`, was superseded at the merge of unit C1 by the client's own proof down to grpc's
`ClientConn.Invoke`: `client/v3/InvKVConn.lean`, `client/v3/Results.lean`.) -/

section slice
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.api.v3 mvcc txn

/-- **The server implements the clients' model of etcd** (`etcdModelOfServer E γr on`, every law a
theorem; strict M1: at the read names `γr` and the auth mode `on`): its predicates are the server's
facts about prefixes of the KV model of committed raft logs (`srvEtcdState`, `srvStep`: `srvLog`,
in place of mvcc's seal `idxSealed`), the revisions of such logs (`srvReachedAt`: `srvRevLbA`, in
place of mvcc's `certOk`) and the revisions' tokens the apply thread mints (`revTok`). -/
theorem etcd_model_of_server (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) :
    ∃ M : EtcdModel GF, M.etcdState = srvEtcdState γr on ∧ M.etcdReachedAt = srvReachedAt γr on ∧
      M.etcdRevToken = revTok E ∧ M.EtcdStep = srvStep γr on :=
  ⟨etcdModelOfServer E γr on, rfl, rfl, rfl, rfl⟩

/-- **A header's revision is reached**: the revision of a log the server witnessed (every
answer's header revision is one: `rangeAnsOk`'s, `txnReadAns`'s, the writes' `E.Nx` of the log
after, which is `srvApi.kvNx γr on` at the server's tie) gives `etcdReached` in the server's model
(`etcdReached_of_nx`; strict M1, in place of `certOk`). -/
theorem etcdReached_of_hdr (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) (log : mvcc.Log)
    (r : w64) (h : sint.Z r < log.length) :
    srvApi.kvNx γr on log ⊢ etcdReached (EM := etcdModelOfServer E γr on) r :=
  etcdReached_of_nx E γr on log r h

/-- The off server's witness is the off model's (`srvKVInvs`' tie). -/
theorem srvKVInvs_kvNx (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvs E γr ⊢ ⌜E.Nx = srvApi.kvNx γr false⌝ := by
  iintro #H
  iunfold srvKVInvs at H
  icases H with ⟨-, -, -, -, -, %h, -⟩
  ipureintro; rw [h]; rfl

/-- A log with a receipt for its changes is small (`txn.LogSmall`), under the receipt bound. -/
theorem logSmall_of_receipt (log : mvcc.Log) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ⧖ (mvcc.logCh log) ⊢ ⌜txn.LogSmall log⌝ := by
  iintro Hr
  ihave %Hm := preceipt_lt _ $$ Hr
  ipureintro
  unfold txn.LogSmall txn.logChanges; unfold mvcc.logCh at Hm; omega

/-- **A read's log, in the off server's model** (the common part of `etcdState_of_range` and
`etcdState_of_txnRead`): the witness `E.Nx log` of a read view's answer is the model's `kvNx`
(persistent), and the log's keys are bounded (`read_keys`). -/
theorem read_kvNx (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (log : mvcc.Log) :
    isServerRead s E γr ∗ E.Nx log ⊢
      |={⊤}=> srvApi.kvNx γr false log ∗ ⌜mvcc.LogPutsLe etcdKeyMax log⌝ := by
  iintro ⟨#Hsrd, Hnx⟩
  ihave #Hinv := srvKVInvs_of_read s E γr $$ Hsrd
  ihave %hNx := srvKVInvs_kvNx E γr $$ Hinv
  ihave #Hkn : srvApi.kvNx γr false log $$ [Hnx]
  · rw [← hNx]; iexact Hnx
  ihave Hnx2 : E.Nx log $$ []
  · rw [hNx]; iexact Hkn
  imod read_keys s E γr log $$ Hsrd Hnx2 with %Hk
  imodintro
  iframe Hkn
  ipureintro; exact Hk

/-- **What a successful `Range` gives the clients' model** (`range_end_to_end`'s `rangeAnsOk`):
the header's revision `r` is the witnessed log's last (reached), and etcd's state at `r` under any
prefix is the log's last state restricted to it; the response is the txn package's range at that
log (`txn.rangeResult`; with `rangeSel_underPfx`, its selection of a range under the prefix is the
restricted state's). (2026-10-30, `notes/keylen.md`) With the server's read view
(`isServerRead`, a handler's), whose KV invariant bounds the log's keys (`read_keys`), as
`etcdState`'s model now requires. (Strict M1: in the model `etcdModelOfServer E γr false`; the
log is small by its receipt, under `receiptBound GF ≤ 2 ^ 62`, in place of mvcc's `storeSmall`.) -/
theorem etcdState_of_range (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : Log)
    (o : OpFull) (resp : Loc) (r : w64) (pfx : GoString) (Q : List EntryModel → IProp GF)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isServerRead s E γr ∗ rangeAnsOk E γr c F o resp r Q ⊢
      |={⊤}=> ∃ log : Log, ⌜r = W64 ((log.length : Int) - 1) ∧ 2 ≤ log.length ∧
          log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
        □ etcdState (self := etcdModelOfServer E γr false) r pfx (underPfx pfx (stateAfter log)) ∗
        ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ ∗
        etcdReached (EM := etcdModelOfServer E γr false) r ∗
        (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
        (∃ crev : Int,
          txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) crev o true) := by
  iintro ⟨#Hsrd, Hok⟩
  iunfold rangeAnsOk at Hok
  iunfold rangeAnsOkM at Hok
  icases Hok with ⟨%log, -, Hnx, Hrc, %Hl, Hlin, -, Hres⟩
  obtain ⟨hw, h2, h3, rfl, hF⟩ := Hl
  ihave %hs := logSmall_of_receipt log hrb $$ Hrc
  imod read_kvNx s E γr log $$ [$Hsrd $Hnx] with ⟨#Hkn, %Hk⟩
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave ⟨#Hst, %Hwf⟩ := etcdState_of_nx_last E γr false log pfx h2 h3 hw hs Hk $$ Hkn
  imodintro
  iexists log
  iframe Hst Hlin Hres
  isplitr
  · ipureintro; exact ⟨rfl, h2, h3, hF⟩
  isplitr
  · ipureintro; exact Hwf
  iapply etcdReached_of_nx E γr false log _ (by omega) $$ Hkn

/-- **What a successful read-only `Txn` gives the clients' model** (`txn_end_to_end`'s
`txnReadAns`): as `etcdState_of_range`, the response the server's run of the transaction at the
log's last revision. -/
theorem etcdState_of_txnRead (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : Log)
    (t : TxnModel) (Q : List EntryModel → IProp GF) (resp : Loc) (r : w64) (pfx : GoString)
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isServerRead s E γr ∗ txnReadAns E γr c F t Q resp r ⊢
      |={⊤}=> ∃ log : Log, ⌜r = W64 ((log.length : Int) - 1) ∧ 2 ≤ log.length ∧
          log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
        □ etcdState (self := etcdModelOfServer E γr false) r pfx (underPfx pfx (stateAfter log)) ∗
        ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ ∗
        etcdReached (EM := etcdModelOfServer E γr false) r ∗
        (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
        txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
          (txn.srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).1
          (txn.srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).2.2 := by
  iintro ⟨#Hsrd, Hok⟩
  iunfold txnReadAns at Hok
  iunfold txnReadAnsM at Hok
  icases Hok with ⟨%log, -, Hnx, Hrc, %Hl, Hlin, -, Hres⟩
  obtain ⟨hw, h2, h3, rfl, hF⟩ := Hl
  ihave %hs := logSmall_of_receipt log hrb $$ Hrc
  imod read_kvNx s E γr log $$ [$Hsrd $Hnx] with ⟨#Hkn, %Hk⟩
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave ⟨#Hst, %Hwf⟩ := etcdState_of_nx_last E γr false log pfx h2 h3 hw hs Hk $$ Hkn
  imodintro
  iexists log
  iframe Hst Hlin Hres
  isplitr
  · ipureintro; exact ⟨rfl, h2, h3, hF⟩
  isplitr
  · ipureintro; exact Hwf
  iapply etcdReached_of_nx E γr false log _ (by omega) $$ Hkn

/-- **What a successful `Put` gives the clients' model** (`put_end_to_end`'s `putAppliedOk`, the
client's `putApplied`): the token of the header's revision `r` (`etcdRevToken r`: the apply thread
minted it when the put's revision committed) and that etcd has reached `r`. (Strict M1: in the
model at the witness's names, `hNx : E.Nx = srvApi.kvNx γw on`, the server's tie, in place of
mvcc's `certOk`.) -/
theorem revToken_of_put (E : apply.AEnv GF) (γw : ReadNames) (on : Bool) (F : Log) (o : OpFull)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) (hNx : E.Nx = srvApi.kvNx γw on) :
    putApplied E γw F o Q resp r ⊢
      etcdRevToken (self := etcdModelOfServer E γw on) r ∗
        etcdReached (EM := etcdModelOfServer E γw on) r := by
  iintro Hok
  iunfold putApplied at Hok
  icases Hok with ⟨%hm, %x, %x', %l, %skip, %Hp, -, -, HMint, -, Hnx, -, -, -⟩
  obtain ⟨Hstep, rfl, -, -, h3⟩ := Hp
  obtain ⟨cs, hcs⟩ := put_appended o hm x x' l skip Hstep
  ihave #Hkn : srvApi.kvNx γw on x'.log $$ [Hnx]
  · rw [← hNx]; iexact Hnx
  iunfold revMinted at HMint
  icases HMint with (%He | ⟨%cs', %He, Ht⟩)
  · rw [hcs] at He
    exact absurd (congrArg List.length He) (by simp)
  isplitl [Ht]
  · rw [etcdModelOfServer_etcdRevToken]
    iexact Ht
  iapply etcdReached_of_nx E γw on x'.log _ (by rw [hcs]; simp; word) $$ Hkn

end slice

/-! ## The watch slice, unit W-S (2026-10-14): the gRPC watch service

`watchServer.Watch` (`watch.go`) over the verified mvcc watch stream, against a server-end stream
(`srvStreamIs`, InvWatchStream.lean: a premise, in the shape of `notes/grpc-stream-spec.md`):
every response it sends at down position `j` carries `watchDn j m` (`watchStreamSpec`): its
header is the server's, and it answers a request the client sent (`ctrlOk`) or is the mvcc
stream's response for a watcher, the watcher's responses with events sent before it, then it,
being exactly its responses with events received (`mvccOk`, whose `watchRecvOk` is mvcc's watch
guarantee). `watchStreamSpec_step` turns a watcher's events into the clients' model's steps
(`revEvs`), `srvStep_of_watch` into `srvStep` of the server's model. -/

section watch
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The watch service's method** (`watchServer.Watch`, linked): see the section header. -/
theorem watch_server : EtcdGrove.v3rpc.watchServer.Watch.spec (GF := GF) (hG := hG) :=
  watchServer.wp_Watch

/-- **The watch server's constructor** (`NewWatchServer`, linked): `isWatchServer`. -/
theorem new_watch_server : EtcdGrove.v3rpc.NewWatchServer.spec (GF := GF) (hG := hG) :=
  wp_NewWatchServer

/-- **A registered watcher was authorized** (the auth plan's A4, 2026-10-24; strengthened in G2,
2026-10-30; `WatchClass.lean`, `ctrlWatcher_authorized`): with the server's auth mode `on γa`
(`watchSrvOk`'s tag, `auth.modeTag r.srv.tag`), the watcher a created, not canceled, control
response names (`watchDn`'s `ctrlOk`, `ctrlWatcher`, of the run `r` and the stream's token `tok`;
strict M1: the run's registry entry `regIs r.γreg m.watchId i`, in place of mvcc's internal
`watcherIs`/`idAssigned`) has a range every key of which some principal could read at a recorded state
of the auth history, at an index at least the create's bound `c.bound`: auth disabled there, or the
principal a user with the root role, or one whose READ permissions cover the key; and the
principal is bound to the stream's token (`infoBoundT`: the empty user, a token issued to its user,
or the server's TLS identity). The interval the check saw is the interval mvcc registers for every
request shape (`createRangeOk_inRange`): the point, the proper range, `WithFromKey`'s `"\x00"` end,
the empty key. -/
theorem watch_registered_authorized (r : WRun GF) (tok : Option GoString)
    (γa : auth.AuthNames) (c : CreateReqM) (m : WatchRespM) (h : m.canceled = false) :
    auth.modeTag (GF := GF) r.srv.tag (.on γa) ∗ ctrlWatcher r tok (.create c) m ⊢
      ∃ (i : RegInfo) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (j : Nat)
        (st : auth.AuthState),
        ⌜createRangeOk c m.watchId i.rg⌝ ∗ regIs r.γreg m.watchId i ∗
        auth.authStateAt γa j st ∗ infoBoundT (srvTLSId r.srv.s) (.on γa) tok info ∗
        ⌜c.bound ≤ j ∧ (st.enabled = false ∨
          ((auth.authInfoM info).rev ≠ 0 ∧
            ∃ u, st.users !! (auth.authInfoM info).user = some u ∧
              (auth.isRoot u ∨ ∀ x, i.rg.covers x = true →
                ∃ p ∈ auth.userPerms st u, p.covers .read x)))⌝ :=
  ctrlWatcher_authorized r tok γa c m h

end watch

/-! ## The watch service on the wire (unit W-W)

The generated stream handler `_Watch_Watch_Handler` (linked) runs `watchServer.Watch` on the
wrapped raw server end grpc passes (`srvStreamIs_of_raw`, over `GenericServerStream`'s methods,
axioms: Goose does not translate methods of generic types); with the server's stream
interceptors transparent (`srvStreamInterceptorsOk`, a premise: grpc-prometheus's and
`newStreamInterceptor` are not verified), the handler meets the registration's contract
(`etcd_watchMethodOk`), and with the server's pools it meets grpc's stream run contract, its
specification holding at its content (`etcd_watch_served`): what the single-process start takes to
register it at the server's address (`grpc.start'`, phase 7's switch, SW1), which a client's
`NewStream` needs. -/

section watch_wire
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.api.v3

/-- **The generated stream handler** (`_Watch_Watch_Handler`, linked): see the section header. -/
theorem watch_handler : EtcdGrove.etcdserverpb._Watch_Watch_Handler.spec (GF := GF) (hG := hG) :=
  etcdserverpb.wp__Watch_Watch_Handler

/-- **The watch server's `Watch` is a stream method** (`grpcStreamHandlerOk`): on the wrapped
server end, with the run's store reader token (`mvccReaders W.γm 1`, the send loop's, given back
through the wait group `close` waits on), the client's content `watchUp` and the stream
specification `watchSpec R` (`watchStreamSpec` at the server's names), from `watch_server`; the
receive loop borrows its own resources from the pools of levels 2 and 3 (per-type stage B3). -/
theorem watch_streamHandlerOk (p : Loc) (R : WSrv GF) (W : SrvW GF) (N₂ N₃ : Namespace)
    (γ₂ γ₃ : GName) (F₂ F₃ : IProp GF)
    (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) (HT : 5 ≤ threadBound GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvWOk W R.wsl wsN ∗
      threadPool.isThreadPoolL N₂ 2 γ₂ iprop(F₂ ∗ R.E.RD) ∗
      threadPool.isThreadPoolL N₃ 3 γ₃ iprop(mvcc.api.mvccReaders W.γm 1 ∗ F₃) ⊢
    grpcStreamHandlerOk (Req := pbWatchRequest)
      #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
        go!"Watch" #p)
      iprop(mvcc.api.mvccReaders W.γm 1 ∗ levelTok v3rpc.ctxErrLvl) (watchUp R) (fun md => watchSpec R W (auth.mdTokenOf md)) := by
  have := srvWOk_persistent (mvcc.api.mvccApi_persistent_law_holds (GF := GF)) W R.wsl wsN
  iintro ⟨#Hinit, #Hws, #HW, #Hp2, #Hp3⟩
  unfold grpcStreamHandlerOk
  iintro !> %γs %Dn %ci %cd %st %Φ HSpec ⟨Hrd, Hl4⟩ #Hst HRt HSt HAux HΦ
  iunfold grpcStreamSpecAt at HSpec
  icases HSpec with ⟨%md, #Hmd, HSpec⟩
  ihave #HtokC0 := auth.ctxToken_of_ctxInMD ci md $$ Hmd
  ihave #HtokC : iprop(□ (⌜R.E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ci) (auth.mdTokenOf md))) $$ []
  · iintro !> -; iexact HtokC0
  ihave HSpec : watchStreamSpec γs R W (auth.mdTokenOf md) Dn $$ [HSpec]
  · iexact HSpec
  ihave #Hup := upOk_watchUp (GF := GF) R
  iapply (watch_server p R W st γs (watchUp R) Dn ci (auth.mdTokenOf md) cd N₂ N₃ γ₂ γ₃ F₂ F₃)
    $$ [HSpec HRt HSt HAux Hrd Hl4]
  · iframe
    iframe #
    ipureintro; exact ⟨Htb, HT⟩
  inext
  iintro %err ⟨#Hse, -, Hrd, Hl4⟩
  iapply HΦ $$ %err Hse [Hrd Hl4]
  iframe

/-- **The generated handler meets the registration's contract** (`grpcStreamMethodOk`) for the
`*watchServer` `p` (its type implements `WatchServer`: a method-set fact), under the server's
stream interceptors `ics`, transparent with their run resources `Rs`, at any slot `S` that holds
the interceptors' resources and a store reader token and gives them back (`h1`, `h2`); the receive
loop borrows from the pools of levels 2 and 3. -/
theorem etcd_watchMethodOk (p : Loc) (R : WSrv GF) (W : SrvW GF) (ics : List GoFunc)
    (Rs : List (IProp GF)) (icW : GoFunc) (RW : IProp GF) (S F : IProp GF) (N₂ N₃ : Namespace)
    (γ₂ γ₃ : GName) (F₂ F₃ : IProp GF)
    (h1 : S ⊢ iprop((mvcc.api.mvccReaders W.γm 1 ∗ levelTok v3rpc.ctxErrLvl) ∗
      [∗list] R' ∈ Rs ++ [RW], R') ∗ F)
    (h2 : iprop((mvcc.api.mvccReaders W.γm 1 ∗ levelTok v3rpc.ctxErrLvl) ∗
      [∗list] R' ∈ Rs ++ [RW], R') ∗ F ⊢ S)
    (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) (HT : 5 ≤ threadBound GF)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvWOk W R.wsl wsN ∗ srvStreamInterceptorsOk ics Rs ∗
      srvStreamInterceptorWOk icW RW ∗
      threadPool.isThreadPoolL N₂ 2 γ₂ iprop(F₂ ∗ R.E.RD) ∗
      threadPool.isThreadPoolL N₃ 3 γ₃ iprop(mvcc.api.mvccReaders W.γm 1 ∗ F₃) ⊢
    grpcStreamMethodOk (Req := pbWatchRequest) (@! etcdserverpb._Watch_Watch_Handler)
      (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) (ics ++ [icW])
      S (watchUp R) (fun md => watchSpec R W (auth.mdTokenOf md)) := by
  have := srvWOk_persistent (mvcc.api.mvccApi_persistent_law_holds (GF := GF)) W R.wsl wsN
  iintro ⟨#Hpb, #Hinit, #Hws, #HW, #Hics, #HicW, #Hp2, #Hp3⟩
  ihave #Hh := watch_streamHandlerOk p R W N₂ N₃ γ₂ γ₃ F₂ F₃ Htb HT $$ [Hinit Hws HW Hp2 Hp3]
  · iframe #
  unfold grpcStreamMethodOk
  isplitr
  · iintro !> %md
    iapply streamSpecOk_watchSpec R W
  iintro !> %γs %Dn %ci %cd %st %info HSpec HS #Hraw HRt HSt HAux #Hinfo
  icases h1 $$ HS with ⟨⟨Hrd, HRs⟩, HF⟩
  iapply (srvStreamChainWP_of_okW iprop(True) ics Rs icW RW pbWatchRequestT pbWatchResponseT pbWatchRequestT_reg
    pbWatchResponseT_reg (watchUp R) Dn γs ci cd
    (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) st info
    (@! etcdserverpb._Watch_Watch_Handler)
    (fun v => iprop(∃ err : GoInterface, ⌜v = #err⌝ ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗ S)))
  simp only [pbWatchRequestT, pbWatchResponseT]
  iframe #
  iframe HRs
  isplit
  · iintro %st' %ci' %cd' #Heq #Hraw'
    ihave HSpec : grpcStreamSpecAt (fun md => watchSpec R W (auth.mdTokenOf md)) ci' γs Dn $$ [HSpec]
    · iunfold grpcStreamSpecAt at HSpec
      icases HSpec with ⟨%md, #Hmd, HSpec⟩
      iunfold grpcStreamSpecAt
      iexists md
      ihave #Hmd' := Heq $$ %md Hmd
      iframe Hmd' HSpec
    iapply (watch_handler pbWatchRequest pbWatchResponse (watchUp R)
      (fun md => watchSpec R W (auth.mdTokenOf md))
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty, #p⟩
      iprop(mvcc.api.mvccReaders W.γm 1 ∗ levelTok v3rpc.ctxErrLvl) γs Dn ci' cd' st' rfl rfl hset)
      $$ [HSpec Hrd HRt HSt HAux]
    · iframe
      iframe #
      iintro !> %l Hl
      iexists _
      iexact Hl
    inext
    iintro %err ⟨#Hse, Hrd⟩
    iexists err
    isplitr
    · ipureintro; rfl
    iframe Hse
    iintro HRs
    iexists err
    isplitr
    · ipureintro; rfl
    iframe Hse
    iapply h2
    iframe
  · iintro HRs %err - #Hse
    iexists err
    isplitr
    · ipureintro; rfl
    iframe Hse
    iapply h2
    iframe

/-- **The watch method, as the single-process start takes it** (phase 7's switch, SW1, 2026-11-24:
`grpc.start'` takes the server's streams, `GrpcStreamMethod`, with their response content `dn`):
`Watch_ServiceDesc`'s `Watch` stream registered with the `*watchServer` `p`, at the registered
models, the client's content `watchUp`, the stream specification `watchStreamSpec` at the token of
the stream's metadata (`auth.mdTokenOf`), and its content `watchDn` at that token. -/
def watchMethod (p : Loc) (R : WSrv GF) (W : SrvW GF) : GrpcStreamMethod GF :=
  { name := go!"/etcdserverpb.Watch/Watch", Req := pbWatchRequestT, Rep := pbWatchResponseT,
    reqReg := pbWatchRequestT_reg, repReg := pbWatchResponseT_reg,
    Up := watchUp R, spec := fun md => watchSpec R W (auth.mdTokenOf md),
    dn := fun md γs => watchDn γs R W (auth.mdTokenOf md),
    handler := functions etcdserverpb._Watch_Watch_Handler [],
    srv := interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p }

/-- **The watch service's run contract** (unit W-W; as `etcd_kv_served` for the KV service; since
phase 7's switch, SW1, 2026-11-24, what the single-process start takes for the stream,
`grpc.start'`, which registers it: until then this theorem took the server's stream token
`grpcStreamServerAt` and gave the registration `isGrpcStreamMd`): the generated handler on the
`*watchServer` `p`, under the stream interceptors `ics` (transparent, with the resources `Rs`) and
`icW`, with the server's pools (`srvRevokeBuilt`, `srvRunPool`; per-type stage B3, in place of `n` run
slots: each run borrows the stream bundle `srvStreamBundle`, which holds the interceptors' resources
and a store reader token, `h1`/`h2`, and its receive loop borrows its own), meets grpc's stream run
contract at `watchMethod p R W` (`grpcStreamRunOk`), whose specification holds at its content
`watchDn`: its stream specification is `watchStreamSpec` at the server's names and ids, and each
request the client sends carries `watchUp` (restricted, a watch token and the auth bound with each
create). Since G2 (2026-10-30) the registration is metadata-indexed: the stream specification is at
the token of the stream's metadata (`auth.mdTokenOf`), for which each create's check passed. -/
theorem etcd_watch_served (p : Loc) (R : WSrv GF) (W : SrvW GF) (ics : List GoFunc)
    (Rs : List (IProp GF)) (icW : GoFunc) (RW : IProp GF)
    (γr : ReadNames) (F : IProp GF)
    (h1 : srvStreamBundle R.s R.E γr ⊢
      iprop((mvcc.api.mvccReaders W.γm 1 ∗ levelTok v3rpc.ctxErrLvl) ∗
        [∗list] R' ∈ Rs ++ [RW], R') ∗ F)
    (h2 : iprop((mvcc.api.mvccReaders W.γm 1 ∗ levelTok v3rpc.ctxErrLvl) ∗
        [∗list] R' ∈ Rs ++ [RW], R') ∗ F ⊢
      srvStreamBundle R.s R.E γr)
    (hγ : W.γm = R.E.γ) (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders)
    (HL : srvLevels (GF := GF))
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvWOk W R.wsl wsN ∗ srvStreamInterceptorsOk ics Rs ∗
      srvStreamInterceptorWOk icW RW ∗ srvRevokeBuilt R.s R.E ∗ srvRunPool R.s R.E γr ⊢
    □ [∗list] m ∈ [watchMethod p R W], grpcStreamRunOk #m.handler m.srv (ics ++ [icW]) m.Up m.spec ∗
      □ ∀ md γs, m.spec md γs (m.dn md γs) := by
  have := srvWOk_persistent (mvcc.api.mvccApi_persistent_law_holds (GF := GF)) W R.wsl wsN
  have HT : 5 ≤ threadBound GF := by
    have := HL; unfold srvLevels srvLevelK srvRevokeK at this; omega
  have hpool : srvRunPool (GF := GF) R.s R.E γr ⊢ ∃ γ₃ : GName, threadPool.isThreadPoolL srvRunN 3 γ₃
      iprop(mvcc.api.mvccReaders W.γm 1 ∗ (srvReadReader R.s γr ∗ srvBemuReader R.s)) := by
    rw [hγ]; unfold srvRunPool; exact .rfl
  iintro ⟨#Hpb, #Hinit, #Hws, #HW, #Hics, #HicW, #Hb, #Hrp⟩
  ihave ⟨%γ₁, %γ₂, -, #Hp2⟩ := srvRevokeBuilt_runPools R.s R.E $$ Hb
  ihave ⟨%γ₃, #Hp3⟩ := hpool $$ Hrp
  ihave #Hok := etcd_watchMethodOk p R W ics Rs icW RW (srvStreamBundle R.s R.E γr) F srvRevokeInnerN
    srvRunN γ₂ γ₃ (srvLeadTimeReader R.s) iprop(srvReadReader R.s γr ∗ srvBemuReader R.s) h1 h2 Htb HT
    hset $$ [Hpb Hinit Hws HW Hics HicW Hp2 Hp3]
  · iframe #
  ihave #Hrun := srvStreamRunOk_of_pools (Req := pbWatchRequest) (Rep := pbWatchResponse)
    R.s R.E γr (@! etcdserverpb._Watch_Watch_Handler)
    (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) (ics ++ [icW])
    (watchUp R) (fun md => watchSpec R W (auth.mdTokenOf md)) HL $$ [Hok Hb Hrp]
  · iframe #
  iintro !>
  iapply BigSepL.bigSepL_singleton.2
  simp only [watchMethod, pbWatchRequestT, pbWatchResponseT]
  isplitr
  · iexact Hrun
  iintro !> %md %γs
  simp only [watchSpec]; unfold watchStreamSpec
  iintro !> %j %x
  isplit
  · iintro H; iexact H
  · iintro H; iexact H

/-- **etcd's stream run bundle as the watch method's slot** under a chain of two interceptors, a
resource-free one and one with the run's level-0 token (`newStreamInterceptor`'s, prove-ps2-cap,
2026-11-23: `IsCapabilityEnabled`'s): a store reader token, the interceptors' `True` and level 0,
and the rest. -/
theorem srvStreamBundle_watchSlot (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvStreamBundle s E γr ⊣⊢
      iprop((mvcc.api.mvccReaders E.γ 1 ∗ levelTok v3rpc.ctxErrLvl) ∗
        [∗list] R' ∈ [iprop(True)] ++ [levelTok 0], R') ∗
      iprop(srvLgReader s ∗ (srvLeadTimeReader s ∗ E.RD) ∗
        (srvReadReader s γr ∗ srvBemuReader s)) := by
  unfold srvStreamBundle
  simp only [List.cons_append, List.nil_append]
  constructor
  · iintro ⟨H0, H4, Hlg, Hlt, Hrd, Hrr, Hbe⟩
    isplitl [Hrd H4 H0]
    · iframe Hrd H4
      iapply BigSepL.bigSepL_cons.2
      isplitl []
      · itrivial
      iapply BigSepL.bigSepL_cons.2
      iframe H0
      iapply BigSepL.bigSepL_nil.2
      itrivial
    iframe
  · iintro ⟨⟨⟨Hrd, H4⟩, HRs⟩, Hlg, Hlt, Hrr, Hbe⟩
    icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨-, HRs⟩
    icases BigSepL.bigSepL_cons.1 $$ HRs with ⟨H0, -⟩
    iframe

/-- **The watch service is served by etcd's server** (`etcd_watch_served` at the stream chain
`v3rpc.Server` installs, `grpc.go`: `grpc.ChainStreamInterceptor(serverMetrics.StreamServerInterceptor(),
newStreamInterceptor(s))`, in that order): grpc-prometheus's `im` (assumed transparent, as
`etcd_kv_served` assumes the unary one) and etcd's `newStreamInterceptor` `is` (its contract a
premise: proved by the stream-interceptor unit), neither with a run resource. (Phase 7's switch,
SW1) What the single-process start takes for the stream (`grpc.start'`), as `etcd_watch_served`. -/
theorem etcd_watch_served_chain (p : Loc) (R : WSrv GF) (W : SrvW GF)
    (im is : GoFunc) (γr : ReadNames)
    (hγ : W.γm = R.E.γ) (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders)
    (HL : srvLevels (GF := GF))
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvWOk W R.wsl wsN ∗ srvStreamInterceptorOk im iprop(True) ∗
      srvStreamInterceptorWOk is (levelTok 0) ∗
      srvRevokeBuilt R.s R.E ∗ srvRunPool R.s R.E γr ⊢
    □ [∗list] m ∈ [watchMethod p R W], grpcStreamRunOk #m.handler m.srv [im, is] m.Up m.spec ∗
      □ ∀ md γs, m.spec md γs (m.dn md γs) := by
  have := srvWOk_persistent (mvcc.api.mvccApi_persistent_law_holds (GF := GF)) W R.wsl wsN
  have hb := srvStreamBundle_watchSlot (GF := GF) R.s R.E γr
  rw [← hγ] at hb
  have h := etcd_watch_served p R W [im] [iprop(True)] is (levelTok 0) γr _ hb.1 hb.2 hγ Htb HL hset
  simp only [List.cons_append, List.nil_append] at h
  iintro ⟨#Hpb, #Hinit, #Hws, #HW, #Him, #His, #Hb, #Hrp⟩
  iapply h
  iframe #
  iunfold srvStreamInterceptorsOk
  iframe #
  try iunfold srvStreamInterceptorsOk
  try simp only [List.cons_append, List.nil_append]
  try itrivial

/-- **etcd's stream interceptor** (`newStreamInterceptor`, linked; the watch slice's unit W-W): it
starts the leader monitor and returns a transparent stream interceptor (`srvStreamInterceptorOk`,
no resource) (until 2026-11-13, k8s 7f-4 step 6, under the deployment premise `runsNoRequireLeader`). -/
theorem new_stream_interceptor :
    EtcdGrove.v3rpc.newStreamInterceptor.spec (GF := GF) (hG := hG) :=
  wp_newStreamInterceptor

/-- **The watch service is served by etcd's server, with etcd's own stream interceptor**
(`etcd_watch_served_chain` with its second interceptor the one `newStreamInterceptor(s)` returns,
`new_stream_interceptor` discharging its contract): from `newStreamInterceptor`'s premises (the
server's member id, `lead`, cluster, `GoAttach` slots, `stopping` channel, configuration fields,
), the call returns an interceptor `is` with the `GoAttach` slots back, and the watch stream,
under the chain `[im, is]` (grpc-prometheus's `im` still assumed transparent), meets what the
single-process start takes for it (`grpc.start'`; phase 7's switch, SW1: until then a gRPC server
built with the chain and the `Watch` stream registered served the method). -/
theorem etcd_watch_served_etcd_chain (p : Loc) (R : WSrv GF) (W : SrvW GF)
    (im : GoFunc) (γr : ReadNames)
    (hγ : W.γm = R.E.γ) (Htb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders)
    (HL : srvLevels (GF := GF))
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true)
    (s c ch : Loc) (mid tm et : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗ srvClusterAddr s ↦□ c ∗
        membership.isRaftCluster c ∗ membership.localKept c ∗
        srvGoRes s ∗ srvLgReader s ∗ srvStoppingAddr s ↦□ ch ∗ stopChan ch ∗
        cfgTickMsAddr (srvCfgAddr s) ↦□ tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ et }}
      (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newStreamInterceptor))
        (Val #s))
    {{ (is : GoFunc), RET #is; srvGoRes s ∗ srvLgReader s ∗
        (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
          isWatchServer p R ∗ srvWOk W R.wsl wsN ∗ srvStreamInterceptorOk im iprop(True) ∗
          srvRevokeBuilt R.s R.E ∗ srvRunPool R.s R.E γr -∗
          □ [∗list] m ∈ [watchMethod p R W], grpcStreamRunOk #m.handler m.srv [im, is] m.Up m.spec ∗
            □ ∀ md γs, m.spec md γs (m.dn md γs)) }} := by
  iintro %Φ ⟨#Hpkg, -, Hpre⟩ HΦ
  wp_apply (new_stream_interceptor s c ch mid tm et) $$ [Hpre] as %is ⟨#His, Hgr, Hlg⟩
  · icases Hpre with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11⟩
    iframe
    ipureintro
    have := Htb; rw [sync.rwmutex.actualMaxReaders_unseal] at this; omega
  iapply HΦ
  iframe Hgr Hlg
  iintro ⟨#Hpb, #Hws, HW, #Him, Hb, Hrp⟩
  iapply (etcd_watch_served_chain p R W im is γr hγ Htb HL hset)
  iframe #
  iframe

end watch_wire

/-! ## The lease reads at the gRPC level (`notes/lease-grpc-plan.md`, 2026-11-01)

`LeaseServer.LeaseTimeToLive` and `LeaseServer.LeaseLeases` (linked, over the contract
`raftLeaseRead`), and the contract discharged from the server's linked `EtcdServer.LeaseTimeToLive`
and `EtcdServer.LeaseLeases` at `S := E.RD ∗ levelTok 0` and the store's reader;
the two specs' bounds premises are the discharge's. Both handler proofs rest on a `sorry` (Go's
second `errors.Is(err, ErrLeaseNotFound)` answering differently from the first), pending
Perennial's change (`notes/perennial-changes.md`, "`errors.Is` answers the same twice"). -/

section leaseRead
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

theorem leaseTimeToLive_handler :
    EtcdGrove.v3rpc.LeaseServer.LeaseTimeToLive.spec (GF := GF) (hG := hG) :=
  LeaseServer.wp_LeaseTimeToLive

theorem leaseLeases_handler :
    EtcdGrove.v3rpc.LeaseServer.LeaseLeases.spec (GF := GF) (hG := hG) :=
  LeaseServer.wp_LeaseLeases

/-- **The lease-read contract, discharged** (`raftLeaseRead_of_server` at the linked results), under
the deployment premise `leasePeersOk` (the trust-boundary `leaseTimeToLive`'s). -/
theorem raftLeaseRead_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γl : GName) (cs ms : w64) (hT : threadBound GF ≤ 2 ^ 30 - 1) (hR : receiptBound GF ≤ 2 ^ 62)
    (hP : leasePeersOk) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthAt s E ∗
        srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ lease.lessorRdPool γl ∗ srvHeaderFacts s cs ms ⊢
      raftLeaseRead s E γl iprop(E.RD ∗ levelTok 0)
        (mvcc.api.mvccReaders E.γ 1) :=
  raftLeaseRead_of_server EtcdServer.wp_LeaseTimeToLive EtcdServer.wp_LeaseLeases
    s E ρ γr γl cs ms hT hR hP

/-- **The grant contract at the lessor's history, discharged** (`lessorGrantOkLM_of_server` at the
linked `EtcdServer.LeaseGrant`; the lease-grant plan's 2.4), in a cluster that grants leases, in the
monotone lease mode (the lease-expiry plan's X2, 2026-11-04: `lease.srvInv … .mono`). (Auth-lease S4,
the C5′ merge, 2026-11-16: at the environment's auth mode; until then `lessorGrantOkL_server`, with
auth off.) -/
theorem lessorGrantOkLM_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (h : srvGrantsLeases E ρ) (hlm : ρ.rd.kv.lm ≠ .revocable) (on : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      lease.srvInv on s E .mono ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkLM E.authOn s E ρ S :=
  lessorGrantOkLM_of_server EtcdServer.wp_LeaseGrant s E ρ S h hlm on

/-- **The grant contract at the mode-free fact, in the environment's auth mode, discharged**
(auth-lease S3c, Draft §7.3; `lessorGrantOkLive_of_server` at the linked `EtcdServer.LeaseGrant`):
the server's view at `E.authOn`, the contract `lessorGrantOkGM E.authOn` (the client's update passed
through, the result at the request context's token). -/
theorem lessorGrantOkLiveM_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (R : w64 × w64 → Prop) (hR : ∀ m, R m → ρ.rd.kv.lm = .revocable → m.2 = W64 0)
    (h : srvGrantsLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkGM E.authOn s E ρ S (grantLiveG E) R :=
  lessorGrantOkLive_of_server EtcdServer.wp_LeaseGrant s E ρ S h R hR

/-- **The revoke contract, in the environment's auth mode, discharged** (auth-lease S3c, Draft §7.3;
`lessorRevokeOk_of_server` at the linked `EtcdServer.LeaseRevoke`), in a cluster that revokes leases. -/
theorem lessorRevokeOkM_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (h : srvRevokesLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorRevokeOkM E.authOn s E ρ S :=
  lessorRevokeOk_of_server EtcdServer.wp_LeaseRevoke s E ρ S h

/-- **The server's header fields, from its request side** (`srvHeaderFacts_of_reqM`: the discharge's
`srvHeaderFacts` premise needs no source of its own). -/
theorem srvHeaderFacts_server (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) on s E ρ ⊢ ∃ cs ms : w64, srvHeaderFacts s cs ms :=
  srvHeaderFacts_of_reqM on s E ρ

end leaseRead

/-! ## The lease keep-alive stream at the gRPC level (`notes/lease-keepalive-plan.md`, 2026-11-01)

`LeaseServer.LeaseKeepAlive` (linked, over the contract `raftLeaseRenew`: the `j`th response answers
the `j`th request and, unless its TTL is `0`, carries the renewal's key check at the request's ghost
bounds for the stream's token, `kaStreamSpec`), and the contract discharged from the server's linked
`EtcdServer.LeaseRenew` at `S' := E.RD ∗ levelTok 0 ∗ srvLgReader s ∗
srvReadReader s γr`, its peer round tripper `srvPeerRt s` (which `NewServer` exports, with
`srvLessorRd`). -/

section leaseKeepAlive
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

theorem leaseKeepAlive_handler :
    EtcdGrove.v3rpc.LeaseServer.LeaseKeepAlive.spec (GF := GF) (hG := hG) :=
  LeaseServer.wp_LeaseKeepAlive

/-- **The renewal contract, discharged** (`raftLeaseRenew_of_server` at the linked result). -/
theorem raftLeaseRenew_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γl : GName) (hT : threadBound GF ≤ 2 ^ 30 - 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthAt s E ∗
        srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ lease.lessorRdPool γl ∗ srvPeerRt s ⊢
      raftLeaseRenew s E γl
        iprop(E.RD ∗ levelTok 0 ∗ srvLgReader s ∗ srvReadReader s γr) :=
  raftLeaseRenew_of_server EtcdServer.wp_LeaseRenew s E ρ γr γl hT

end leaseKeepAlive

section clientPort
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [apply_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **Every row's specs hold** (the table's proved rows, each by its linked results). -/
theorem clientPortTable_ok :
    ∀ r ∈ v3rpc.clientPortTable (GF := GF) (hG := hG), r.status.proved = true → r.specs :=
  List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_doSerialize, _root_.Perennial.EtcdGrove.EtcdServer.wp_Range, _root_.Perennial.EtcdGrove.v3rpc.kvServer.wp_Range⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_doSerialize, _root_.Perennial.EtcdGrove.EtcdServer.wp_RangeStream, _root_.Perennial.EtcdGrove.v3rpc.kvServer.wp_RangeStream⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.wp_checkPutAuth, _root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Put, _root_.Perennial.EtcdGrove.EtcdServer.wp_Put⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_DeleteRange, _root_.Perennial.EtcdGrove.EtcdServer.wp_DeleteRange⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.wp_CheckTxnAuth, _root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Txn, _root_.Perennial.EtcdGrove.EtcdServer.wp_Txn⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.AuthAdmin.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.kvServer.wp_Compact, _root_.Perennial.EtcdGrove.EtcdServer.wp_Compact⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.serverWatchStream.wp_isWatchPermitted, _root_.Perennial.EtcdGrove.v3rpc.watchServer.wp_Watch⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_requireAuthInfo, _root_.Perennial.EtcdGrove.EtcdServer.wp_LeaseGrant, _root_.Perennial.EtcdGrove.v3rpc.LeaseServer.wp_LeaseGrant⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_requireAuthInfo, _root_.Perennial.EtcdGrove.apply.authApplierV3.wp_LeaseRevoke, _root_.Perennial.EtcdGrove.EtcdServer.wp_LeaseRevoke, _root_.Perennial.EtcdGrove.v3rpc.LeaseServer.wp_LeaseRevoke⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkLeaseTimeToLive, _root_.Perennial.EtcdGrove.EtcdServer.wp_LeaseTimeToLive, _root_.Perennial.EtcdGrove.v3rpc.LeaseServer.wp_LeaseTimeToLive⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkLeaseLeases, _root_.Perennial.EtcdGrove.EtcdServer.wp_LeaseLeases, _root_.Perennial.EtcdGrove.v3rpc.LeaseServer.wp_LeaseLeases⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkLeaseRenew, _root_.Perennial.EtcdGrove.EtcdServer.wp_LeaseRenew, _root_.Perennial.EtcdGrove.v3rpc.LeaseServer.wp_leaseKeepAlive, _root_.Perennial.EtcdGrove.v3rpc.LeaseServer.wp_LeaseKeepAlive⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkMembershipOperationPermission, _root_.Perennial.EtcdGrove.EtcdServer.wp_AddMember, _root_.Perennial.EtcdGrove.v3rpc.ClusterServer.wp_MemberAdd⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkMembershipOperationPermission, _root_.Perennial.EtcdGrove.EtcdServer.wp_RemoveMember, _root_.Perennial.EtcdGrove.v3rpc.ClusterServer.wp_MemberRemove⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkMembershipOperationPermission, _root_.Perennial.EtcdGrove.EtcdServer.wp_UpdateMember, _root_.Perennial.EtcdGrove.v3rpc.ClusterServer.wp_MemberUpdate⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_requireAuthInfo, _root_.Perennial.EtcdGrove.EtcdServer.wp_MemberList, _root_.Perennial.EtcdGrove.v3rpc.ClusterServer.wp_MemberList⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.EtcdServer.wp_checkMembershipOperationPermission, _root_.Perennial.EtcdGrove.EtcdServer.wp_promoteMember, _root_.Perennial.EtcdGrove.EtcdServer.wp_PromoteMember, _root_.Perennial.EtcdGrove.v3rpc.ClusterServer.wp_MemberPromote⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_Defragment⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_Snapshot⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_Hash⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_HashKV⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_MoveLeader⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_Downgrade⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_isPermitted, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_requireAuthInfo, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_Alarm⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_requireAuthInfo, _root_.Perennial.EtcdGrove.v3rpc.authMaintenanceServer.wp_Status⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.server_authenticate_on, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_Authenticate⟩,
    List.forall_mem_cons.2 ⟨fun _ => _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_AuthStatus,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_AuthEnable, _root_.Perennial.EtcdGrove.EtcdServer.wp_AuthEnable⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_AuthDisable, _root_.Perennial.EtcdGrove.EtcdServer.wp_AuthDisable⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserAdd, _root_.Perennial.EtcdGrove.EtcdServer.wp_UserAdd⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserDelete, _root_.Perennial.EtcdGrove.EtcdServer.wp_UserDelete⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserChangePassword⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserGrantRole, _root_.Perennial.EtcdGrove.EtcdServer.wp_UserGrantRole⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserRevokeRole, _root_.Perennial.EtcdGrove.EtcdServer.wp_UserRevokeRole⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserList, _root_.Perennial.EtcdGrove.EtcdServer.wp_UserList⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_RoleAdd, _root_.Perennial.EtcdGrove.EtcdServer.wp_RoleAdd⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_RoleDelete, _root_.Perennial.EtcdGrove.EtcdServer.wp_RoleDelete⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_RoleGrantPermission, _root_.Perennial.EtcdGrove.EtcdServer.wp_RoleGrantPermission⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_RoleRevokePermission, _root_.Perennial.EtcdGrove.EtcdServer.wp_RoleRevokePermission⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_Apply, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_RoleList, _root_.Perennial.EtcdGrove.EtcdServer.wp_RoleList⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_UserGet, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_UserGet, _root_.Perennial.EtcdGrove.EtcdServer.wp_UserGet⟩,
    List.forall_mem_cons.2 ⟨fun _ => ⟨_root_.Perennial.EtcdGrove.apply.authApplierV3.wp_RoleGet, _root_.Perennial.EtcdGrove.v3rpc.AuthServer.wp_RoleGet, _root_.Perennial.EtcdGrove.EtcdServer.wp_RoleGet⟩,
    List.forall_mem_cons.2 ⟨fun _ => trivial,
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_cons.2 ⟨fun h => absurd h (by decide),
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- **Every registration of `v3rpc.Server` has a row** of the client port's table: the six
services' methods and streams by name, grpc's health service's by its prefix. -/
theorem clientPort_covered (q pw ql pc pa pm : Loc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (h : v3rpc.serverRegsOk q pw ql pc pa pm regs sregs) :
    ∀ x ∈ regs ++ sregs, ∃ r ∈ v3rpc.clientPortTable (GF := GF) (hG := hG), r.covers x.1 := by
  obtain ⟨hrs, hsrs, rfl, rfl, hH, -⟩ := h
  have cov : ∀ (i : Nat) {n : GoString} (hi : i < (v3rpc.clientPortTable (GF := GF) (hG := hG)).length),
      ((v3rpc.clientPortTable (GF := GF) (hG := hG))[i]).isPrefix = false →
      ((v3rpc.clientPortTable (GF := GF) (hG := hG))[i]).key = n →
      ∃ r ∈ v3rpc.clientPortTable (GF := GF) (hG := hG), r.covers n := by
    intro i n hi hp hk
    refine ⟨_, List.getElem_mem hi, ?_⟩
    simp only [v3rpc.PortRow.covers, hp, Bool.false_eq_true, if_false, hk]
  have hlen : (v3rpc.clientPortTable (GF := GF) (hG := hG)).length = 50 := rfl
  have hE : ∀ x ∈ v3rpc.kvMethodRegs q ++ v3rpc.leaseRegs ql ++ v3rpc.clusterRegs pc ++
      v3rpc.authAllRegs pa ++ v3rpc.maintRegs pm ++
      [v3rpc.kvSReg q, v3rpc.watchSReg pw, v3rpc.leaseSReg ql, v3rpc.maintSReg pm],
      ∃ r ∈ v3rpc.clientPortTable (GF := GF) (hG := hG), r.covers x.1 := by
    simp only [v3rpc.kvMethodRegs, v3rpc.leaseRegs, v3rpc.clusterRegs, v3rpc.authAllRegs,
      v3rpc.maintRegs, v3rpc.kvSReg, v3rpc.watchSReg, v3rpc.leaseSReg, v3rpc.maintSReg,
      List.cons_append, List.nil_append, List.forall_mem_cons, List.forall_mem_nil, and_true]
    exact ⟨cov 0 (by rw [hlen]; decide) rfl rfl, cov 2 (by rw [hlen]; decide) rfl rfl, cov 3 (by rw [hlen]; decide) rfl rfl, cov 4 (by rw [hlen]; decide) rfl rfl, cov 5 (by rw [hlen]; decide) rfl rfl, cov 7 (by rw [hlen]; decide) rfl rfl, cov 8 (by rw [hlen]; decide) rfl rfl, cov 9 (by rw [hlen]; decide) rfl rfl, cov 10 (by rw [hlen]; decide) rfl rfl, cov 12 (by rw [hlen]; decide) rfl rfl, cov 13 (by rw [hlen]; decide) rfl rfl, cov 14 (by rw [hlen]; decide) rfl rfl, cov 15 (by rw [hlen]; decide) rfl rfl, cov 16 (by rw [hlen]; decide) rfl rfl, cov 27 (by rw [hlen]; decide) rfl rfl, cov 28 (by rw [hlen]; decide) rfl rfl, cov 26 (by rw [hlen]; decide) rfl rfl, cov 25 (by rw [hlen]; decide) rfl rfl, cov 29 (by rw [hlen]; decide) rfl rfl, cov 40 (by rw [hlen]; decide) rfl rfl, cov 34 (by rw [hlen]; decide) rfl rfl, cov 30 (by rw [hlen]; decide) rfl rfl, cov 31 (by rw [hlen]; decide) rfl rfl, cov 32 (by rw [hlen]; decide) rfl rfl, cov 33 (by rw [hlen]; decide) rfl rfl, cov 35 (by rw [hlen]; decide) rfl rfl, cov 41 (by rw [hlen]; decide) rfl rfl, cov 39 (by rw [hlen]; decide) rfl rfl, cov 36 (by rw [hlen]; decide) rfl rfl, cov 37 (by rw [hlen]; decide) rfl rfl, cov 38 (by rw [hlen]; decide) rfl rfl, cov 23 (by rw [hlen]; decide) rfl rfl, cov 24 (by rw [hlen]; decide) rfl rfl, cov 17 (by rw [hlen]; decide) rfl rfl, cov 19 (by rw [hlen]; decide) rfl rfl, cov 20 (by rw [hlen]; decide) rfl rfl, cov 21 (by rw [hlen]; decide) rfl rfl, cov 22 (by rw [hlen]; decide) rfl rfl, cov 1 (by rw [hlen]; decide) rfl rfl, cov 6 (by rw [hlen]; decide) rfl rfl, cov 11 (by rw [hlen]; decide) rfl rfl, cov 18 (by rw [hlen]; decide) rfl rfl, fun _ h => nomatch h⟩
  intro x hx
  have hx' : x ∈ v3rpc.kvMethodRegs q ++ v3rpc.leaseRegs ql ++ v3rpc.clusterRegs pc ++
      v3rpc.authAllRegs pa ++ v3rpc.maintRegs pm ++
      [v3rpc.kvSReg q, v3rpc.watchSReg pw, v3rpc.leaseSReg ql, v3rpc.maintSReg pm] ∨
      x ∈ hrs ++ hsrs := by
    rw [← List.mem_append]
    refine List.Perm.subset ?_ hx
    rw [List.perm_iff_count]
    intro a
    simp only [List.count_append, List.cons_append, List.nil_append, List.count_cons]
    omega
  rcases hx' with hx' | hx'
  · exact hE x hx'
  · refine ⟨_, List.getElem_mem (n := 42) (by rw [hlen]; decide), ?_⟩
    simp only [v3rpc.PortRow.covers]
    exact hH x hx'

/-- **Complete mediation on etcd's client port** (auth-mediation M1, `notes/auth-mediation-scope.md`
§2.2): `v3rpc.Server` registers exactly the six services' methods and streams and grpc's health
service's (`v3rpc.Server.spec`'s `serverRegsOk`); every one of them has a row of the client port's
table (`clientPortTable`: its access class and status, the Lock and Election services `embed`
registers excluded by name, with why); and the specs every row of a proved status names hold, each
the handler's or the guard's own spec as its `Link` proves it. What each row's specs mean (that the
handler acts only after the row's check, for the request's principal) is in the specs themselves,
reviewed per row; that a client reaches only these handlers on the client port (its HTTP side is
untranslated), and anything of the peer port, are outside the statement (§2.2, "What it does not
prove"). -/
theorem client_port_mediated :
    v3rpc.Server.spec (GF := GF) (hG := hG) ∧
    (∀ (q pw ql pc pa pm : Loc) (regs sregs : List (GoString × GoFunc × GoInterface)),
      v3rpc.serverRegsOk q pw ql pc pa pm regs sregs →
      ∀ x ∈ regs ++ sregs, ∃ r ∈ v3rpc.clientPortTable (GF := GF) (hG := hG), r.covers x.1) ∧
    (∀ r ∈ v3rpc.clientPortTable (GF := GF) (hG := hG), r.status.proved = true → r.specs) :=
  ⟨wp_Server, clientPort_covered, clientPortTable_ok⟩

end clientPort

end v3rpc

#print axioms Perennial.EtcdGrove.v3rpc.checkIntervals_nodup
#print axioms Perennial.EtcdGrove.v3rpc.check_gives_nodup
#print axioms Perennial.EtcdGrove.v3rpc.checkRequestOp_nonempty
#print axioms Perennial.EtcdGrove.v3rpc.checkTxnRequest_ok
#print axioms Perennial.EtcdGrove.v3rpc.put_handler
#print axioms Perennial.EtcdGrove.v3rpc.range_handler
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_handler
#print axioms Perennial.EtcdGrove.v3rpc.kvServer.wp_Txn
#print axioms Perennial.EtcdGrove.v3rpc.wp_NewKVServer
#print axioms Perennial.EtcdGrove.v3rpc.headerFillingRangeStream.wp_Send
#print axioms Perennial.EtcdGrove.v3rpc.kvServer.wp_RangeStream
#print axioms Perennial.EtcdGrove.v3rpc.wp_checkRangeStreamRequest
#print axioms Perennial.EtcdGrove.v3rpc.wp_togRPCError
#print axioms Perennial.EtcdGrove.v3rpc.put_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.range_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.txn_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.raftKV_server
#print axioms Perennial.EtcdGrove.v3rpc.raftKV_serverM
#print axioms Perennial.EtcdGrove.v3rpc.put_end_to_endM
#print axioms Perennial.EtcdGrove.v3rpc.put_end_to_endML
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_end_to_endM
#print axioms Perennial.EtcdGrove.v3rpc.range_end_to_endM
#print axioms Perennial.EtcdGrove.v3rpc.txn_end_to_endM
#print axioms Perennial.EtcdGrove.v3rpc.txn_end_to_endML
#print axioms Perennial.EtcdGrove.v3rpc.put_end_to_end_model
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_end_to_end_model
#print axioms Perennial.EtcdGrove.v3rpc.etcdModelOfServer
#print axioms Perennial.EtcdGrove.v3rpc.etcd_model_of_server
#print axioms Perennial.EtcdGrove.v3rpc.etcdState_of_range
#print axioms Perennial.EtcdGrove.v3rpc.etcdState_of_txnRead
#print axioms Perennial.EtcdGrove.v3rpc.etcdReached_of_hdr
#print axioms Perennial.EtcdGrove.v3rpc.revToken_of_put
#print axioms Perennial.EtcdGrove.v3rpc.watch_server
#print axioms Perennial.EtcdGrove.v3rpc.new_watch_server
#print axioms Perennial.EtcdGrove.v3rpc.watch_registered_authorized
#print axioms Perennial.EtcdGrove.v3rpc.watchStreamSpec_step
#print axioms Perennial.EtcdGrove.v3rpc.srvStep_of_watch
#print axioms Perennial.EtcdGrove.v3rpc.watch_handler
#print axioms Perennial.EtcdGrove.v3rpc.watch_streamHandlerOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_watchMethodOk
#print axioms Perennial.EtcdGrove.v3rpc.etcd_watch_served
#print axioms Perennial.EtcdGrove.v3rpc.etcd_watch_served_chain
#print axioms Perennial.EtcdGrove.v3rpc.new_stream_interceptor
#print axioms Perennial.EtcdGrove.v3rpc.etcd_watch_served_etcd_chain
#print axioms Perennial.EtcdGrove.v3rpc.authEnable_end_to_end_on
#print axioms Perennial.EtcdGrove.v3rpc.userAdd_end_to_end_on
#print axioms Perennial.EtcdGrove.v3rpc.roleAdd_end_to_end_on
#print axioms Perennial.EtcdGrove.v3rpc.userGrantRole_end_to_end_on
#print axioms Perennial.EtcdGrove.v3rpc.roleGrantPermission_end_to_end_on
#print axioms Perennial.EtcdGrove.v3rpc.etcd_auth_served
#print axioms Perennial.EtcdGrove.v3rpc.leaseTimeToLive_handler
#print axioms Perennial.EtcdGrove.v3rpc.leaseLeases_handler
#print axioms Perennial.EtcdGrove.v3rpc.raftLeaseRead_server
#print axioms Perennial.EtcdGrove.v3rpc.srvHeaderFacts_server
#print axioms Perennial.EtcdGrove.v3rpc.leaseKeepAlive_handler
#print axioms Perennial.EtcdGrove.v3rpc.raftLeaseRenew_server
#print axioms Perennial.EtcdGrove.v3rpc.client_port_mediated

end EtcdGrove
end Perennial
