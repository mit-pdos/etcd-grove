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
(`ServerKV.lean`: `srvKVAns`, `raftKV_of_server`, from the linked `EtcdServer.Put`/`DeleteRange`):
* **`put_end_to_end`**, **`deleteRange_end_to_end`**: the gRPC handler's `(resp, nil)` is the
  apply thread's application of the request at the log the entry met (`putAppliedOk`/
  `deleteAppliedOk`: `applyStep … (.dispatched (.applied l false) skip)`, the outcome's answer,
  `idxCert` of the log after) with the header filled (`hdrFilled`, `hdrRevOut`); an error is the
  apply's or the proposal's (`putErrOk`/`deleteErrOk`). Premises: `isServerReq` (the raft contract,
  the wait registry, the ids, the auth store's request side), the `*kvServer` (`kvServerAt`), and
  the read side's conjuncts of `raftKV` (unit 3b's).
* **`put_end_to_end_model`**, **`deleteRange_end_to_end_model`** (pure): through the
  uber-applier's chain, such a put appends the client's put change to the log (a delete commits
  its changes), no alarm raised.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckNodup
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Wire

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
(`raftKV_of_server`, from the server's linked `EtcdServer.Put`/`DeleteRange`/`Range`/`Txn` and
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-- **The server's contract, discharged** (`raftKV_of_server` at the linked results). -/
theorem raftKV_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      raftKV s (srvKVAns s E ρ γr c) :=
  raftKV_of_server EtcdServer.wp_Put EtcdServer.wp_DeleteRange EtcdServer.wp_Range
    EtcdServer.wp_Txn EtcdServer.wp_KV mvcc.store.wp_Rev EtcdServer.wp_Cluster
    membership.RaftCluster.wp_ID EtcdServer.wp_MemberID EtcdServer.wp_Term EtcdServer.wp_Leader
    s E ρ γr c

/-- **`put_end_to_end`** (see the section header). -/
theorem put_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ txn.putRequestIs r o }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Put")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match putCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
              hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗ srvRdCall s E γr c ∗
              putAppliedOk s E o resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ putErrOk s E ρ o e) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #Hr⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Put p s (srvKVAns s E ρ γr c) cid mid n ctx r o) $$ [Hc Hc0]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0
  inext
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : putCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    iexact Hpost

/-- **`deleteRange_end_to_end`** (as `put_end_to_end`, for `DeleteRange`: the answer's request is
the one the proposed data decode to, `deleteAppliedOk`). -/
theorem deleteRange_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ txn.deleteRangeRequestIs r o }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"DeleteRange")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match deleteCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗
              srvRdCall s E γr c ∗ deleteAppliedOk s E o resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ deleteErrOk s E ρ o e) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #Hr⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_DeleteRange p s (srvKVAns s E ρ γr c) cid mid n ctx r o) $$ [Hc Hc0]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0
  inext
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : deleteCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    iexact Hpost

/-- **`range_end_to_end`**: the gRPC `Range`'s `(resp, nil)` is the txn package's range at a
certified log of at least two revisions (`rangeAnsOk`: `rangeResult` of the server's selection
at the revision read, the header's revision the log's last), read after the read index unless
serializable (`readLogOk γr c log`: the applied index reached the committed index `c` the caller
knew of, and `log` extends the log applied through an index at least `c`; unit 4b), the header
filled; the id credit and the reader slot back. -/
theorem range_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ txn.rangeRequestIs r o }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Range")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match rangeCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗
              srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s ∗
              rangeAnsOk E γr c o resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ _e : GoInterface,
            srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗ srvLeadTimeReader s) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #Hr⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Range p s (srvKVAns s E ρ γr c) cid mid n ctx r o) $$ [Hc Hc0]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0
  inext
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : rangeCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    iexact Hpost

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
    (ts es : List ReqOp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ txnReqIs r cs ts es ∗ txnReqWire r ts es ∗
        ⌜txnInModel cs ts es⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Txn")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match txnAllCheck (sint.Z n) cs ts es with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗
              srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
              ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
                if txn.txnReadonly t then iprop(idCred ρ.ids 1 ∗ txnReadAns E γr c t resp rv)
                else txnAppliedAns E t resp rv) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface,
            srvRdCall s E γr c ∗ srvLeadTimeReader s ∗
            ∃ t, ⌜txnModelOf cs ts es = some t⌝ ∗
              if txn.txnReadonly t then idCred ρ.ids 1 else txnErrOk E ρ t e) }} := by
  iintro %Φ ⟨#Pv, #Ps, #Hsrv, #Hsrd, #Hat, Hc, Hc0, #Hr, #Hw, %Hin⟩ HΦ
  ihave #HKV := raftKV_server s E ρ γr c $$ []
  · iframe #
  ihave #Hks := kvServerIs_of_at p s _ cid mid n $$ [$Hat $HKV]
  iapply (kvServer.wp_Txn p s (srvKVAns s E ρ γr c) cid mid n
    ctx r cs ts es) $$ [Hc Hc0]
  · iframe #; simp only [srvKVAns]; iframe Hc Hc0; ipureintro; exact Hin
  inext
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : txnAllCheck (sint.Z n) cs ts es with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    iexact Hpost

/-- **What a successful gRPC `Put` applied** (pure; with `put_end_to_end`'s `putAppliedOk`):
through the uber-applier's chain `alarmChain ns cr`, the put was applied by the client model:
the log after is the log the entry met with the put's one change (`putChangeOf`, the client's
`putTxnOp`), neither the corrupt nor the space alarm raised (`put_applied_model`). -/
theorem put_end_to_end_model (o : OpFull) (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
    (l : mvcc.Log) (skip ns cr : Bool) (hc : x.chain = apply.alarmChain ns cr)
    (h : apply.applyStep (apply.withHeader (irrPut o) hm) true x x'
      (.dispatched (.applied l false) skip)) :
    x'.log = x.log ++ [[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter x.log))]] ∧
      ns = false ∧ cr = false := by
  obtain ⟨hlog, ha⟩ := put_applied_model o hm x x' _ skip ns cr hc h
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
`deleteAppliedOk`): through `alarmChain ns cr`, the delete `op'` of the decoded request was
applied by the client model: the log after commits its changes (`delChanges`, none if nothing
matched), the corrupt alarm not raised (`deleteRange_applied_model`). -/
theorem deleteRange_end_to_end_model (op op' : OpFull) (hm : apply.HeaderModel)
    (rq' : apply.IRRModel) (x x' : apply.ApplyKV) (l : mvcc.Log) (skip ns cr : Bool)
    (hc : x.chain = apply.alarmChain ns cr)
    (hw : irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq')
    (hop : rq'.deleteRange = some op')
    (h : apply.applyStep rq' true x x' (.dispatched (.applied l false) skip)) :
    x'.log = mvcc.commitLog x.log (txn.delChanges (mvcc.stateAfter x.log) op') ∧ cr = false := by
  obtain ⟨hlog, ha⟩ := deleteRange_applied_model op op' hm rq' x x' _ skip ns cr hc hw hop h
  simp only [apply.Outcome.logAfter] at hlog
  unfold apply.alarmDelete at ha
  cases cr <;> simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_or] at ha
  unfold apply.deleteModel at ha
  rcases ha with ha | ⟨-, ha⟩
  · cases ha; exact ⟨hlog, rfl⟩
  · cases ha

end endToEnd

/-! ## The vertical slice, unit V1 (2026-10-13): the clients' model implemented; the wire

`ClientModel.lean`: the clients' class `EtcdModel` (`cache/v3/EtcdModel.lean`, fourteen axioms
until V1) instantiated by the server (`etcdModelOfServer`), each law a theorem; what the
server's answers give the model (`etcdState_of_range`, `etcdState_of_txnRead`,
`etcdReached_of_cert`, `revToken_of_put`). `Wire.lean`: the generated gRPC KV stub's contract
(four axioms, `kVClient.wp_Range`, ..., in `Link.lean`), each the server's end-to-end theorem
transported to the client, and `isKVClient`, proved of the stub from the connection
(`kvclient_of_conn`). -/

section slice
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.api.v3 mvcc txn

/-- **The server implements the clients' model of etcd** (`etcdModelOfServer`, every law a
theorem): its predicates are the server's facts about its certified log (`srvEtcdState`,
`srvReachedAt`, `srvStep`) and the revisions' tokens the apply thread mints (`revTok`). -/
theorem etcd_model_of_server (E : apply.AEnv GF) :
    ∃ M : EtcdModel GF, M.etcdState = srvEtcdState E ∧ M.etcdReachedAt = srvReachedAt E ∧
      M.etcdRevToken = revTok E ∧ M.EtcdStep = srvStep E :=
  ⟨etcdModelOfServer E, rfl, rfl, rfl, rfl⟩

/-- **A header's revision is reached**: the revision of a certified log (every answer's header
revision is one: `rangeAnsOk`'s, `txnReadAns`'s, the writes' `idxCert` of the log after) gives
`etcdReached` in the server's model (`etcdReached_of_cert`). -/
theorem etcdReached_of_hdr (E : apply.AEnv GF) (log : mvcc.Log) (r : w64)
    (h : sint.Z r < log.length) :
    mvcc.idxCert E.γ.idx log ⊢ etcdReached (EM := etcdModelOfServer E) r :=
  etcdReached_of_cert E log r h

/-- **What a successful `Range` gives the clients' model** (`range_end_to_end`'s `rangeAnsOk`):
the header's revision `r` is the certified log's last (reached), and etcd's state at `r` under any
prefix is the log's last state restricted to it; the response is the txn package's range at that
log (`txn.rangeResult`; with `rangeSel_underPfx`, its selection of a range under the prefix is the
restricted state's). -/
theorem etcdState_of_range (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (o : OpFull)
    (resp : Loc) (r : w64) (pfx : GoString) :
    storeSmall E.γ ∗ rangeAnsOk E γr c o resp r ⊢
      ∃ log : Log, ⌜r = W64 ((log.length : Int) - 1) ∧ 2 ≤ log.length ∧
          log.length + 3 ≤ 2 ^ 63⌝ ∗
        □ etcdState (self := etcdModelOfServer E) r pfx (underPfx pfx (stateAfter log)) ∗
        ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ ∗
        etcdReached (EM := etcdModelOfServer E) r ∗
        (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
        txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true := by
  iintro ⟨#Hsm, Hok⟩
  iunfold rangeAnsOk at Hok
  icases Hok with ⟨%log, #H, %Hl, Hlin, Hres⟩
  obtain ⟨h2, h3, rfl⟩ := Hl
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave ⟨#Hst, %Hwf⟩ := etcdState_of_cert_last E log pfx h2 h3 $$ [$Hsm $H]
  iexists log
  iframe Hst Hlin Hres
  isplitr
  · ipureintro; exact ⟨rfl, h2, h3⟩
  isplitr
  · ipureintro; exact Hwf
  iapply etcdReached_of_cert E log _ (by omega) $$ H

/-- **What a successful read-only `Txn` gives the clients' model** (`txn_end_to_end`'s
`txnReadAns`): as `etcdState_of_range`, the response the server's run of the transaction at the
log's last revision. -/
theorem etcdState_of_txnRead (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (t : TxnModel)
    (resp : Loc) (r : w64) (pfx : GoString) :
    storeSmall E.γ ∗ txnReadAns E γr c t resp r ⊢
      ∃ log : Log, ⌜r = W64 ((log.length : Int) - 1) ∧ 2 ≤ log.length ∧
          log.length + 3 ≤ 2 ^ 63⌝ ∗
        □ etcdState (self := etcdModelOfServer E) r pfx (underPfx pfx (stateAfter log)) ∗
        ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ ∗
        etcdReached (EM := etcdModelOfServer E) r ∗
        (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
        txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
          (txn.srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).1
          (txn.srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).2.2 := by
  iintro ⟨#Hsm, Hok⟩
  iunfold txnReadAns at Hok
  icases Hok with ⟨%log, #H, %Hl, Hlin, Hres⟩
  obtain ⟨h2, h3, rfl⟩ := Hl
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave ⟨#Hst, %Hwf⟩ := etcdState_of_cert_last E log pfx h2 h3 $$ [$Hsm $H]
  iexists log
  iframe Hst Hlin Hres
  isplitr
  · ipureintro; exact ⟨rfl, h2, h3⟩
  isplitr
  · ipureintro; exact Hwf
  iapply etcdReached_of_cert E log _ (by omega) $$ H

/-- **What a successful `Put` gives the clients' model** (`put_end_to_end`'s `putAppliedOk`, the
client's `putApplied`): the token of the header's revision `r` (`etcdRevToken r`: the apply thread
minted it when the put's revision committed) and that etcd has reached `r`. -/
theorem revToken_of_put (E : apply.AEnv GF) (o : OpFull) (resp : Loc) (r : w64) :
    putApplied E o resp r ⊢
      etcdRevToken (self := etcdModelOfServer E) r ∗ etcdReached (EM := etcdModelOfServer E) r := by
  iintro Hok
  iunfold putApplied at Hok
  icases Hok with ⟨%hm, %x, %x', %l, %skip, %Hp, -, #Hcert, HMint⟩
  obtain ⟨Hstep, rfl⟩ := Hp
  obtain ⟨cs, hcs⟩ := put_appended o hm x x' l skip Hstep
  ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
  iunfold revMinted at HMint
  icases HMint with (%He | ⟨%cs', %He, Ht⟩)
  · rw [hcs] at He
    exact absurd (congrArg List.length He) (by simp)
  isplitl [Ht]
  · rw [etcdModelOfServer_etcdRevToken]
    iexact Ht
  iapply etcdReached_of_cert E x'.log _ (by rw [hcs] at Hlen ⊢; simp at Hlen ⊢; word) $$ Hcert

/-- **The generated stub is a `pb.KVClient` talking to the server** (`isKVClient`): `&kVClient{cc}`
with `cc` connected to the server's KV service (`connectedTo`), from the stub's four axioms. -/
theorem kvclient_of_conn (c : Loc) (cc : GoInterface) (p s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid n : w64) :
    structFieldRef etcdserverpb.kVClient go!"cc" c ↦□ cc ∗ connectedTo cc p s E ρ γr cid mid n ⊢
      isKVClient ⟨go.GoType.PointerType etcdserverpb.kVClient.ty, #c⟩ E ρ γr cid mid n := by
  iintro ⟨#Hcc, #Hconn⟩
  unfold isKVClient
  isplitl
  · imodintro
    iintro %ctx %cd %inp %o %opts !> %Φ ⟨Hpkg, Hctx, Hr⟩ HΦ
    iapply (kVClient.wp_Range c cc p s E ρ γr cid mid n ctx cd inp o opts) $$ [Hpkg Hctx Hr] HΦ
    iframe Hpkg Hctx Hr Hcc Hconn
  isplitl
  · imodintro
    iintro %ctx %cd %inp %o %opts !> %Φ ⟨Hpkg, Hctx, Hr⟩ HΦ
    iapply (kVClient.wp_Put c cc p s E ρ γr cid mid n ctx cd inp o opts) $$ [Hpkg Hctx Hr] HΦ
    iframe Hpkg Hctx Hr Hcc Hconn
  isplitl
  · imodintro
    iintro %ctx %cd %inp %o %opts !> %Φ ⟨Hpkg, Hctx, Hr⟩ HΦ
    iapply (kVClient.wp_DeleteRange c cc p s E ρ γr cid mid n ctx cd inp o opts) $$
      [Hpkg Hctx Hr] HΦ
    iframe Hpkg Hctx Hr Hcc Hconn
  · imodintro
    iintro %ctx %cd %inp %cs %ts %es %opts !> %Φ ⟨Hpkg, Hctx, Hr, Hw, %Hm⟩ HΦ
    iapply (kVClient.wp_Txn c cc p s E ρ γr cid mid n ctx cd inp cs ts es opts) $$
      [Hpkg Hctx Hr Hw] HΦ
    iframe Hpkg Hctx Hr Hw Hcc Hconn
    ipureintro; exact Hm

end slice

end v3rpc

#print axioms Perennial.EtcdGrove.v3rpc.checkIntervals_nodup
#print axioms Perennial.EtcdGrove.v3rpc.check_gives_nodup
#print axioms Perennial.EtcdGrove.v3rpc.intervalsOkCheckStmt_holds
#print axioms Perennial.EtcdGrove.v3rpc.intervalsOkNoKeysStmt_false
#print axioms Perennial.EtcdGrove.v3rpc.checkRequestOp_nonempty
#print axioms Perennial.EtcdGrove.v3rpc.checkTxnRequest_ok
#print axioms Perennial.EtcdGrove.v3rpc.put_handler
#print axioms Perennial.EtcdGrove.v3rpc.range_handler
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_handler
#print axioms Perennial.EtcdGrove.v3rpc.kvServer.wp_Txn
#print axioms Perennial.EtcdGrove.v3rpc.wp_NewKVServer
#print axioms Perennial.EtcdGrove.v3rpc.headerFillingRangeStream.wp_Send
#print axioms Perennial.EtcdGrove.v3rpc.wp_checkRangeStreamRequest
#print axioms Perennial.EtcdGrove.v3rpc.wp_togRPCError
#print axioms Perennial.EtcdGrove.v3rpc.put_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.range_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.txn_end_to_end
#print axioms Perennial.EtcdGrove.v3rpc.raftKV_server
#print axioms Perennial.EtcdGrove.v3rpc.put_end_to_end_model
#print axioms Perennial.EtcdGrove.v3rpc.deleteRange_end_to_end_model
#print axioms Perennial.EtcdGrove.v3rpc.etcdModelOfServer
#print axioms Perennial.EtcdGrove.v3rpc.etcd_model_of_server
#print axioms Perennial.EtcdGrove.v3rpc.etcdState_of_range
#print axioms Perennial.EtcdGrove.v3rpc.etcdState_of_txnRead
#print axioms Perennial.EtcdGrove.v3rpc.etcdReached_of_hdr
#print axioms Perennial.EtcdGrove.v3rpc.revToken_of_put
#print axioms Perennial.EtcdGrove.v3rpc.kvclient_of_conn

end EtcdGrove
end Perennial
