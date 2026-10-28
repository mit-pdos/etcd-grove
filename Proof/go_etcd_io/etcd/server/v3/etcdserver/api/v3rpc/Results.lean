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

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchBound
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.GuardBound
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckNodup
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-- **The server's contract, discharged** (`raftKV_of_server` at the linked results). -/
theorem raftKV_server (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (F : mvcc.Log) (d : v3rpc.KVDep GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ⊢
      raftKV s (srvKVAns s E ρ γr c F d) :=
  raftKV_of_server EtcdServer.wp_Put EtcdServer.wp_DeleteRange EtcdServer.wp_Range
    EtcdServer.wp_Txn EtcdServer.wp_KV mvcc.store.wp_Rev EtcdServer.wp_Cluster
    membership.RaftCluster.wp_ID EtcdServer.wp_MemberID EtcdServer.wp_Term EtcdServer.wp_Leader
    s E ρ γr c F d

/-- **`put_end_to_end`** (see the section header). -/
theorem put_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : v3rpc.KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ mvcc.idxCert E.γ.idx F ∗ txn.putRequestIs r o ∗ kvDepOwn ρ γr d ∗
        ⌜kvDepPre d (.put o)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Put")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match putCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ hdrFilled h cid mid ∗
              hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗ srvRdCall s E γr c ∗
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
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : putCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    iexact Hpost

/-- **`deleteRange_end_to_end`** (as `put_end_to_end`, for `DeleteRange`: the answer's request is
the one the proposed data decode to, `deleteAppliedOk`). -/
theorem deleteRange_end_to_end (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ mvcc.idxCert E.γ.idx F ∗ txn.deleteRangeRequestIs r o ∗
        kvDepOwn ρ γr d ∗ ⌜kvDepPre d (.deleteRange o)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"DeleteRange")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match deleteCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗
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
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : deleteCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
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
    (c : w64) (cid mid n : w64) (ctx : GoInterface) (r : Loc) (o : OpFull) (F : mvcc.Log) (d : KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ mvcc.idxCert E.γ.idx F ∗ txn.rangeRequestIs r o ∗
        kvDepOwn ρ γr d ∗ ⌜kvDepPre d (.range o)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Range")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match rangeCheck o with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗
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
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : rangeCheck o with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
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
    (ts es : List ReqOp) (F : mvcc.Log) (d : KVDep GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServerAt p s (srvKVAns s E ρ γr c F d) cid mid n ∗
        srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ mvcc.idxCert E.γ.idx F ∗ txnReqIs r cs ts es ∗ txnReqWire r ts es ∗
        ⌜txnInModel cs ts es⌝ ∗ kvDepOwn ρ γr d ∗ ⌜kvDepPre d (.txn cs ts es)⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer.ty @!! go!"Txn")) (Val #ctx))
        (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        match txnAllCheck (sint.Z n) cs ts es with
        | some e => checkOut e resp err ∗ srvCall s ρ ctx ∗ srvRdCall s E γr c ∗ kvDepOwn ρ γr d
        | none =>
          (⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
              structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗
              hdrFilled h cid mid ∗ hdrRevOut (mvcc.storeReader E.s E.γ) h rv rv' ∗
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
  iintro %resp %err Hpost
  iapply HΦ
  cases hc : txnAllCheck (sint.Z n) cs ts es with
  | some e =>
    simp only [hc, srvKVAns]
    icases Hpost with ⟨Hco, Hc, Hc0, Hdep', -⟩
    iframe
  | none =>
    simp only [hc, kvOut, srvKVAns]
    iexact Hpost

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
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ ⌜r ≠ null⌝ ∗ adminPreOn s E ρ ctx cd F }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"AuthEnable"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ irrAuthEnable F (adminQh ρ.kv irrAuthEnable)
          etcdserverpb.AuthEnableResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, %Hr, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"AuthEnable" (GoInterface.ok ctx) r
      iprop(⌜r ≠ null⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ irrAuthEnable F (adminQh ρ.kv irrAuthEnable) etcdserverpb.AuthEnableResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨%Hr', HP'⟩ HΨ
    iapply (server_auth_enable_on s E ρ ctx cd r F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_AuthEnable p s ctx r iprop(⌜r ≠ null⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ irrAuthEnable F (adminQh ρ.kv irrAuthEnable) etcdserverpb.AuthEnableResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **`AuthServer.RoleAdd` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the handler's
contract discharged by the server's `RoleAdd` with auth on (`server_role_add_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem roleAdd_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (name : GoString) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ apply.authRoleAddIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleAdd"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name))
          etcdserverpb.AuthRoleAddResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hreq, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"RoleAdd" (GoInterface.ok ctx) r
      iprop(apply.authRoleAddIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name)) etcdserverpb.AuthRoleAddResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨#Hreq', %Hn', HP'⟩ HΨ
    iapply (server_role_add_on s E ρ ctx cd r name F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_RoleAdd p s ctx r iprop(apply.authRoleAddIs r name ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrRoleAdd name) F (adminQh ρ.kv (irrRoleAdd name)) etcdserverpb.AuthRoleAddResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **`AuthServer.UserGrantRole` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the handler's
contract discharged by the server's `UserGrantRole` with auth on (`server_user_grant_role_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem userGrantRole_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (user role : GoString) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ apply.authUserGrantRoleIs r (user, role) ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGrantRole"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ (irrUserGrantRole user role) F (adminQh ρ.kv (irrUserGrantRole user role))
          etcdserverpb.AuthUserGrantRoleResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hreq, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"UserGrantRole" (GoInterface.ok ctx) r
      iprop(apply.authUserGrantRoleIs r (user, role) ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrUserGrantRole user role) F (adminQh ρ.kv (irrUserGrantRole user role)) etcdserverpb.AuthUserGrantRoleResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨#Hreq', %Hn', HP'⟩ HΨ
    iapply (server_user_grant_role_on s E ρ ctx cd r user role F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_UserGrantRole p s ctx r iprop(apply.authUserGrantRoleIs r (user, role) ∗ ⌜user.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrUserGrantRole user role) F (adminQh ρ.kv (irrUserGrantRole user role)) etcdserverpb.AuthUserGrantRoleResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **`AuthServer.RoleGrantPermission` with auth on, end to end** (the auth plan's E3z, 2026-10-27): the handler's
contract discharged by the server's `RoleGrantPermission` with auth on (`server_role_grant_permission_on`): the handler's `(resp, nil)` is
the request applied at the committed prefix before its entry, its admin step succeeding there
(`adminOutOn`'s `appliedOkM true`, `adminDoneM`); its error, `togRPCError`'s of the apply thread's
or the proposal's (`authWrapOut`). -/
theorem roleGrantPermission_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (name : GoString) (w : Option auth.PermW) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ apply.authRoleGrantPermissionIs r (name, w) ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleGrantPermission"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (adminOutOn s E ρ (irrRoleGrantPermission name w) F (adminQh ρ.kv (irrRoleGrantPermission name w))
          etcdserverpb.AuthRoleGrantPermissionResponse.ty) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hreq, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"RoleGrantPermission" (GoInterface.ok ctx) r
      iprop(apply.authRoleGrantPermissionIs r (name, w) ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrRoleGrantPermission name w) F (adminQh ρ.kv (irrRoleGrantPermission name w)) etcdserverpb.AuthRoleGrantPermissionResponse.ty) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨#Hreq', %Hn', HP'⟩ HΨ
    iapply (server_role_grant_permission_on s E ρ ctx cd r name w F) $$ [HP'] HΨ
    iframe # HP'
    try (ipureintro; assumption)
  iapply (AuthServer.wp_RoleGrantPermission p s ctx r iprop(apply.authRoleGrantPermissionIs r (name, w) ∗ ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F)
      (adminOutOn s E ρ (irrRoleGrantPermission name w) F (adminQh ρ.kv (irrRoleGrantPermission name w)) etcdserverpb.AuthRoleGrantPermissionResponse.ty)) $$ [HP] HΦ
  iframe # HP
  try (ipureintro; assumption)

/-- **What `AuthServer.UserAdd` with auth on answers** (the server's error and response, before
`togRPCError`): the hashing's error, nothing proposed (`adminPreOn` back), or the server's answer to
the proposed request (`userAddOutOn`). -/
def userAddAnsOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) (name : GoString) (b : Bool)
    (l : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜l = null ∧ err ≠ GoInterface.nil⌝ ∗ adminPreOn s E ρ ctx cd F) ∨
    userAddOutOn s E ρ F name b l err)

/-- **`AuthServer.UserAdd` with auth on, end to end** (the auth plan's E3y, 2026-10-27): the
handler's contract discharged by the server's `UserAdd` with auth on (`server_user_add_on`), the
password hashed by `bcrypt` (whose error is one `togRPCError` takes, since E3y): on `(resp, nil)`,
some model of the request (its name `name`, its password choice `b`) applied at the committed
prefix before its entry, its admin step succeeding there (`userAddOutOn`'s `appliedOkM true`,
`adminDoneM`); an error is `togRPCError`'s of the hashing's (nothing proposed), the apply thread's
or the proposal's (`authWrapOut`, `userAddAnsOn`). -/
theorem userAdd_end_to_end_on (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ast : GoInterfaceOk) (r : Loc) (name pw hpw : GoString)
    (o : Loc) (b : Bool) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        ⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" r ↦□ name ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" r ↦□ o ∗ auth.userOptsAt o b ∗
        ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F }}
      (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserAdd"))
        (Val #(GoInterface.ok ctx))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        v3rpc.authWrapOut (userAddAnsOn s E ρ ctx cd F name b) resp err }} := by
  iintro %Φ ⟨#Pv, #Ps, #Has, #Hast, #Hcost, %Hr, #HN, Hpw, Hhpw, #Ho, #Hopts, %Hn, HP⟩ HΦ
  ihave #Hin : v3rpc.authInnerOk s go!"UserAdd" (GoInterface.ok ctx) r
      iprop(structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
        structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
        adminPreOn s E ρ ctx cd F)
      (userAddAnsOn s E ρ ctx cd F name b) $$ []
  · iunfold v3rpc.authInnerOk
    iintro !> %Ψ ⟨Hpw', Hhpw', HP'⟩ HΨ
    iapply (server_user_add_on s E ρ ctx cd ast r name pw hpw o b F) $$ [Hpw' Hhpw' HP']
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
        adminPreOn s E ρ ctx cd F)
      (userAddAnsOn s E ρ ctx cd F name b)) $$ [Hpw Hhpw HP] HΦ
  iframe # Hpw Hhpw HP

/-- `UserAdd`'s answer (`authWrapOut` of `userAddAnsOn`, the password choice `false`): the run's
slot back and, on `nil`, the reply (`userAddReplied`). -/
theorem authWrapOut_userAdd (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (F : mvcc.Log) (name : GoString) (resp : Loc)
    (err : GoInterface) :
    v3rpc.authWrapOut (userAddAnsOn s E ρ ctx cd F name false) resp err ⊢
      authSlot s E ∗ (⌜err = GoInterface.nil⌝ -∗ userAddReplied E ρ name) := by
  iintro H
  iunfold v3rpc.authWrapOut at H
  icases H with (⟨%He, H⟩ | ⟨%Hr, %e0, %He0, H⟩)
  · subst He
    iunfold userAddAnsOn at H
    icases H with (⟨%Hc, -⟩ | H)
    · exact absurd rfl Hc.2
    iunfold userAddOutOn at H
    icases H with ⟨%um, %Hum, H⟩
    ihave ⟨Hs, Hrep⟩ := adminOutOn_reply s E ρ (irrUserAdd um) F _ resp GoInterface.nil $$ H
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
      ihave ⟨Hs, -⟩ := adminOutOn_reply s E ρ (irrUserAdd um) F _ null e0 $$ H
      iframe Hs
      iintro %He
      exact absurd He Hr.2

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
      grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserAdd")
        (authSlot s E) (etcdUserAddSpec E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR, #Hast, #Hcost⟩
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, Ho, Hspec⟩ HΨ
  simp only [pbAuthUserAddRequest]
  icases Hr with ⟨%Hrn, #HN, %o, #Ho', #Hopts⟩
  iunfold userOptsFalse at Hopts
  icases Ho with ⟨Hpw, Hhpw⟩
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold etcdUserAddSpec at Hspec
  icases Hspec with ⟨%Hn, Hk⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #HF
  iapply (userAdd_end_to_end_on p s E ρ ci cd ast r m.name m.pw [] o false []) $$
    [Hpw Hhpw Hlt Hrd Hid]
  · unfold adminPreOn
    iframe; iframe #
    try (ipureintro; exact ⟨Hrn, Hn⟩)
  inext
  iintro %resp %err Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_userAdd s E ρ ci cd [] m.name resp err $$ Hout
  iapply HΨ
  iframe Hs
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthUserAddResponse]; itrivial
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `RoleAdd`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_roleAddHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleAdd")
        (authSlot s E) (etcdRoleAddSpec E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hspec⟩ HΨ
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold etcdRoleAddSpec at Hspec
  icases Hspec with ⟨%Hn, Hk⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #HF
  iapply (roleAdd_end_to_end_on p s E ρ ci cd r m []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    simp only [apply.authRoleAddIs, auth.roleAddReqIs, pbAuthRoleAddRequest]
    iframe; iframe #
    ipureintro; exact Hn
  inext
  iintro %resp %err Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (irrRoleAdd m) [] _ resp err $$ Hout
  iapply HΨ
  iframe Hs
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthRoleAddResponse]; itrivial
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `UserGrantRole`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_userGrantRoleHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGrantRole")
        (authSlot s E) (etcdUserGrantRoleSpec E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hspec⟩ HΨ
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold etcdUserGrantRoleSpec at Hspec
  icases Hspec with ⟨%Hn, Hk⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #HF
  iapply (userGrantRole_end_to_end_on p s E ρ ci cd r m.1 m.2 []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    simp only [apply.authUserGrantRoleIs, pbAuthUserGrantRoleRequest]
    iframe; iframe #
    ipureintro; exact Hn
  inext
  iintro %resp %err Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (irrUserGrantRole m.1 m.2) [] _ resp err $$ Hout
  iapply HΨ
  iframe Hs
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthUserGrantRoleResponse]; itrivial
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `RoleGrantPermission`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_roleGrantPermissionHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleGrantPermission")
        (authSlot s E) (etcdRoleGrantPermissionSpec E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hspec⟩ HΨ
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold etcdRoleGrantPermissionSpec at Hspec
  icases Hspec with ⟨%Hn, Hk⟩
  ihave Hu := HNR
  imod Hu with Hid
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #HF
  iapply (roleGrantPermission_end_to_end_on p s E ρ ci cd r m.1 (some m.2) []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    simp only [apply.authRoleGrantPermissionIs, pbAuthRoleGrantPermissionRequest]
    iframe; iframe #
    ipureintro; exact Hn
  inext
  iintro %resp %err Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ (irrRoleGrantPermission m.1 (some m.2)) [] _ resp err $$ Hout
  iapply HΨ
  iframe Hs
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthRoleGrantPermissionResponse]; itrivial
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `AuthEnable`, as the service runs it** (as `etcd_userAddHandlerOk`; it does not write its
request). -/
theorem etcd_authEnableHandlerOk (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ⊢
      grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"AuthEnable")
        (authSlot s E) (etcdAuthEnableSpec E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR⟩
  unfold grpcHandlerOwnOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨Hslot, #Hctx, #Hrc, #Hr, -, Hk⟩ HΨ
  simp only [pbAuthEnableRequest] at *
  iunfold authSlot at Hslot
  icases Hslot with ⟨Hlt, Hrd⟩
  iunfold etcdAuthEnableSpec at Hk
  ihave Hu := HNR
  imod Hu with Hid
  imod (mvcc.idxCert_nil (GF := GF) E.γ.idx) with #HF
  iapply (authEnable_end_to_end_on p s E ρ ci cd r []) $$ [Hlt Hrd Hid]
  · unfold adminPreOn
    iframe; iframe #
  inext
  iintro %resp %err Hout
  ihave ⟨Hs, Hrep⟩ := authWrapOut_admin s E ρ irrAuthEnable [] _ resp err $$ Hout
  iapply HΨ
  iframe Hs
  iintro %He
  iexists ()
  isplitr
  · simp only [pbAuthEnableResponse]; itrivial
  iapply Hk
  iapply Hrep
  ipureintro; exact He

/-- **etcd's `UserAdd`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodOk`): the generated
`_Auth_UserAdd_Handler` on the `*AuthServer` `p` whose `UserAdd` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_userAddMethodOk (p : Loc) (Spec : GrpcSpec (GF := GF) pbAuthUserAddRequest pbAuthUserAddResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserAdd") S Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Auth_UserAdd_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthUserAddRequest) -∗
      (pbAuthUserAddRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthUserAddRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthUserAddRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserAddRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthUserAddRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_UserAdd_Handler pbAuthUserAddRequest pbAuthUserAddResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `RoleAdd`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodOk`): the generated
`_Auth_RoleAdd_Handler` on the `*AuthServer` `p` whose `RoleAdd` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_roleAddMethodOk (p : Loc) (Spec : GrpcSpec (GF := GF) pbAuthRoleAddRequest pbAuthRoleAddResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleAdd") S Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Auth_RoleAdd_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthRoleAddRequest) -∗
      (pbAuthRoleAddRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthRoleAddRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthRoleAddRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthRoleAddRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthRoleAddRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_RoleAdd_Handler pbAuthRoleAddRequest pbAuthRoleAddResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `UserGrantRole`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodOk`): the generated
`_Auth_UserGrantRole_Handler` on the `*AuthServer` `p` whose `UserGrantRole` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_userGrantRoleMethodOk (p : Loc) (Spec : GrpcSpec (GF := GF) pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"UserGrantRole") S Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Auth_UserGrantRole_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthUserGrantRoleRequest) -∗
      (pbAuthUserGrantRoleRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthUserGrantRoleRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthUserGrantRoleRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthUserGrantRoleRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthUserGrantRoleRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_UserGrantRole_Handler pbAuthUserGrantRoleRequest pbAuthUserGrantRoleResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `RoleGrantPermission`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodOk`): the generated
`_Auth_RoleGrantPermission_Handler` on the `*AuthServer` `p` whose `RoleGrantPermission` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_roleGrantPermissionMethodOk (p : Loc) (Spec : GrpcSpec (GF := GF) pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"RoleGrantPermission") S Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Auth_RoleGrantPermission_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthRoleGrantPermissionRequest) -∗
      (pbAuthRoleGrantPermissionRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthRoleGrantPermissionRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthRoleGrantPermissionRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthRoleGrantPermissionRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthRoleGrantPermissionRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_RoleGrantPermission_Handler pbAuthRoleGrantPermissionRequest pbAuthRoleGrantPermissionResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

/-- **etcd's `AuthEnable`, as grpc runs it** (`grpcMethodOk`; as `etcd_putMethodOk`): the generated
`_Auth_AuthEnable_Handler` on the `*AuthServer` `p` whose `AuthEnable` meets etcd's spec, under a chain of
transparent interceptors. -/
theorem etcd_authEnableMethodOk (p : Loc) (Spec : GrpcSpec (GF := GF) pbAuthEnableRequest pbAuthEnableResponse)
    (S : IProp GF) (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOwnOk (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty @!! go!"AuthEnable") S Spec ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Auth_AuthEnable_Handler)
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  iintro ⟨#Hh, #Ppb, #Hics⟩
  unfold grpcMethodOk
  iintro %m %Φ %ci %cd %dec %ui !> %Ψ ⟨⟨HS, HRs⟩, #Hctx, #Hrc, #Hdec, #Hch, HSpec⟩ HΨ
  ihave #Hbl : iprop(□ ∀ l : Loc, l ↦ (zero_val etcdserverpb.AuthEnableRequest) -∗
      (pbAuthEnableRequest (GF := GF)).blank l) $$ []
  · iintro !> %l Hl; simp only [pbAuthEnableRequest]; iexact Hl
  ihave #HQr : iprop(□ ∀ l : Loc, (pbAuthEnableRequest (GF := GF)).recv l m -∗
      v3rpc.learnerReqOk (interface.mkOk (go.GoType.PointerType etcdserverpb.AuthEnableRequest.ty) #l)) $$ []
  · iintro !> %l -
    iapply (v3rpc.learnerReqOk_ptr _ l (by simp [etcdserverpb.AuthEnableRequest.ty, etcdserverpb.RangeRequest.ty]))
  iapply (v3rpc.etcdserverpb.wp__Auth_AuthEnable_Handler pbAuthEnableRequest pbAuthEnableResponse Spec
    ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty, #p⟩
    S ics Rs v3rpc.learnerReqOk m Φ ci cd dec ui rfl rfl authServer_isAuthServer)
    $$ [HS HRs HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, HRs, Hres⟩
  iapply HΨ
  iframe

end endToEnd

/-! ## The Auth service over gRPC (the auth plan's E3za, 2026-10-27)

The five admin methods `examples/authkv`'s `SetUp` calls, as grpc runs them (`etcd_*MethodOk`, from
each handler's E3y result, `etcd_*HandlerOk`), and served at an address (`etcd_auth_served`), with
etcd's specs (`AuthService.lean`). -/

section authGrpc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

/-- **What `RegisterAuthServer(gs, p)` registers of the Auth service's methods we specify** (the
`ServiceDesc`'s `MethodDesc`s under `"/etcdserverpb.Auth/"`, with the service value). -/
def etcdAuthRegs (p : Loc) : List (GoString × val × GoInterface) :=
  [(go!"/etcdserverpb.Auth/UserAdd", (@! etcdserverpb._Auth_UserAdd_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/UserGrantRole", (@! etcdserverpb._Auth_UserGrantRole_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/RoleAdd", (@! etcdserverpb._Auth_RoleAdd_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/RoleGrantPermission", (@! etcdserverpb._Auth_RoleGrantPermission_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p),
   (go!"/etcdserverpb.Auth/AuthEnable", (@! etcdserverpb._Auth_AuthEnable_Handler),
     interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p)]

/-- **etcd's Auth methods** as registered, with etcd's specs. -/
def etcdAuthMethods (p : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Auth/UserAdd", pbAuthUserAddRequest, pbAuthUserAddResponse, etcdUserAddSpec E ρ,
     (@! etcdserverpb._Auth_UserAdd_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p⟩,
   ⟨go!"/etcdserverpb.Auth/UserGrantRole", pbAuthUserGrantRoleRequest, pbAuthUserGrantRoleResponse, etcdUserGrantRoleSpec E ρ,
     (@! etcdserverpb._Auth_UserGrantRole_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p⟩,
   ⟨go!"/etcdserverpb.Auth/RoleAdd", pbAuthRoleAddRequest, pbAuthRoleAddResponse, etcdRoleAddSpec E ρ,
     (@! etcdserverpb._Auth_RoleAdd_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p⟩,
   ⟨go!"/etcdserverpb.Auth/RoleGrantPermission", pbAuthRoleGrantPermissionRequest, pbAuthRoleGrantPermissionResponse, etcdRoleGrantPermissionSpec E ρ,
     (@! etcdserverpb._Auth_RoleGrantPermission_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p⟩,
   ⟨go!"/etcdserverpb.Auth/AuthEnable", pbAuthEnableRequest, pbAuthEnableResponse, etcdAuthEnableSpec E ρ,
     (@! etcdserverpb._Auth_AuthEnable_Handler), interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthServer.ty) #p⟩]

/-- **etcd's server serves its Auth methods** (the auth plan's E3za; as `etcd_kv_served`): the gRPC
server at `addr` built with the chain `ics` of transparent interceptors (with their per-run
resources `Rs`), with the Auth service registered on the `*AuthServer` `p` (`etcdAuthRegs p` among
the registered methods), that hands the runtime `N` run slots (`authSlot` and the interceptors'),
registers etcd's specs of `UserAdd`, `UserGrantRole`, `RoleAdd`, `RoleGrantPermission` and
`AuthEnable` at `addr` (`isGrpcRpc`). Premises: the server's with auth on (`isServerReqM true`,
the id budget `□ |==> idCred ρ.ids 1`), the `*AuthServer` over it (`authServerIs`: what
`NewAuthServer(s)` returns), its auth store's bcrypt cost (`bcryptCostOk`), the interceptors'
contracts, the packages'. -/
theorem etcd_auth_served (addr : GoString) (p s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (ast : GoInterfaceOk) (ics : List GoFunc) (Rs : List (IProp GF))
    (regs : List (GoString × val × GoInterface)) (N : Nat)
    (hregs : ∀ x ∈ etcdAuthRegs (GF := GF) p, x ∈ regs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        v3rpc.authServerIs p s ∗ isServerReqM true s E ρ ∗ □ (|==> idCred ρ.ids 1) ∗
        structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗ bcryptCostOk ast ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ∗
        grpcServerAt addr ics regs ∗
        ([∗list] _x ∈ List.replicate N (), iprop(authSlot s E ∗ [∗list] R ∈ Rs, R)) ⊢
      |={⊤}=> isGrpcRpc addr go!"/etcdserverpb.Auth/UserAdd" (etcdUserAddSpec E ρ) ∗
        isGrpcRpc addr go!"/etcdserverpb.Auth/UserGrantRole" (etcdUserGrantRoleSpec E ρ) ∗
        isGrpcRpc addr go!"/etcdserverpb.Auth/RoleAdd" (etcdRoleAddSpec E ρ) ∗
        isGrpcRpc addr go!"/etcdserverpb.Auth/RoleGrantPermission" (etcdRoleGrantPermissionSpec E ρ) ∗
        isGrpcRpc addr go!"/etcdserverpb.Auth/AuthEnable" (etcdAuthEnableSpec E ρ) := by
  iintro ⟨#Pv, #Ps, #Has, #Hsrv, #HNR, #Hast, #Hcost, #Hics, Hl, Hslots⟩
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
  ihave #Hmu := etcd_userAddMethodOk p _ _ ics Rs $$ [Hu Ppb Hics]
  · iframe #
  ihave #Hmg := etcd_userGrantRoleMethodOk p _ _ ics Rs $$ [Hg Ppb Hics]
  · iframe #
  ihave #Hmr := etcd_roleAddMethodOk p _ _ ics Rs $$ [Hr Ppb Hics]
  · iframe #
  ihave #Hmp := etcd_roleGrantPermissionMethodOk p _ _ ics Rs $$ [Hp Ppb Hics]
  · iframe #
  ihave #Hme := etcd_authEnableMethodOk p _ _ ics Rs $$ [He Ppb Hics]
  · iframe #
  imod (grpc_serve_rpcs addr ics regs (etcdAuthMethods p E ρ)
    iprop(authSlot s E ∗ [∗list] R ∈ Rs, R) N (by simp only [etcdAuthMethods, List.map]; decide)
    (by
      intro x hx
      apply hregs
      simp only [etcdAuthMethods, List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [etcdAuthRegs])) $$ [Hl Hslots] with Hrpcs
  · iframe
    imodintro
    simp only [etcdAuthMethods]
    iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  simp only [etcdAuthMethods]
  icases Hrpcs with ⟨#H1, #H2, #H3, #H4, #H5, -⟩
  imodintro
  iframe #

end authGrpc

/-! ## The vertical slice, unit V1 (2026-10-13): the clients' model implemented

`ClientModel.lean`: the clients' class `EtcdModel` (`cache/v3/EtcdModel.lean`, fourteen axioms
until V1) instantiated by the server (`etcdModelOfServer`), each law a theorem; what the
server's answers give the model (`etcdState_of_range`, `etcdState_of_txnRead`,
`etcdReached_of_certOk`, `revToken_of_put`). (V1's wire, the generated stub's four axioms and
`isKVClient`, was superseded at the merge of unit C1 by the client's own proof down to grpc's
`ClientConn.Invoke`: `client/v3/InvKVConn.lean`, `client/v3/Results.lean`.) -/

section slice
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.api.v3 mvcc txn

/-- **The server implements the clients' model of etcd** (`etcdModelOfServer`, every law a
theorem): its predicates are the server's facts about its sealed logs (`srvEtcdState`, `srvStep`:
`idxSealed`, unit W-M2b) and the logs it certified (`srvReachedAt`: `certOk`, unit W-M3: the KV
model of a committed raft prefix) and the revisions' tokens the apply thread mints (`revTok`). -/
theorem etcd_model_of_server (E : apply.AEnv GF) :
    ∃ M : EtcdModel GF, M.etcdState = srvEtcdState E ∧ M.etcdReachedAt = srvReachedAt E ∧
      M.etcdRevToken = revTok E ∧ M.EtcdStep = srvStep E :=
  ⟨etcdModelOfServer E, rfl, rfl, rfl, rfl⟩

/-- **A header's revision is reached**: the revision of a log the server certified (every
answer's header revision is one: `rangeAnsOk`'s, `txnReadAns`'s, the writes' `certOk` of the log
after; unit W-M3) gives `etcdReached` in the server's model (`etcdReached_of_certOk`). -/
theorem etcdReached_of_hdr (E : apply.AEnv GF) (log : mvcc.Log) (r : w64)
    (h : sint.Z r < log.length) :
    mvcc.certOk E.γ log ⊢ etcdReached (EM := etcdModelOfServer E) r :=
  etcdReached_of_certOk E log r h

/-- **What a successful `Range` gives the clients' model** (`range_end_to_end`'s `rangeAnsOk`):
the header's revision `r` is the certified log's last (reached), and etcd's state at `r` under any
prefix is the log's last state restricted to it; the response is the txn package's range at that
log (`txn.rangeResult`; with `rangeSel_underPfx`, its selection of a range under the prefix is the
restricted state's). -/
theorem etcdState_of_range (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : Log) (o : OpFull)
    (resp : Loc) (r : w64) (pfx : GoString) (Q : List EntryModel → IProp GF) :
    storeSmall E.γ ∗ rangeAnsOk E γr c F o resp r Q ⊢
      ∃ log : Log, ⌜r = W64 ((log.length : Int) - 1) ∧ 2 ≤ log.length ∧
          log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
        □ etcdState (self := etcdModelOfServer E) r pfx (underPfx pfx (stateAfter log)) ∗
        ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ ∗
        etcdReached (EM := etcdModelOfServer E) r ∗
        (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
        txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true := by
  iintro ⟨#Hsm, Hok⟩
  iunfold rangeAnsOk at Hok
  icases Hok with ⟨%log, #H, #Hcok, %Hl, Hlin, -, Hres⟩
  obtain ⟨h2, h3, rfl, hF⟩ := Hl
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave ⟨#Hst, %Hwf⟩ := etcdState_of_cert_last E log pfx h2 h3 $$ [$Hsm $H]
  iexists log
  iframe Hst Hlin Hres
  isplitr
  · ipureintro; exact ⟨rfl, h2, h3, hF⟩
  isplitr
  · ipureintro; exact Hwf
  iapply etcdReached_of_certOk E log _ (by omega) $$ Hcok

/-- **What a successful read-only `Txn` gives the clients' model** (`txn_end_to_end`'s
`txnReadAns`): as `etcdState_of_range`, the response the server's run of the transaction at the
log's last revision. -/
theorem etcdState_of_txnRead (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : Log)
    (t : TxnModel) (Q : List EntryModel → IProp GF) (resp : Loc) (r : w64) (pfx : GoString) :
    storeSmall E.γ ∗ txnReadAns E γr c F t Q resp r ⊢
      ∃ log : Log, ⌜r = W64 ((log.length : Int) - 1) ∧ 2 ≤ log.length ∧
          log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
        □ etcdState (self := etcdModelOfServer E) r pfx (underPfx pfx (stateAfter log)) ∗
        ⌜EtcdStateWf pfx (underPfx pfx (stateAfter log))⌝ ∗
        etcdReached (EM := etcdModelOfServer E) r ∗
        (if txn.txnSerializable t then iprop(True) else readLogOk γr c log) ∗
        txn.txnResponseIs false resp (W64 ((log.length : Int) - 1)) t
          (txn.srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).1
          (txn.srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).2.2 := by
  iintro ⟨#Hsm, Hok⟩
  iunfold txnReadAns at Hok
  icases Hok with ⟨%log, #H, #Hcok, %Hl, Hlin, -, Hres⟩
  obtain ⟨h2, h3, rfl, hF⟩ := Hl
  have hr : sint.Z (W64 ((log.length : Int) - 1)) = (log.length : Int) - 1 := by word
  ihave ⟨#Hst, %Hwf⟩ := etcdState_of_cert_last E log pfx h2 h3 $$ [$Hsm $H]
  iexists log
  iframe Hst Hlin Hres
  isplitr
  · ipureintro; exact ⟨rfl, h2, h3, hF⟩
  isplitr
  · ipureintro; exact Hwf
  iapply etcdReached_of_certOk E log _ (by omega) $$ Hcok

/-- **What a successful `Put` gives the clients' model** (`put_end_to_end`'s `putAppliedOk`, the
client's `putApplied`): the token of the header's revision `r` (`etcdRevToken r`: the apply thread
minted it when the put's revision committed) and that etcd has reached `r`. -/
theorem revToken_of_put (E : apply.AEnv GF) (γw : ReadNames) (F : Log) (o : OpFull)
    (Q : KVState → IProp GF) (resp : Loc) (r : w64) :
    putApplied E γw F o Q resp r ⊢
      etcdRevToken (self := etcdModelOfServer E) r ∗ etcdReached (EM := etcdModelOfServer E) r := by
  iintro Hok
  iunfold putApplied at Hok
  icases Hok with ⟨%hm, %x, %x', %l, %skip, %Hp, -, #Hcert, HMint, -, #Hcok, -⟩
  obtain ⟨Hstep, rfl, -⟩ := Hp
  obtain ⟨cs, hcs⟩ := put_appended o hm x x' l skip Hstep
  ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
  iunfold revMinted at HMint
  icases HMint with (%He | ⟨%cs', %He, Ht⟩)
  · rw [hcs] at He
    exact absurd (congrArg List.length He) (by simp)
  isplitl [Ht]
  · rw [etcdModelOfServer_etcdRevToken]
    iexact Ht
  iapply etcdReached_of_certOk E x'.log _ (by rw [hcs] at Hlen ⊢; simp at Hlen ⊢; word) $$ Hcok

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The watch service's method** (`watchServer.Watch`, linked): see the section header. -/
theorem watch_server : EtcdGrove.v3rpc.watchServer.Watch.spec (GF := GF) (hG := hG) :=
  watchServer.wp_Watch

/-- **The watch server's constructor** (`NewWatchServer`, linked): `isWatchServer`. -/
theorem new_watch_server : EtcdGrove.v3rpc.NewWatchServer.spec (GF := GF) (hG := hG) :=
  wp_NewWatchServer

/-- **A registered watcher was authorized** (the auth plan's A4, 2026-10-24; `WatchClass.lean`,
`ctrlWatcher_authorized`): with the server's auth mode `on γa` (`watchSrvOk`'s tag of the store's
names, `auth.modeTag γ.tag`), the mvcc watcher a created, not canceled, control response names
(`watchDn`'s `ctrlOk`, `ctrlWatcher`) has a range every key of which some principal (the stream's
context's auth info, or the empty one) could read at a recorded state of the auth history: auth
disabled there, or the principal a user with the root role, or one whose READ permissions cover
the key. The interval the check saw is the interval mvcc registers for every request shape
(`createRangeOk_inRange`): the point, the proper range, `WithFromKey`'s `"\x00"` end, the empty
key. -/
theorem watch_registered_authorized (γ : mvcc.WsNames) (γo : mvcc.WsStreamNames)
    (γa : auth.AuthNames) (c : CreateReqM) (m : WatchRespM) (h : m.canceled = false) :
    auth.modeTag (GF := GF) γ.tag (.on γa) ∗ ctrlWatcher γ γo (.create c) m ⊢
      ∃ (w : Loc) (r : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (i : Nat) (st : auth.AuthState),
        ⌜createRangeOk c m.watchId r⌝ ∗ mvcc.watcherIs γ w r fcs lo ∗
        mvcc.idAssigned γo m.watchId w ∗ auth.authStateAt γa i st ∗
        ⌜st.enabled = false ∨
          ((auth.authInfoM info).rev ≠ 0 ∧
            ∃ u, st.users !! (auth.authInfoM info).user = some u ∧
              (auth.isRoot u ∨ ∀ x, r.covers x = true →
                ∃ p ∈ auth.userPerms st u, p.covers .read x))⌝ :=
  ctrlWatcher_authorized γ γo γa c m h

/-- **The gRPC layer's guards with the token binding** (`GuardBound.lean`): over a server whose
store has the bound request side, `AuthAdmin.isPermitted`'s admin token and the
`requireAuthInfo`s' authenticated user are bound principals. -/
theorem authAdmin_isPermitted_bound :
    v3rpc.AuthAdmin.isPermitted.boundSpec (GF := GF) (hG := hG) :=
  v3rpc.AuthAdmin.isPermitted_bound EtcdServer.wp_AuthStore

theorem authAdmin_requireAuthInfo_bound :
    v3rpc.AuthAdmin.requireAuthInfo.boundSpec (GF := GF) (hG := hG) :=
  v3rpc.AuthAdmin.requireAuthInfo_bound EtcdServer.wp_AuthStore

theorem maintenance_requireAuthInfo_bound :
    v3rpc.authMaintenanceServer.requireAuthInfo.boundSpec (GF := GF) (hG := hG) :=
  v3rpc.authMaintenanceServer.requireAuthInfo_bound
    (v3rpc.AuthAdmin.requireAuthInfo_bound EtcdServer.wp_AuthStore)

/-- **The watch's check with the token binding** (the auth plan's E1, `WatchBound.lean`): over a
server whose store has the bound request side (`srvAuthBound`), a passed `isWatchPermitted`'s
principal is the anonymous one, a user to whom some token was issued, or the TLS fallback's. -/
theorem watch_check_bound :
    v3rpc.serverWatchStream.isWatchPermitted.boundSpec (GF := GF) (hG := hG) :=
  v3rpc.serverWatchStream.isWatchPermitted_bound EtcdServer.wp_AuthStore

end watch

/-! ## The watch service on the wire (unit W-W)

The generated stream handler `_Watch_Watch_Handler` (linked) runs `watchServer.Watch` on the
wrapped raw server end grpc passes (`srvStreamIs_of_raw`, over `GenericServerStream`'s methods,
axioms: Goose does not translate methods of generic types); with the server's stream
interceptors transparent (`srvStreamInterceptorsOk`, a premise: grpc-prometheus's and
`newStreamInterceptor` are not verified), the handler meets the registration's contract
(`etcd_watchMethodOk`), and a server with the method registered (`grpcStreamServerAt`) and `n`
run slots serves it at its address (`etcd_watch_served`): what a client's `NewStream` needs. -/

section watch_wire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode go_etcd_io.etcd.api.v3

/-- **The generated stream handler** (`_Watch_Watch_Handler`, linked): see the section header. -/
theorem watch_handler : EtcdGrove.etcdserverpb._Watch_Watch_Handler.spec (GF := GF) (hG := hG) :=
  etcdserverpb.wp__Watch_Watch_Handler

/-- **The watch server's `Watch` is a stream method** (`grpcStreamHandlerOk`): on the wrapped
server end, with the run slot `watchRunSlot R`, the client's content `watchUp` and the stream
specification `watchSpec R` (`watchStreamSpec` at the server's names), from `watch_server`. -/
theorem watch_streamHandlerOk (p : Loc) (R : WSrv GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ⊢
    grpcStreamHandlerOk (Req := pbWatchRequest)
      #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
        go!"Watch" #p)
      (watchRunSlot R) (watchUp R.γ) (watchSpec R) := by
  iintro ⟨#Hinit, #Hws⟩
  unfold grpcStreamHandlerOk
  iintro !> %γs %Dn %ci %cd %st %Φ HSpec HS #Hst HRt HSt HAux HΦ
  ihave #Hup := upOk_watchUp (GF := GF) R.γ
  iapply (watch_server p R st γs (watchUp R.γ) Dn ci cd) $$ [HSpec HS HRt HSt HAux]
  · iframe
    iframe #
  inext
  iintro %err -
  iapply HΦ

/-- **The generated handler meets the registration's contract** (`grpcStreamMethodOk`) for the
`*watchServer` `p` (its type implements `WatchServer`: a method-set fact), under the server's
stream interceptors `ics`, transparent with their run resources `Rs`: the run slot is the watch
run's (`watchRunSlot R`) and the interceptors'. -/
theorem etcd_watchMethodOk (p : Loc) (R : WSrv GF) (ics : List GoFunc) (Rs : List (IProp GF))
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvStreamInterceptorsOk ics Rs ⊢
    grpcStreamMethodOk (Req := pbWatchRequest) (@! etcdserverpb._Watch_Watch_Handler)
      (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) ics
      iprop(watchRunSlot R ∗ [∗list] R' ∈ Rs, R') (watchUp R.γ) (watchSpec R) := by
  iintro ⟨#Hpb, #Hinit, #Hws, #Hics⟩
  ihave #Hh := watch_streamHandlerOk p R $$ [Hinit Hws]
  · iframe #
  unfold grpcStreamMethodOk
  isplitr
  · iapply streamSpecOk_watchSpec
  iintro !> %γs %Dn %ci %cd %st %info HSpec ⟨HS, HRs⟩ #Hraw HRt HSt HAux #Hinfo
  iapply (srvStreamChainWP_of_ok ics Rs pbWatchRequest pbWatchResponse (watchUp R.γ) Dn γs ci cd
    (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) st info
    (@! etcdserverpb._Watch_Watch_Handler) (fun _ => iprop(True)))
  iframe #
  iframe HRs
  isplit
  · iintro %st' %ci' %cd' #Hraw'
    iapply (watch_handler pbWatchRequest pbWatchResponse (watchUp R.γ) (watchSpec R)
      ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty, #p⟩
      (watchRunSlot R) γs Dn ci' cd' st' rfl rfl hset) $$ [HSpec HS HRt HSt HAux]
    · iframe
      iframe #
      iintro !> %l Hl
      iexists _
      iexact Hl
    inext
    iintro %err -
    iexists err
    isplitr
    · ipureintro; rfl
    iintro -
    itrivial
  · iintro - %err -
    itrivial

/-- **The watch service is served** (unit W-W; as `etcd_kv_served` for the KV service): a gRPC
server at `addr` built with the stream interceptors `ics` (transparent, with the resources `Rs`)
and the `Watch` stream of `Watch_ServiceDesc` registered with the `*watchServer` `p`
(`grpcStreamServerAt`, the registration `RegisterWatchServer` makes), handed `n` run slots (each
the watch run's resources and the interceptors'), serves the method: its stream specification is
`watchStreamSpec` at the server's names and ids, and each request the client sends carries
`watchUp` (restricted, a watch token with each create). -/
theorem etcd_watch_served (addr : GoString) (p : Loc) (R : WSrv GF) (ics : List GoFunc)
    (Rs : List (IProp GF)) (sregs : List (GoString × val × GoInterface)) (n : Nat)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true)
    (hreg : (go!"/etcdserverpb.Watch/Watch", (@! etcdserverpb._Watch_Watch_Handler : val),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) ∈ sregs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvStreamInterceptorsOk ics Rs ∗ grpcStreamServerAt addr ics sregs ∗
      ([∗list] _x ∈ List.replicate n (), iprop(watchRunSlot R ∗ [∗list] R' ∈ Rs, R')) ⊢
    |={⊤}=> isGrpcStream (Req := pbWatchRequest) (Rep := pbWatchResponse) addr
      go!"/etcdserverpb.Watch/Watch" (watchUp R.γ)
      (fun γs Dn => watchStreamSpec γs R.γ R.cid R.mid Dn) := by
  iintro ⟨#Hpb, #Hinit, #Hws, #Hics, Hsrv, Hslots⟩
  ihave #Hok := etcd_watchMethodOk p R ics Rs hset $$ [Hpb Hinit Hws Hics]
  · iframe #
  let m : GrpcStreamMethod GF :=
    { name := go!"/etcdserverpb.Watch/Watch", Req := pbWatchRequest, Rep := pbWatchResponse,
      Up := watchUp R.γ, spec := watchSpec R, handler := @! etcdserverpb._Watch_Watch_Handler,
      srv := interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p }
  have hnd : ([m].map GrpcStreamMethod.name).Nodup := by simp
  have hr : ∀ x ∈ [m], (x.name, x.handler, x.srv) ∈ sregs := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hreg
  imod (grpc_serveStream_rpcs addr ics sregs [m] _ n hnd hr) $$ [Hsrv Hslots] with Hs
  · iframe
    imodintro
    iapply BigSepL.bigSepL_singleton.2
    iexact Hok
  ihave Hs := BigSepL.bigSepL_singleton.1 $$ Hs
  imodintro
  iexact Hs

/-- **The watch service is served by etcd's server** (`etcd_watch_served` at the stream chain
`v3rpc.Server` installs, `grpc.go`: `grpc.ChainStreamInterceptor(serverMetrics.StreamServerInterceptor(),
newStreamInterceptor(s))`, in that order): grpc-prometheus's `im` (assumed transparent, as
`etcd_kv_served` assumes the unary one) and etcd's `newStreamInterceptor` `is` (its contract a
premise: proved by the stream-interceptor unit), neither with a run resource. -/
theorem etcd_watch_served_chain (addr : GoString) (p : Loc) (R : WSrv GF) (im is : GoFunc)
    (sregs : List (GoString × val × GoInterface)) (n : Nat)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true)
    (hreg : (go!"/etcdserverpb.Watch/Watch", (@! etcdserverpb._Watch_Watch_Handler : val),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) ∈ sregs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      isWatchServer p R ∗ srvStreamInterceptorOk im iprop(True) ∗
      srvStreamInterceptorOk is iprop(True) ∗ grpcStreamServerAt addr [im, is] sregs ∗
      ([∗list] _x ∈ List.replicate n (), watchRunSlot R) ⊢
    |={⊤}=> isGrpcStream (Req := pbWatchRequest) (Rep := pbWatchResponse) addr
      go!"/etcdserverpb.Watch/Watch" (watchUp R.γ)
      (fun γs Dn => watchStreamSpec γs R.γ R.cid R.mid Dn) := by
  iintro ⟨#Hpb, #Hinit, #Hws, #Him, #His, Hsrv, Hslots⟩
  iapply (etcd_watch_served addr p R [im, is] [iprop(True), iprop(True)] sregs n hset hreg)
  iframe #
  iframe Hsrv
  isplitl []
  · iunfold srvStreamInterceptorsOk
    iframe #
    iunfold srvStreamInterceptorsOk
    iframe #
    iunfold srvStreamInterceptorsOk
    itrivial
  iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := List.replicate n ())
    (Φ := fun _ _ => watchRunSlot R)
    (Ψ := fun _ _ => iprop(watchRunSlot R ∗ [∗list] R' ∈ [iprop(True), iprop(True)], R'))
    (fun {_ _} => ?_)) $$ Hslots
  iintro H
  iframe
  iapply BigSepL.bigSepL_cons.2
  isplitl []
  · itrivial
  iapply BigSepL.bigSepL_cons.2
  isplitl []
  · itrivial
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **etcd's stream interceptor** (`newStreamInterceptor`, linked; the watch slice's unit W-W): it
starts the leader monitor and returns a transparent stream interceptor (`srvStreamInterceptorOk`,
no resource), under the premise `runsNoRequireLeader` (no client asks for a leader on a stream:
a premise about the deployment, `InvStreamInterceptor.lean`). -/
theorem new_stream_interceptor :
    EtcdGrove.v3rpc.newStreamInterceptor.spec (GF := GF) (hG := hG) :=
  wp_newStreamInterceptor

/-- **The watch service is served by etcd's server, with etcd's own stream interceptor**
(`etcd_watch_served_chain` with its second interceptor the one `newStreamInterceptor(s)` returns,
`new_stream_interceptor` discharging its contract): from `newStreamInterceptor`'s premises (the
server's member id, `lead`, cluster, `GoAttach` slots, `stopping` channel, configuration fields,
and `runsNoRequireLeader`), the call returns an interceptor `is` with the `GoAttach` slots back,
and a gRPC server built with the chain `[im, is]` (grpc-prometheus's `im` still assumed
transparent) and the `Watch` stream registered serves the method. -/
theorem etcd_watch_served_etcd_chain (addr : GoString) (p : Loc) (R : WSrv GF) (im : GoFunc)
    (sregs : List (GoString × val × GoInterface)) (n : Nat)
    (hset : go.typeSetContains
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty)
      etcdserverpb.WatchServer.ty = true)
    (hreg : (go!"/etcdserverpb.Watch/Watch", (@! etcdserverpb._Watch_Watch_Handler : val),
      interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) ∈ sregs)
    (s c ch : Loc) (mid tm et : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗ srvClusterAddr s ↦□ c ∗
        membership.isRaftCluster c ∗ membership.localKept c ∗
        srvGoRes s ∗ srvLgReader s ∗ srvStoppingAddr s ↦□ ch ∗ stopChan ch ∗
        cfgTickMsAddr (srvCfgAddr s) ↦□ tm ∗ cfgElectionTicksAddr (srvCfgAddr s) ↦□ et ∗
        v3rpc.runsNoRequireLeader }}
      (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newStreamInterceptor))
        (Val #s))
    {{ (is : GoFunc), RET #is; srvGoRes s ∗ srvLgReader s ∗
        (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
          isWatchServer p R ∗ srvStreamInterceptorOk im iprop(True) ∗
          grpcStreamServerAt addr [im, is] sregs ∗
          ([∗list] _x ∈ List.replicate n (), watchRunSlot R) ={⊤}=∗
          isGrpcStream (Req := pbWatchRequest) (Rep := pbWatchResponse) addr
            go!"/etcdserverpb.Watch/Watch" (watchUp R.γ)
            (fun γs Dn => watchStreamSpec γs R.γ R.cid R.mid Dn)) }} := by
  iintro %Φ ⟨#Hpkg, -, Hpre⟩ HΦ
  wp_apply (new_stream_interceptor s c ch mid tm et) $$ [Hpre] as %is ⟨#His, Hgr, Hlg⟩
  · iexact Hpre
  iapply HΦ
  iframe Hgr Hlg
  iintro ⟨#Hpb, #Hws, #Him, Hsrv, Hslots⟩
  iapply (etcd_watch_served_chain addr p R im is sregs n hset hreg)
  iframe #
  iframe

end watch_wire

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
#print axioms Perennial.EtcdGrove.v3rpc.watch_server
#print axioms Perennial.EtcdGrove.v3rpc.new_watch_server
#print axioms Perennial.EtcdGrove.v3rpc.watch_registered_authorized
#print axioms Perennial.EtcdGrove.v3rpc.watch_check_bound
#print axioms Perennial.EtcdGrove.v3rpc.authAdmin_isPermitted_bound
#print axioms Perennial.EtcdGrove.v3rpc.authAdmin_requireAuthInfo_bound
#print axioms Perennial.EtcdGrove.v3rpc.maintenance_requireAuthInfo_bound
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

end EtcdGrove
end Perennial
