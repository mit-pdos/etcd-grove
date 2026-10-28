/-
`s.Txn(ctx, r)` (`v3_server.go`): a read-only transaction read locally (as `Range`), a writing one through raft (as `Put`).
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Txn(ctx, r)`**, any goroutine, at a context, for a transaction request `r` holding `t`,
with a write call's resources (a reader slot of `s.leadTimeMu`, one id credit) and a read call's
(`srvRdCall`). A read-only `t` (`txnReadonly`; its gets within the model, `txnGetsOk`): the id
credit back; success, the server's run of `t` at a certified log, after the read index unless
serializable, the header's id fields owned (`txnReadOk`); failure, an error the gRPC layer can
take (the response may be non-nil: a context done during a range returns the partly filled
response with `executeTxn`'s error). A writing `t`: as `Put` (`txnAppliedOk`: the apply
thread's application of the request the proposed data decode to; `txnErrOk`: the apply's error
or the proposal's, which may still be applied). 2026-10-15 (unit T2): a writing transaction's
update is over the whole state (`txnPermit`: plain, no range end `[0]`, the client's
`kvOpAu (.txn t)`), a success giving `□ Q` of the state it linearized at; since 2026-10-20
(linkv-txn stage A, as `Put`) fired at most once (`kvOpAu1`), a success giving `Q`. Unit W-M3: a read-only
`t` takes a read deposit as `Range` (`kvDep γr.kv Qr`: a client's read update, or nothing), a
linearizable success reading the KV model of a committed raft log `L` at which the deposit gave
`□ Qr L` (`txnReadOk`), the state of the log written for a writing `t` (`txnAppliedOk`). -/
abbrev EtcdServer.Txn.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (Q : KVState → IProp GF) (Qr : List EntryModel → IProp GF) (ot : Option Loc) (te : Bool)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
      srvRdCall s E γr c ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ txn.txnRequestIs r t ∗
      ⌜txn.txnReadonly t = true → txn.txnGetsOk t⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      (if txn.txnReadonly t then kvDep γr.kv Qr else txnPermit ρ.kv t Q) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLeadTimeReader s ∗ srvRdCall s E γr c ∗
      if txn.txnReadonly t then
        iprop(idCred ρ.ids 1 ∗
          ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnReadOk E γr c F t Qr resp) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)))
      else
        iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnAppliedOk E ρ.rd F t Q resp) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ txnErrOk E ρ F t err)) }}

/-- **`spec` for a writing transaction in the auth mode `on`** (the auth plan's E3d, 2026-10-27;
`ReqOn.lean`): a transaction `t` that is not read-only, at the server as a proposer sees it in the
mode `on` (`isServerReqM true`), with `s.Logger()`'s field and reader slot (`EnsureTrace` reads it;
the read side's `srvRdCall` held it in `spec`) and the auth store's reader resource `E.RD`, and the
transaction's permission with its checks of the permission cache's shape (`txnPermitOn`); the
same post as `spec`'s writing case: a success is a transaction the auth state its entry met
granted (the apply thread's auth verdict is the model's, `authTie`), so its client's update fired
there and its result `Q` holds at the log the entry met (`txnAppliedOk`); a refusal is an error
(`txnErrOk`). A read-only transaction in the mode `on` (the read path, `doSerialize`'s check at
the auth store) is not covered here. -/
abbrev EtcdServer.Txn.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel) (Q : KVState → IProp GF)
    (ot : Option Loc) (te : Bool) (F : mvcc.Log) (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      txn.txnRequestIs r t ∗ ⌜txn.txnReadonly t = false⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      txnPermitOn ρ.kv t Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnAppliedOk E ρ.rd F t Q resp ∗
          ∃ (tw : txn.TxnModelW) (hm : apply.HeaderModel) (L : List EntryModel),
            ⌜tw.toModel = t⌝ ∗ pubAfterM true E ρ (apply.withHeader (irrTxn tw) hm) L) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ txnErrOk E ρ F t err)) }}

/-- **`spec` for a read-only transaction in the auth mode `on`** (the auth plan's E3v, 2026-10-27;
`notes/decisions.md`, "E3v of the auth plan"; `Range.specOn`'s): in the mode `on γa`, a read-only
`t` with its gets within the model, over the request and read views with auth on, the read deposit
at the mode-`on` model's state (`kvDep γr.kv Qr (kvStM true γr.kv)`), a lower bound `n` of the auth
store's published index (`auth.authPubLbM`; `0` is free) with the server's range check at such
bounds (`srvAuthLb`). Success: every permission the transaction's checks see was granted at states
no older than some `m ≥ n` (`txnClassFrom`, through `CheckTxnAuth`'s checks at the bound) and, for a
linearizable `t`, no older than the auth state the committed log through the read index left
(`authFloorAt`: `Txn` checks after waiting for the read index); the read as `spec`'s, at the
mode-`on` model (`txnReadOkM true`). Failure: an error the gRPC layer can take. -/
abbrev EtcdServer.Txn.specOnR : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (Qr : List EntryModel → IProp GF) (ot : Option Loc) (te : Bool) (F : mvcc.Log) (n : Nat)
    (γa : auth.AuthNames),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
      auth.authPubLbM E.authMode n ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
      srvRdCall s E γr c ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ txn.txnRequestIs r t ∗
      ⌜txn.txnReadonly t = true ∧ txn.txnGetsOk t⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      kvDep γr.kv Qr (kvStM true γr.kv) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLeadTimeReader s ∗ srvRdCall s E γr c ∗ idCred ρ.ids 1 ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
          (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗
            txnClassFrom E.authMode m info t ∗
            (if txn.txnSerializable t then iprop(True) else authFloorAt E.authMode γr c m)) ∗
          txnReadOkM true E γr c F t Qr resp) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
