/-
`s.Txn(ctx, r)` (`v3_server.go`): a read-only transaction read locally (as `Range`), a writing one through raft (as `Put`).
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
`kvOpAu (.txn t)`), a success giving `□ Q` of the state it linearized at. -/
abbrev EtcdServer.Txn.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (t : TxnModel)
    (Q : KVState → IProp GF) (ot : Option Loc) (te : Bool) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗
      srvRdCall s E γr c ∗ context.isContext ctx cd ∗ traceutil.ctxTraceIs ctx ot ∗
      traceutil.ownTraceOpt ot te ∗ txn.txnRequestIs r t ∗
      ⌜txn.txnReadonly t = true → txn.txnGetsOk t⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      (if txn.txnReadonly t then iprop(True) else txnPermit ρ.kv t Q) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Txn"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLeadTimeReader s ∗ srvRdCall s E γr c ∗
      if txn.txnReadonly t then
        iprop(idCred ρ.ids 1 ∗
          ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnReadOk E γr c F t resp) ∨
           (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err)))
      else
        iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ txnAppliedOk E ρ.rd F t Q resp) ∨
          (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ txnErrOk E ρ F t err)) }}

end spec

end EtcdGrove
end Perennial
