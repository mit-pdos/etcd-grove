/-
`s.Put(ctx, r)` (`v3_server.go`): a put through raft and the apply thread. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

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

/-- **`s.Put(ctx, r)`**, any goroutine, at a context, for a put request `r` holding `op`, with
one id credit and a reader slot of `s.leadTimeMu`: success, the apply package's answer to the put
(`putOutcomeIs`, no error: applied, `putModel`'s, at the log `x.log` the entry met) of the request
with the header the server set (`hm`), dispatched at `x` to `x'` (`applyStep`), the response
header's id fields owned (`appliedHdr`: for the gRPC layer to fill), with mvcc's certificate of
the log after, the token of the revision it appended (`revMinted`, the vertical slice's unit
V1), and (2026-10-14, unit C2a) the log after applied through an index of the committed log
(`appliedWit ρ.rd x'.log`: a linearizable read at that index reads a log extending it); failure, no response and an error the gRPC layer can take (`applyErrIs`): the
apply's (`appliedErr`), or the proposal's (made or not; if made, deposited: it may still be
applied). 2026-10-15 (unit T2): the put's update is over the whole state (`putPermit`: the lease
`0`, the client's `kvOpAu (.put op)`), a success giving `□ Q` of the state it linearized at.
2026-10-19 (D21 M6, D20 (b)): the update is fired at most once (`kvOpAu1`), a success giving `Q` of
the state it fired at; on a failure it fired once or not at all. -/
abbrev EtcdServer.Put.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull)
    (Q : KVState → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ reqIdCtx ρ ctx ∗ context.isContext ctx cd ∗
      txn.putRequestIs r op ∗ putPermit ρ.kv op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
          (o : apply.Outcome) (skip : Bool),
          ⌜apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip) ∧
            (∃ log', o = .applied log' false) ∧ F <+: x.log⌝ ∗
          apply.putOutcomeIs x.log op resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut op) hm) F err) ∨
          srvMaybeDeposited ρ (irrPut op)))) }}

end spec

end EtcdGrove
end Perennial
