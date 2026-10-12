/-
`s.DeleteRange(ctx, r)` (`v3_server.go`): a delete through raft and the apply thread. Lean-first
(no Rocq counterpart).
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

/-- **`s.DeleteRange(ctx, r)`** (as `Put`): success, the apply package's answer to the delete
(`deleteOutcomeIs`, no error: applied; the response header's id fields owned, `appliedHdr`) of the request the proposed data decode to (`rq'`, whose delete is
`op'`: `op` itself unless the range end is `[0]`, the model's ambiguity, `irrWireOf`), at the log
the entry met, with mvcc's certificate of the log after. -/
abbrev EtcdServer.DeleteRange.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.deleteRangeRequestIs r op }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
          (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
          ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq' ∧ rq'.deleteRange = some op' ∧
            (irrNoZeroEnd (irrDeleteRange op) → op' = op) ∧
            apply.applyStep rq' true x x' (.dispatched o skip) ∧ ∃ log', o = .applied log' false⌝ ∗
          apply.deleteOutcomeIs x.log op' resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq'⌝ ∗ appliedErr E rq' err) ∨
          srvMaybeDeposited ρ (irrDeleteRange op)))) }}

end spec

end EtcdGrove
end Perennial
