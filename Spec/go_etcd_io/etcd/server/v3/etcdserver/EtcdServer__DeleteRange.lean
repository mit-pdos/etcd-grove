/-
`s.DeleteRange(ctx, r)` (`v3_server.go`): a delete through raft and the apply thread. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn

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

/-- **`s.DeleteRange(ctx, r)`** (as `Put`; 2026-10-15, unit T2: a delete's update is over the
whole state, `deletePermit`: its range end not `[0]`, the client's `kvOpAu (.deleteRange op)`; a
success gives `□ Q` of the state it linearized at): success, the apply package's answer to the delete
(`deleteOutcomeIs`, no error: applied; the response header's id fields owned, `appliedHdr`) of the request the proposed data decode to (`rq'`, whose delete is
`op'`: `op` itself unless the range end is `[0]`, the model's ambiguity, `irrWireOf`), at the log
the entry met, with mvcc's certificate of the log after. 2026-10-20 (linkv-txn stage A, as
`Put` since D21 M6): the update is fired at most once (`kvOpAu1`), a success giving `Q` of the
state it fired at; on a failure it fired once or not at all. -/
abbrev EtcdServer.DeleteRange.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.deleteRangeRequestIs r op ∗ deletePermit ρ.kv op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
          (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
          ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq' ∧ rq'.deleteRange = some op' ∧
            (irrNoZeroEnd (irrDeleteRange op) → op' = op) ∧
            apply.applyStep rq' true x x' (.dispatched o skip) ∧ (∃ log', o = .applied log' false) ∧
            F <+: x.log⌝ ∗
          apply.deleteOutcomeIs x.log op' resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ (irrDeleteRange op)))) }}


/-- **`spec` in the auth mode `on`** (the auth plan's E3b, 2026-10-26; `Put.specOn`'s): a success
is a delete the auth state the entry met granted, its result `Q` at the log the entry met. -/
abbrev EtcdServer.DeleteRange.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.deleteRangeRequestIs r op ∗ deletePermitOn ρ.kv op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
          (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
          ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq' ∧ rq'.deleteRange = some op' ∧
            (irrNoZeroEnd (irrDeleteRange op) → op' = op) ∧
            apply.applyStep rq' true x x' (.dispatched o skip) ∧ (∃ log', o = .applied log' false) ∧
            F <+: x.log⌝ ∗
          apply.deleteOutcomeIs x.log op' resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ (irrDeleteRange op)))) }}

end spec

end EtcdGrove
end Perennial
