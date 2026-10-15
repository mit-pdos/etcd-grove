/-
`s.raftRequest(ctx, r)` (`v3_server.go`): the request's response, or the apply's error. Lean-first
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

/-- `s.raftRequest(ctx, r)` (as `processInternalRaftRequestOnce`): success, the apply thread's
answer to `rq'` (`appliedOk`: dispatched, the apply package's response, no error); failure, no
response and an error (2026-10-14, unit C2a: the success with the result's witness at `ρ.rd`,
`appliedWit`): the apply's (`appliedErr`), or `processInternalRaftRequestOnce`'s (the
proposal, if made, deposited). -/
abbrev EtcdServer.raftRequest.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedOk E ρ.rd rq' F resp) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ rq))) }}

end spec

end EtcdGrove
end Perennial
