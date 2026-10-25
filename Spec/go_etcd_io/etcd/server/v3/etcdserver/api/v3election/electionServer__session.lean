/-
`(*electionServer).session(ctx, lease)` (`server/etcdserver/api/v3election/election.go`; the auth
plan's A3c, 2026-10-24). Lean-first (no Rocq counterpart); see `v3election/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3election

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions]

/-- **`session(ctx, lease)`**: a session of the server's client over the lease `lease` (its lease
`id`: the request's, if it names one), orphaned (`Orphan`: its keep-alive stopped, the lease left
to expire), or no session and an error. -/
abbrev electionServer.session.spec : Prop :=
  ∀ (es c : Loc) (lease : w64) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗
      isElectionServer es c ∗ electionClientOk c ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs }}
    (App (App (Val (es @!! go.GoType.PointerType electionServer.ty @!! go!"session"))
      (Val #(GoInterface.ok ctx))) (Val #lease))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err = GoInterface.nil ∧ s ≠ null⌝ ∗ ∃ (γ : SessionNames) (id : w64),
        isSession s γ c id ∗ ⌜id ≠ W64 0 ∧ (lease ≠ W64 0 → id = lease)⌝) ∨
      ⌜s = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3election
end EtcdGrove
end Perennial
