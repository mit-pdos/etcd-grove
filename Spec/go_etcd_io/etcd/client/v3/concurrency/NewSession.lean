/-
`concurrency.NewSession(client, opts...)` (`client/v3/concurrency/session.go`). Lean-first (no Rocq counterpart); see
`InvSession.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSession

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`NewSession(client, opts...)`**, for a client (`isEtcdSessionClient`: its context `cctx`, its
`Lease`, its logger) and options with transformers `gs`, whose resulting context (the client's,
unless `WithContext`) is a cancelable context (`isCancelCtxCtx`: Perennial's `WithCancel` takes
one; the client's is, `newClient` makes it with `WithCancel`): `nil` with an error, or a session (`isSession`) with a lease
`id` that is the options' lease, if they name one, or a granted one (`sessionLeaseOk`). -/
abbrev NewSession.spec : Prop :=
  ∀ (client : Loc) (cctx : GoInterface) (sl : GoSlice) (gs : List (SessionOpts → SessionOpts))
    (pctx : GoInterfaceOk) (pcs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdSessionClient client cctx ∗ sessOptsAt sl gs ∗
      ⌜(sessOptsFold gs (SessionOpts.init cctx)).ctx = GoInterface.ok pctx⌝ ∗
      context.isContext pctx pcs ∗ context.isCancelCtxCtx pctx pcs }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSession)) (Val #client)) (Val #sl))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      ⌜s = null ∧ err ≠ GoInterface.nil⌝ ∨
      (⌜err = GoInterface.nil ∧ s ≠ null⌝ ∗ ∃ (γ : SessionNames) (id : w64),
        isSession s γ client id ∗ ⌜sessionLeaseOk (sessOptsFold gs (SessionOpts.init cctx)) id⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
