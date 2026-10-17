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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`NewSession(client, opts...)`**, for a client (`isEtcdSessionClient`: its context `cctx`, its
`Lease`, its logger) and options with transformers `gs`, whose resulting context (the client's,
unless `WithContext`) is a cancelable context (`isCancelCtxCtx`: Perennial's `WithCancel` takes
one; the client's is, `newClient` makes it with `WithCancel`): `nil` with an error, or a session (`isSession`) with a lease
`id` that is the options' lease, if they name one, or a granted one (`sessionLeaseOk`), whose
context has the values and the deadline of the options' context (`sessionCtxOf`): a creation
timeout (`WithCreationTimeout`, etcd-io/etcd#16385) bounds only the lease's `Grant`, not the
session's context, which outlives it. (That the timeout makes `NewSession` return is liveness,
which a Hoare triple does not state; nor does it say the error is `DeadlineExceeded`, nor that
`Grant` gets the creation context. Nor does it exclude passing the creation context to
`KeepAlive`, which the deferred cancel would then end at return: the lease client's `KeepAlive`
triple, `isEtcdLease`, takes any context and promises nothing of the stream; and a creation
context made with `WithCancel` alone, with the session's derived from it, keeps the values and
the deadline. `sessionCtxOf` excludes the session's context inheriting the timeout's deadline.) -/
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
        isSession s γ client id ∗ ⌜sessionLeaseOk (sessOptsFold gs (SessionOpts.init cctx)) id⌝ ∗
        sessionCtxOf s pcs) }}

end spec

end concurrency
end EtcdGrove
end Perennial
