/-
`s.checkLeaseRenew(ctx, id)` (`v3_server.go`): the key check of a keep-alive (`LeaseRenew`). Lean-first (no Rocq counterpart); the lease-keys plan's
Part B (2026-10-31), vocabulary `LeaseCheck.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheck

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

/-- **`s.checkLeaseRenew(ctx, id)`**, any goroutine, with the resources of
`checkLeaseTimeToLive.spec`: on `nil`, auth disabled at a state no older than `n`, or the request's
principal an admin at one or allowed to write (`IsPutPermitted(k)`) every key of the lease `id` at a
lessor index no older than `m`; on an error, an error the gRPC layer can take. (The revision re-check,
`ErrAuthOldRevision`, refuses a check across an auth change; the class does not need it, each
verdict being at a state no older than `n`.) -/
abbrev EtcdServer.checkLeaseRenew.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (id : w64) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      lease.lessorLb γl m ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗ lease.lessorReader γl }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"checkLeaseRenew"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (err : GoInterface), RET #err; E.RD ∗ lease.lessorReader γl ∗ applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, leaseCheckFrom s E (GoInterface.ok ctx) n
        (fun info => leaseKeysVerdictFrom E.authMode n info γl m id .write)) }}

end spec

end EtcdGrove
end Perennial
