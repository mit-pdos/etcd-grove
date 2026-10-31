/-
`s.checkLeaseLeases(ctx, leases)` (`v3_server.go`): the key check of `LeaseLeases`. Lean-first (no Rocq counterpart); the lease-keys plan's
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

/-- **`s.checkLeaseLeases(ctx, leases)`**, any goroutine, for a slice of leases each a lease of some
id at a lessor index no older than `m` (what `Leases()` returns: its spec waits for the entry points,
`notes/lease-keys-plan.md`), with the resources of `checkLeaseTimeToLive.spec`: on `nil`, auth
disabled at a state no older than `n`, or the request's principal an admin at one or allowed to read
every key of each of the leases at a lessor index no older than `m`; on an error, an error the gRPC
layer can take. -/
abbrev EtcdServer.checkLeaseLeases.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (ls : List Loc) (dq : DFrac) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      mvcc.txnCtx ctx cd ∗ E.RD ∗ lease.lessorReader γl ∗ sl ↦*{dq} ls ∗
      ([∗list] l ∈ ls, ∃ id : w64, lease.isLeaseObj γl l ∗ lease.leaseLiveFrom γl m id l) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"checkLeaseLeases"))
      (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (err : GoInterface), RET #err; E.RD ∗ lease.lessorReader γl ∗ sl ↦*{dq} ls ∗ applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, leaseCheckFrom s E (GoInterface.ok ctx) n
        (fun info => iprop([∗list] l ∈ ls, ∃ (id : w64) (ks : List GoString),
          lease.leaseKeysFrom γl m id l ks ∗
          [∗list] k ∈ ks, auth.permVerdictFrom E.authMode n info k [] .read GoInterface.nil))) }}

end spec

end EtcdGrove
end Perennial
