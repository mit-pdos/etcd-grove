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

/-- **`s.checkLeaseLeases(ctx, leases)`**, any goroutine, for a slice of leases `ls.map Prod.fst`, each
the lease of its id (`x.2`) at a lessor index no older than `m` (what `Leases()` returns: its spec waits for the entry points,
`notes/lease-keys-plan.md`), with the resources of `checkLeaseTimeToLive.spec`: on `nil`, auth
disabled at a state no older than `n`, or the request's principal an admin at one or allowed to read
every key of each lease `x.1` of `x.2` at a lessor index no older than `m`; on an error, an error the gRPC
layer can take. The revision re-check is not stated (`checkLeaseRenew.spec`'s margin). -/
abbrev EtcdServer.checkLeaseLeases.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (ls : List (Loc × w64)) (dq : DFrac) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      mvcc.txnCtx ctx cd ∗ E.RD ∗ lease.lessorRdPool γl ∗ threadTok ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ sl ↦*{dq} ls.map Prod.fst ∗
      ([∗list] x ∈ ls, lease.isLeaseObj γl x.1 ∗ lease.leaseLiveFrom γl m x.2 x.1) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"checkLeaseLeases"))
      (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (err : GoInterface), RET #err; E.RD ∗ threadTok ∗ sl ↦*{dq} ls.map Prod.fst ∗
      applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, leaseCheckFrom s E (GoInterface.ok ctx) n
        (fun info => iprop([∗list] x ∈ ls,
          leaseOfKeysVerdictFrom E.authMode n info γl m x.2 x.1 .read))) }}

end spec

end EtcdGrove
end Perennial
