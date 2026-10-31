/-
`s.checkLeaseTimeToLive(ctx, id)` (`v3_server.go`): the key check of `LeaseTimeToLive` with `Keys`. Lean-first (no Rocq counterpart); the lease-keys plan's
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

/-- **`s.checkLeaseTimeToLive(ctx, id)`**, any goroutine, with the server's auth store at the lease
checks' lower bounds (`srvAuthLeaseLb`) and its request side (`srvAuthAt`), its lessor (`srvLessorRd`),
a lower bound `n` of the auth store's published index and `m` of the lessor's history, and a reader
of each (`E.RD`, `lessorReader`): on `nil`, auth disabled at a state no older than `n`, or the
request's principal an admin at one or allowed to read (`IsRangePermitted(k, [])`) every key of the
lease `id` at a lessor index no older than `m` (`leaseKeysVerdictFrom`; none if `id` was not live
there); on an error, an error the gRPC layer can take. The returned revision is not stated (its one
use is `LeaseTimeToLive`'s re-check). The keys are the local lessor's: what `LeaseTimeToLive` then
returns comes from another lookup, possibly on the leader (`issues/etcd-lease-timetolive-keys-toctou.md`). -/
abbrev EtcdServer.checkLeaseTimeToLive.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (id : w64) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      lease.lessorLb γl m ∗ mvcc.txnCtx ctx cd ∗ E.RD ∗ lease.lessorReader γl }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"checkLeaseTimeToLive"))
      (Val #(GoInterface.ok ctx))) (Val #id))
  {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err); E.RD ∗ lease.lessorReader γl ∗
      applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, leaseCheckFrom s E (GoInterface.ok ctx) n
        (fun info => leaseKeysVerdictFrom E.authMode n info γl m id .read)) }}

end spec

end EtcdGrove
end Perennial
