/-
`s.LeaseLeases(ctx, r)` (`v3_server.go`): the lease `Leases` row. Lean-first (no Rocq counterpart); the lease-read plan
(`notes/lease-read-plan.md`, 2026-10-31), vocabulary `LeaseRead.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

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

/-- **`s.LeaseLeases(ctx, r)`**, any goroutine, at a context, with the server's read-side facts and
its header's (`srvHeaderFacts`, a reader's slots of the store: `newHeader.spec`'s), the key check's
resources (`checkLeaseLeases.spec`'s: the auth store and lessor at lower bounds `n`, `m`, their
readers, a thread token; an execution of at most `2^62` steps, for `Leases()`' sort): on `nil`, the ids `ids` of the leases of the lease map at a lessor index `i`
no older than `m` (`leaseIdsAt`: all of them, each once), the response listing them with a fresh
header (`leasesRespIs`), and auth disabled at a state no older than `n`, or the request's principal
an admin at one or allowed to read every key of each lease at an index no older than `i`, the
listing's (`leaseKeysVerdictFrom`); on an error, no response and an error the gRPC layer can take.
The ids are listed in the order of `Leases()`' sort (by remaining time: none stated). The revision
re-check is not stated (`checkLeaseRenew.spec`'s margin). -/
abbrev EtcdServer.LeaseLeases.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γl : GName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (mid cid : w64) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReadM E.authOn s E γr ∗ srvHeaderFacts s cid mid ∗ mvcc.storeReader E.s E.γ ∗
      srvAuthAt s E ∗ srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ auth.authPubLbM E.authMode n ∗
      lease.lessorLb γl m ∗ context.isContext ctx cd ∗ E.RD ∗ lease.lessorRdPool γl ∗ threadTok ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗ ⌜receiptBound GF ≤ 2 ^ 62⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"LeaseLeases"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); mvcc.storeReader E.s E.γ ∗ E.RD ∗
      threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (i : Nat) (ids : List w64), ⌜m ≤ i⌝ ∗
          lease.leaseIdsAt γl i ids ∗ leasesRespIs E resp cid mid ids ∗
          leaseCheckFrom s E (GoInterface.ok ctx) n (fun info => iprop([∗list] id ∈ ids,
            leaseKeysVerdictFrom E.authMode n info γl i id .read))) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
