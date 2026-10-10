/-
`concurrency.Election.Campaign(ctx, val)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
`InvElection.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`e.Campaign(ctx, val)`**, from any state, for a cancelable context (`waitDeletes` takes one),
knowing etcd has reached `lo`:
* `nil`: the election's key `key` (under the prefix), created at `rev`, with `val` as its value at a
  revision `rv` (`keyValAt`: put by the transaction, found there, or proclaimed), and at the revision
  `R ≥ rv` of `waitDeletes`' last `Get` no key under the prefix was created before `rev`; so `key`
  is the leader at `R` (`leaderAt pfx key rev R`) — **or it is not there any more**
  (`campaignLost`: deleted, or deleted and re-created, while `Campaign` waited): unlike
  `Mutex.Lock`, `Campaign` does not look at its key after the wait (see `notes/STATUS.md`,
  "Election"). The state holds `key`, `rev`, the session, and the transaction's header (revision
  `r`, `lo ≤ r ≤ R`);
* an error, in some state (the transaction failed, the proclamation failed and `Resign` ran, or the
  wait failed: then `Resign` ran if the context is done, otherwise the leader session is cleared). -/
abbrev Election.Campaign.spec : Prop :=
  ∀ (e s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : ElectionSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (val : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s γ client id pfx ∗
      electionState e s st ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      etcdReached lo }}
    (App (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"Campaign"))
      (Val #(GoInterface.ok ctx))) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (rev r rv R : w64) (hdr : Loc),
        electionState e s ⟨key, rev, s, hdr⟩ ∗ hdrRevAt hdr r ∗ etcdReached R ∗
        keyValAt pfx key rev val rv ∗ (leaderAt pfx key rev R ∨ campaignLost pfx key rev R) ∗
        ⌜pfx <+: key ∧ 0 < sint.Z rev ∧ sint.Z rev ≤ sint.Z r ∧ sint.Z lo ≤ sint.Z r ∧
          sint.Z r ≤ sint.Z rv ∧ sint.Z rv ≤ sint.Z R⌝) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ st' : ElectionSt, electionState e s st') }}

end spec

end concurrency
end EtcdGrove
end Perennial
