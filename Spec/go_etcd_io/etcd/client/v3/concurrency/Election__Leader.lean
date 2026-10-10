/-
`concurrency.Election.Leader(ctx)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
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

/-- **`e.Leader(ctx)`** (`Get(pfx, WithFirstCreate()...)`), knowing etcd has reached `lo`:
* `nil`: the response, at a revision `R ≥ lo`, lists one key-value `v`, the leader at `R`
  (`leaderKvAt`: present, created no later than any key under the prefix);
* `ErrElectionNoLeader` (and a nil response): the prefix is empty at some `R ≥ lo`;
* any other error, and a nil response. -/
abbrev Election.Leader.spec : Prop :=
  ∀ (e s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s γ client id pfx ∗
      context.isContext ctx cs ∗ etcdReached lo }}
    (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"Leader")) (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (R : w64) (kp : Loc) (v : EtcdKv), getRespRev resp R ∗
        etcdReached R ∗ getRespOneKv resp kp v ∗ leaderKvAt pfx v R ∗ ⌜sint.Z lo ≤ sint.Z R⌝) ∨
      (⌜resp = null⌝ ∗ isPkgErr ErrElectionNoLeader err ∗ ∃ R : w64, etcdReached R ∗
        □ etcdState R pfx [] ∗ ⌜sint.Z lo ≤ sint.Z R⌝) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
