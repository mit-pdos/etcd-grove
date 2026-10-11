/-
`concurrency.Election.Proclaim(ctx, val)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
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

/-- **`e.Proclaim(ctx, val)`**, from any state, knowing etcd has reached `lo`:
* `nil`: the election had a leader session; its header is the transaction's; if the leader key is
  under the prefix (always, but after a failed `Proclaim`, which clears it), etcd's states at
  `r - 1` and `r ≥ lo` are a `ProclaimStep`: the guard `CreateRevision(key) = rev` held, and the key
  was put with `val` and the session's lease (`proclaimedAt`; `proclaimStep_guard`: for `rev > 0`,
  the key had create revision `rev`, and keeps it with the value `val`);
* `ErrElectionNotLeader`: no leader session, unchanged; or the guard failed: the leader key is
  cleared, and (if it was under the prefix) it is not there with create revision `rev` at some
  `r ≥ lo` (`notLeaderAt`);
* any other error, unchanged. -/
abbrev Election.Proclaim.spec : Prop :=
  ∀ (e s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : ElectionSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (val : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s γ client id pfx ∗
      electionState e s st ∗ context.isContext ctx cs ∗ etcdReached lo }}
    (App (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"Proclaim"))
      (Val #(GoInterface.ok ctx))) (Val #val))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil ∧ st.sess ≠ null⌝ ∗ ∃ hdr : Loc,
        electionState e s { st with hdr := hdr } ∗
        (⌜¬ pfx <+: st.key⌝ ∨ ∃ r : w64, hdrRevAt hdr r ∗ etcdReached r ∗
          proclaimedAt pfx st.key st.rev val id r ∗ ⌜sint.Z lo ≤ sint.Z r⌝)) ∨
      (isPkgErr ErrElectionNotLeader err ∗
        ((⌜st.sess = null⌝ ∗ electionState e s st) ∨
         (⌜st.sess ≠ null⌝ ∗ electionState e s { st with key := [] } ∗
          (⌜¬ pfx <+: st.key⌝ ∨ ∃ r : w64, etcdReached r ∗ notLeaderAt pfx st.key st.rev r ∗
            ⌜sint.Z lo ≤ sint.Z r⌝)))) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ electionState e s st) }}

end spec

end concurrency
end EtcdGrove
end Perennial
