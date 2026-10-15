/-
`concurrency.Election.Resign(ctx)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`e.Resign(ctx)`**, from any state, knowing etcd has reached `lo`:
* no leader session: `nil`, unchanged;
* otherwise the guarded delete (`CreateRevision(key) = rev`), and the leader key and session are
  cleared: `nil` with the transaction's header and (if the key was under the prefix) the key not
  there with create revision `rev` at the header's revision `R ≥ lo` (`notLeaderAt`: deleted, or
  the guard failed); or an error, the header unchanged. -/
abbrev Election.Resign.spec : Prop :=
  ∀ (e s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString) (st : ElectionSt)
    (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s γ client id pfx ∗
      electionState e s st ∗ context.isContext ctx cs ∗ etcdReached lo }}
    (App (Val (e @!! go.GoType.PointerType Election.ty @!! go!"Resign")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err;
      (⌜st.sess = null ∧ err = GoInterface.nil⌝ ∗ electionState e s st) ∨
      (⌜st.sess ≠ null ∧ err = GoInterface.nil⌝ ∗ ∃ hdr : Loc,
        electionState e s ⟨[], st.rev, null, hdr⟩ ∗
        (⌜¬ pfx <+: st.key⌝ ∨ ∃ R : w64, hdrRevAt hdr R ∗ etcdReached R ∗
          notLeaderAt pfx st.key st.rev R ∗ ⌜sint.Z lo ≤ sint.Z R⌝)) ∨
      (⌜st.sess ≠ null ∧ err ≠ GoInterface.nil⌝ ∗ electionState e s ⟨[], st.rev, null, st.hdr⟩) }}

end spec

end concurrency
end EtcdGrove
end Perennial
