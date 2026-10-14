/-
`concurrency.ResumeElection(s, pfx, leaderKey, leaderRev)` (`client/v3/concurrency/election.go`). Lean-first (no Rocq counterpart); see
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

/-- **`ResumeElection(s, pfx, leaderKey, leaderRev)`**, for a session `s` whose client answers for
the prefix `pfx` (not empty; unlike `NewElection`, no `/` is added): an election on `pfx` whose state
is the given leader key and create revision, with `s` as the leader session (nothing is checked:
the arguments are the caller's). -/
abbrev ResumeElection.spec : Prop :=
  ∀ (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx leaderKey : GoString)
    (leaderRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s γ client id ∗
      isEtcdMutexClient client pfx ∗ ⌜pfx ≠ []⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.ResumeElection)) (Val #s))
      (Val #pfx)) (Val #leaderKey)) (Val #leaderRev))
  {{ (e : Loc), RET #e; isElection e s γ client id pfx ∗
      electionState e s { key := leaderKey, rev := leaderRev, sess := s, hdr := null } }}

end spec

end concurrency
end EtcdGrove
end Perennial
