/-
`isMemberBootstrapped(lg, cl, member, rt, timeout)` (`cluster_util.go:41-55` at the etcd pin; names
only, `notes/bootstrap-proof-plan.md` §7.4: stage 4's, not proved yet, a hypothesis of the results
that reach it). Lean-first; claim #34, stage 2 (2026-11-25), for `bootstrapNewClusterNoWAL`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`isMemberBootstrapped(lg, cl, name, rt, timeout)`** of a cluster not yet shared (its mutex
owned and unlocked, its members at some fraction, no two of one name, `name` a member's), a zap
logger and a round tripper of some network `H`: some boolean, the cluster's fields given back. Go:
`getRemotePeerURLs(cl, name)` (`cl.Members()`, the other members' peer URLs, sorted),
`getClusterFromRemotePeers` (a `GET /members` to each through `rt`, `json.Unmarshal` of the answer,
errors logged), then `cl.MemberByName(name).ID` and the remote cluster's member of that id; it reads
the cluster and writes nothing of it. -/
abbrev isMemberBootstrapped.spec : Prop :=
  ∀ (lg cl : Loc) (name : GoString) (H : http.HttpNet GF) (prt : GoInterface) (tmo : w64) (q : Qp)
    (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM),
  membership.memNamesUniq mem → (∃ k mm, mem !! k = some mm ∧ mm.name = name) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ zapLoggerOk lg ∗
      http.roundTripperOk H prt ∗
      membership.rcMutexAddr cl ↦ (zero_val _root_.Perennial.sync.Mutex) ∗ membership.memAt cl q ms mem }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isMemberBootstrapped))
      (Val #lg)) (Val #cl)) (Val #name)) (Val #prt)) (Val #tmo))
  {{ (b : Bool), RET #b; membership.rcMutexAddr cl ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt cl q ms mem }}

end spec

end EtcdGrove
end Perennial
