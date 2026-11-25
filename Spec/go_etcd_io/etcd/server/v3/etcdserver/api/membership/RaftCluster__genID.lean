/-
`(*membership.RaftCluster).genID()` (`cluster.go:228-236`; claim #34, stage 2, 2026-11-25: translated
with its body, over Perennial's proved `crypto/sha1.Sum`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`c.genID()` of a cluster not yet shared** (as `MemberIDs`), the `fips140` GODEBUG setting off:
`c.cid` is `clusterIdOf` the sorted ids. -/
abbrev membership.RaftCluster.genID.spec : Prop :=
  ∀ (c : Loc) (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) (cid0 : w64),
  crypto.fips140.GodebugFips140Off → membership.memIdsOk mem → GMap.size ms ≤ 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt c q ms mem ∗ membership.rcCidAddr c ↦ cid0 }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"genID")) (Val #()))
  {{ RET #(); membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt c q ms mem ∗
      ∃ ids : List w64, ⌜membership.idsSorted mem ids⌝ ∗
        membership.rcCidAddr c ↦ membership.clusterIdOf ids }}

end spec

end EtcdGrove
end Perennial
