/-
`(*membership.RaftCluster).MemberIDs()` (`cluster.go:170-179`; claim #34, stage 2, 2026-11-25:
translated with its body). Lean-first.
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

/-- **`c.MemberIDs()` of a cluster not yet shared** (its mutex owned and unlocked, its members map at
some fraction, each member under its id, at most `2^62` of them: `sort.Sort`'s bound): the sorted
ids (`idsSorted`), a fresh slice; the mutex unlocked again. (The shared cluster's `MemberIDs`, under
its lock invariant, is not specified: no proved caller.) -/
abbrev membership.RaftCluster.MemberIDs.spec : Prop :=
  ∀ (c : Loc) (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM),
  membership.memIdsOk mem → GMap.size ms ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt c q ms mem }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"MemberIDs")) (Val #()))
  {{ (sl : GoSlice), RET #sl; membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt c q ms mem ∗ ∃ ids : List w64, sl ↦* ids ∗ ⌜membership.idsSorted mem ids⌝ }}

end spec

end EtcdGrove
end Perennial
