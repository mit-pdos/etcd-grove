/-
`(*membership.RaftCluster).MemberByName(name)` (`cluster.go:155-168`; claim #34, stage 2, 2026-11-25:
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

/-- **`c.MemberByName(name)` of a cluster not yet shared** (its mutex owned and unlocked, its members
map at some fraction, no two members of one name, so no `lg.Panic`), the name a member's (`mm`, under
`k`): a fresh clone of that member, with its id; the mutex unlocked again. -/
abbrev membership.RaftCluster.MemberByName.spec : Prop :=
  ∀ (c : Loc) (q : Qp) (ms : GMap w64 Loc) (mem : GMap w64 apply.MemberM) (name : GoString)
    (k : w64) (mm : apply.MemberM),
  membership.memNamesUniq mem → mem !! k = some mm → mm.name = name →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt c q ms mem }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"MemberByName")) (Val #name))
  {{ (mc : Loc), RET #mc; membership.rcMutexAddr c ↦ (zero_val _root_.Perennial.sync.Mutex) ∗
      membership.memAt c q ms mem ∗ membership.memberIs mc mm.id }}

end spec

end EtcdGrove
end Perennial
