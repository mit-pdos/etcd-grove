/-
## `(*unstable).nextEntries` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__nextEntries.lean`: over `UnstableState`.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) The entries not yet in progress (aliasing the array, read-only). -/
def unstable.nextEntries.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState),
  us.Wf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us }}
    (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"nextEntries")) (Val #()))
  {{ (sl : GoSlice), RET #sl; unstable u us ∗ entriesRO sl us.offsetInProgress us.nextEntries }}

end spec
end Raft
end EtcdGrove
end Perennial
