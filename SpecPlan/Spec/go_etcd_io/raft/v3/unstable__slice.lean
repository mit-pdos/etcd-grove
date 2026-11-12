/-
## `(*unstable).slice` (internal)

The embedded `unstable` of a `raftLog` (`raftLog`'s realization holds `unstable` of its field).
Users: `raftLog`'s methods only. Mirrors the code over `UnstableState`.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/unstable__slice.lean`: over `UnstableState`.
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

/-- (internal) The entries `[lo, hi)`, capped (no spare capacity). -/
def unstable.slice.spec : Prop :=
  ∀ (u : Loc) (us : UnstableState) (lo hi : w64),
  us.offset ≤ uint.nat lo → uint.nat lo ≤ uint.nat hi →
  uint.nat hi ≤ us.offset + us.ents.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ unstable u us }}
    (App (App (Val (u @!! go.GoType.PointerType go_etcd_io.raft.v3.unstable.ty @!! go!"slice")) (Val #lo)) (Val #hi))
  {{ (sl : GoSlice), RET #sl; unstable u us ∗ ⌜sl.len = sl.cap⌝ ∗
      entriesRO sl (uint.nat lo) ((us.ents.drop (uint.nat lo - us.offset)).take
        (uint.nat hi - uint.nat lo)) }}

end spec
end Raft
end EtcdGrove
end Perennial
