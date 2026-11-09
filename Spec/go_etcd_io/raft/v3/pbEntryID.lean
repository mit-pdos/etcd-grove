/-
## `pbEntryID(entry)` (internal; `types.go`)

**Users**: `findConflict`. Mirrors the code. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/pbEntryID.lean`: over the
provisional `entryRO`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) The entry's id. -/
def pbEntryID.spec : Prop :=
  ∀ (p : Loc) (k : Nat) (e : LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entryRO p k e }}
    (App (Val (@! go_etcd_io.raft.v3.pbEntryID)) (Val #p))
  {{ RET #(go_etcd_io.raft.v3.entryID.mk e.term (W64 k)); True }}

end spec
end Raft
end EtcdGrove
end Perennial
