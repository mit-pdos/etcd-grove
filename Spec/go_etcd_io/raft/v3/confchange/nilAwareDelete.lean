/-
## `nilAwareDelete(m, id)` (internal)

**Users.** `makeVoter`, `remove`. Mirrors the code: `id` deleted, the map `nil` once empty.
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- (internal) Removes `id` from the set at `mp`, `nil` once empty. -/
def nilAwareDelete.spec : Prop :=
  ∀ (mp : Loc) (mv : GoMap) (s : GSet w64) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ mp ↦ mv ∗ Quorum.majorityOwn mv (DFrac.own 1) s }}
    (App (App (Val #(functions go_etcd_io.raft.v3.confchange.nilAwareDelete [])) (Val #mp)) (Val #id))
  {{ RET #(); ∃ mv', mp ↦ mv' ∗ Quorum.majorityOwn mv' (DFrac.own 1) (s \ {[id]}) ∗
      ⌜mv' = map.nil ↔ s \ {[id]} = ∅⌝ }}

end spec
end ConfChange
end EtcdGrove
end Perennial
