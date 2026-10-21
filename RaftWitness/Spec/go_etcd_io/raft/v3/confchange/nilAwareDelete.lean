/-
`confchange.nilAwareDelete(m, id)` deletes `id` from `*m`, nil'ing the map if it
becomes empty. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `nilAwareDelete(&m, id)`: `*m` (`nil` or a map) afterwards holds the set without `id`,
canonically (`ownIdsetC`): `nil` exactly when that set is empty. A `nil` map is left
alone (generalized 2026-10-12 from the `nil` case `makeVoter` met on `Restore`'s path). -/
abbrev confchange.nilAwareDelete.spec : Prop :=
  ∀ (mp m : Loc) (id : w64) (s : GSet w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ mp ↦ (m : GoMap) ∗ ownIdsetQ m (DFrac.own 1) s }}
    (App (App (Val #(functions confchange.nilAwareDelete [])) (Val #mp)) (Val #id))
  {{ (m' : Loc), RET #(); mp ↦ (m' : GoMap) ∗ ownIdsetC m' (DFrac.own 1) (GMap.delete id s) }}

end spec

end EtcdGrove
end Perennial
