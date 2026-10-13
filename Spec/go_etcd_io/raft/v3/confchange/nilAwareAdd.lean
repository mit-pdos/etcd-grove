/-
`confchange.nilAwareAdd(m, id)` adds `id` to `*m`, allocating the map if `nil`.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
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

/-- `nilAwareAdd(&m, id)`: `*m` (`nil` or a map) afterwards a map (a fresh one if it was
`nil`) holding `id` too. -/
abbrev confchange.nilAwareAdd.spec : Prop :=
  ∀ (mp m : Loc) (id : w64) (s : GSet w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ mp ↦ (m : GoMap) ∗ ownIdsetQ m (DFrac.own 1) s }}
    (App (App (Val #(functions confchange.nilAwareAdd [])) (Val #mp)) (Val #id))
  {{ (m' : Loc), RET #(); mp ↦ (m' : GoMap) ∗ m' ↦$ (<[id := ()]> s) }}

end spec

end EtcdGrove
end Perennial
