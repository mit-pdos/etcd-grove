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

/-- On a `nil` map `nilAwareDelete` returns at once, without writing. Stated for that
case only: `makeVoter` calls it on `Learners` and `LearnersNext`, both `nil` on this
path (`ConfigSimple`). -/
abbrev confchange.nilAwareDelete.spec : Prop :=
  ∀ (mp : Loc) (id : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ mp ↦{dq} (map.nil : GoMap) }}
    (App (App (Val #(functions confchange.nilAwareDelete [])) (Val #mp)) (Val #id))
  {{ RET #(); mp ↦{dq} (map.nil : GoMap) }}

end spec

end EtcdGrove
end Perennial
