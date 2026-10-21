/- Lean-first (no Rocq counterpart).

`copyMap(m)` (check.go): a fresh map with `m`'s contents.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev copyMap.spec : Prop :=
  ∀ (l : Loc) (m : GMap GoString GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ l ↦${dq} m }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.copyMap)) (Val #l))
  {{ (c : Loc), RET #c; l ↦${dq} m ∗ c ↦$ m }}

end spec

end kv
end EtcdGrove
end Perennial
