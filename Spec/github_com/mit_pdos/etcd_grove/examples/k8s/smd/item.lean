/-
`item(key)`: the path of the container named `key`.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI
open smd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- See the file header. -/
abbrev item.spec : Prop :=
  ∀ (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.smd }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8s.smd.item)) (Val #k))
  {{ (s : GoSlice), RET #s; isPath s (item k) }}

end spec

end k8s_smd
end EtcdGrove
end Perennial
