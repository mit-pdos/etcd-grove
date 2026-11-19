/-
`value.NewValueInterface(v)`: a `value.Value` over the unstructured value `v` holds.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev value.NewValueInterface.spec : Prop :=
  ∀ (i : GoInterface) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isIface i x }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface)) (Val #i))
  {{ (v : value.Value), RET #v; isVal v x }}

end spec

end smd
end EtcdGrove
end Perennial
