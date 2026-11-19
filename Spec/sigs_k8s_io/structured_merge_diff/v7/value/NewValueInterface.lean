/-
`value.NewValueInterface(v)`: a `value.Value` over the unstructured value `v` holds: a fresh
wrapper (`HeapAllocator.allocValueUnstructured().reuse(v)`), owned whole (`isValF` at the full
fraction; `isValF_persist` gives the persistent `isVal` the other specs take).

Lean-first (2026-11-19, notes/smd-plan.md); round 1: the whole wrapper (was `isVal`).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
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
variable [package_sem : value.Assumptions]

/-- See the file header. -/
abbrev value.NewValueInterface.spec : Prop :=
  ∀ (i : GoInterface) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isIface i x }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface)) (Val #i))
  {{ (v : value.Value), RET #v; isValF v (DFrac.own 1) x }}

end spec

end smd
end EtcdGrove
end Perennial
