/-
`value.NewValueInterface(v)`: of an `interface{}` holding the unstructured value `x` (`ownU`:
`nil`, a `bool`, an `int64`, a `string`, a `[]interface{}` or a `map[string]interface{}` of
such), a `value.Value` holding `x` (a fresh `*valueUnstructured` from `HeapAllocator`, which never
reuses it: `ownValue`). Ownership of `v`'s data is persistent (read-only) on both sides.

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

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
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ ownU i x }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface)) (Val #i))
  {{ (v : value.Value), RET #v; ownValue v x }}

end spec

end smd
end EtcdGrove
end Perennial
