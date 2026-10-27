/- Lean-first (no Rocq counterpart).

`setItem(items, it)` (k8setcd3.go): a new slice, the items with `it` in key order, replacing
its key's (`setItemL`). Its premise bounds the length: `make([]item, 0, len(items)+1)` panics in
Perennial's model when `len(items) + 1` overflows.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev setItem.spec : Prop :=
  ∀ (sl : GoSlice) (its : List item) (dq : DFrac) (it : item),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ sl ↦*{dq} its ∗ ⌜its.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.setItem)) (Val #sl)) (Val #it))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} its ∗ out ↦* setItemL its it ∗ ownSliceCap item out (DFrac.own 1) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
