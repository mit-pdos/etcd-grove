/- Lean-first (no Rocq counterpart).

`delItem(items, k)` (k8setcd3.go): a new slice, the items without `k`'s (`delItemL`).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev delItem.spec : Prop :=
  ∀ (sl : GoSlice) (its : List item) (dq : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ sl ↦*{dq} its }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.delItem)) (Val #sl)) (Val #k))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} its ∗ out ↦* delItemL its k ∗ ownSliceCap item out (DFrac.own 1) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
