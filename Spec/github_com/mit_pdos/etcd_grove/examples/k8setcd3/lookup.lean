/- Lean-first (no Rocq counterpart).

`lookup(items, k)` (k8setcd3.go): `k`'s first item (`lookupL`).
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
abbrev lookup.spec : Prop :=
  ∀ (sl : GoSlice) (its : List item) (dq : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ sl ↦*{dq} its }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.lookup')) (Val #sl)) (Val #k))
  {{ (it : item) (ok : Bool), RET (PairV #it #ok); sl ↦*{dq} its ∗ ⌜(it, ok) = lookupL its k⌝ }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
