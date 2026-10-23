/- Lean-first (no Rocq counterpart).

`removeAt(pend, i)` (k8setcd3.go): a new slice, `pend` without its `i`-th input (`removeAtL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8setcd3


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev removeAt.spec : Prop :=
  ∀ (sl : GoSlice) (es : List Input) (dq : DFrac) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗ sl ↦*{dq} es ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8setcd3.removeAt)) (Val #sl)) (Val #i))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* removeAtL es (sint.nat i) ∗ ownSliceCap Input out (DFrac.own 1) }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
