/- Lean-first (no Rocq counterpart).

`removeAt(pend, i)` (k8s_etcd3.go): a new slice, `pend` without its `i`-th input (`removeAtL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev removeAt.spec : Prop :=
  ∀ (sl : GoSlice) (es : List Input) (dq : DFrac) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ sl ↦*{dq} es ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.removeAt)) (Val #sl)) (Val #i))
  {{ (out : GoSlice), RET #out;
      sl ↦*{dq} es ∗ out ↦* removeAtL es (sint.nat i) ∗ ownSliceCap Input out (DFrac.own 1) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
