/- Lean-first (no Rocq counterpart).

`(*Model).Equal(other)` (`correctness/model.go`): true iff the two models hold the same `RM`
(resource version, prefix, items by `reflect.DeepEqual`, `NeedsRewrite` by `maps.Equal`; both
`CompactResourceVersion`s are 0) (k8s 7g step 3: porcupine's `Equal`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev Model.Equal.spec : Prop :=
  ∀ (mp1 mp2 : Loc) (m1 m2 : RM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗ modelAt mp1 m1 ∗ modelAt mp2 m2 }}
    (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) go!"Equal" #mp1)) (Val #mp2))
  {{ (b : Bool), RET #b; ⌜b = true ↔ m1 = m2⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
