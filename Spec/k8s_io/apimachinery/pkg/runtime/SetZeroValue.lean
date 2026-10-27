/-
`runtime.SetZeroValue(objPtr)` (`k8s.io/apimachinery/pkg/runtime/helper.go`; translated with its
body, stage 6c of `notes/k8s-etcd3-plan.md`) of a non-nil `*T` holding `x` (of a Lean type `V`
representing `T`): the pointee is `V`'s zero value, no error. Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]

/-- See the file header. -/
abbrev runtime.SetZeroValue.spec : Prop :=
  ∀ (T : go.GoType) (p : Loc) (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V T] (x : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ∗ ⌜p ≠ null⌝ ∗ p ↦ x }}
    (App (Val (@! k8s_io.apimachinery.pkg.runtime.SetZeroValue))
      (Val #(interface.mkOk (go.GoType.PointerType T) #p)))
  {{ RET #GoInterface.nil; p ↦ (zero_val V) }}

end spec

end EtcdGrove
end Perennial
