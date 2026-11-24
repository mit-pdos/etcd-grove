/-
`t.String()` of the model's `rtype` of a type `T` (`reflect.TypeOf(x).String()` through the interface
`reflect.Type`): some string. The trust boundary (`rtype.String` is names-only in Perennial's model of
`reflect`, reflect S0): the part of `reflect.TypeOf`'s old axiom that its model does not prove.
Lean-first (no Rocq counterpart); for the Kubernetes etcd3 store's `getTypeName`
(`reflect.TypeOf(obj).String()`, a tracing attribute).
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev reflect.rtype.String.spec : Prop :=
  ∀ (T : go.GoType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
    (App (Val ((_root_.Perennial.reflect.rtype.mk (go.tok T)) @!! _root_.Perennial.reflect.rtype.ty
      @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
