/-
`MustPanicIsNilZeroValue()` (`examples/specreq/reflect/typednil.go`) never returns: it raises the Go panic that
`reflect.Value.IsNil` raises of the zero `Value` (`reflect.ValueOf` of a nil interface): Go's `&reflect.ValueError{"reflect.Value.IsNil", 0}` ("reflect: call of reflect.Value.IsNil on zero Value"). Lean-first (no Rocq counterpart); reflect S0.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace specreq_reflect

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.specreq.reflect

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.specreq.reflect.Assumptions]

/-- See the file header: the outcome is the panic `PanicV` of a `*reflect.ValueError`. -/
abbrev MustPanicIsNilZeroValue.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.specreq.reflect }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.specreq.reflect.MustPanicIsNilZeroValue)) (Val #()))
  {{ (r : val), RET r; ∃ (l : Loc),
      ⌜r = PanicV #(interface.mkOk (go.PointerType _root_.Perennial.reflect.ValueError.ty) #l)⌝ ∗
      l ↦ (_root_.Perennial.reflect.ValueError.mk go!"reflect.Value.IsNil" (W64 0)) }}

end spec

end specreq_reflect
end EtcdGrove
end Perennial
