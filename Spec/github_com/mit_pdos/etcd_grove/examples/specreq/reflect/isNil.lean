/-
`isNil(msg)` (`examples/specreq/reflect/typednil.go`, etcd's `etcdserver/txn/util.go:105`:
`msg == nil || reflect.ValueOf(msg).IsNil()`) of the nil interface or of an interface holding a
pointer: true exactly of the nil interface and of an interface holding a nil pointer. Lean-first (no
Rocq counterpart); reflect S0.
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

/-- See the file header. -/
abbrev isNil.spec : Prop :=
  ∀ (msg : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.specreq.reflect ∗
      ⌜msg = interface.nil ∨ ∃ (T : go.GoType) (p : Loc), msg = interface.mkOk (go.PointerType T) #p⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.specreq.reflect.isNil)) (Val #msg))
  {{ (b : Bool), RET #b;
      ⌜b = true ↔ (msg = interface.nil ∨ ∃ (T : go.GoType), msg = interface.mkOk (go.PointerType T) #null)⌝ }}

end spec

end specreq_reflect
end EtcdGrove
end Perennial
