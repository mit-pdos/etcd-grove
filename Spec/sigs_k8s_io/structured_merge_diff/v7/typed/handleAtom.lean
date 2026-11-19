/-
`typed.handleAtom(a, tr, ah)` (internal): calls the handler's method for the atom's kind
(`doMap`, `doScalar`, `doList`) and returns its errors. Stated over the handler's bundle for that
method (`atomHandlerOk`: the one triple the call uses), so one spec serves every walker. The
invalid-atom branch (an error) is excluded: the atom holds an `A`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.handleAtom.spec : Prop :=
  ∀ (a : schema.Atom) (A : Atom) (tr : schema.TypeRef) (T : go.GoType) (hv : val)
    (Pre : IProp GF) (Q : GoSlice → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isAtomOpt a (some A) ∗ Pre ∗ atomHandlerOk A a T hv Pre Q }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom)) (Val #a)) (Val #tr)) (Val #(interface.mkOk T hv)))
  {{ (errs : GoSlice), RET #errs; Q errs }}

end spec

end smd
end EtcdGrove
end Perennial
