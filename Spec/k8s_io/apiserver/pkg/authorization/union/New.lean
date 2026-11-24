/-
`union.New(handlers...)` (`union.go`): the union handler of the chain `handlers` (kept), or an
error (an empty or repeated name). The chain has at most `authzChainMax` authorizers, named in at
most `authzNameMax` bytes (`isUnionAuthz`: fmt stage 1). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.union.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  ∀ (s : GoSlice) (nas : List NamedAuthorizer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union ∗ s ↦*□ nas ∗ ([∗list] na ∈ nas, isAuthorizer na.Authorizer') ∗
      ⌜nas.length ≤ authzChainMax ∧ ∀ na ∈ nas, na.AuthorizerName'.length ≤ authzNameMax⌝ }}
    (App (Val (@! _root_.Perennial.k8s_io.apiserver.pkg.authorization.union.New)) (Val #s))
  {{ (a err : GoInterface), RET (PairV #a #err);
      ⌜err ≠ interface.nil⌝ ∨
      (⌜err = interface.nil⌝ ∗ ∃ h : unionAuthzHandler, ⌜a = interface.mkOk unionAuthzHandler.ty #h⌝ ∗ isUnionAuthz h) }}

end spec

end union
end EtcdGrove
end Perennial
