/-
`(*storage.Preconditions).Check(key, obj)` (`k8s.io/apiserver/pkg/storage/interfaces.go:145`):
`nil` when the preconditions `pp` (`nil`: none) hold of the object `obj`'s UID and resource version
string (`KPre.ok`), else `NewInvalidObjError(key, _)` (`invalidErrIs`). The object is a
`metav1.Object` whose `GetUID`/`GetResourceVersion` answer `uid`/`rvs` (`metaAt`, which the
store's objects give, `ObjSpec.metaOk`), so `meta.Accessor`'s error branch is not reached; its
ownership `R` comes back. Lean-first (no Rocq counterpart). Stage 7b of
`notes/k8s-etcd3-plan.md` (before: `nil` preconditions only).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.Preconditions.Check.spec : Prop :=
  ∀ (pp : Loc) (p : KPre) (key : GoString) (obj : GoInterface) (R : IProp GF)
    (uid rvs : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ preAt pp p ∗
      metaAt obj R uid rvs ∗ R }}
    (App (App (Val (pp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.Preconditions.ty @!! go!"Check")) (Val #key)) (Val #obj))
  {{ (err : GoInterface), RET #err; R ∗
      (if p.ok uid rvs then ⌜err = GoInterface.nil⌝ else invalidErrIs err key) }}

end spec

end EtcdGrove
end Perennial
