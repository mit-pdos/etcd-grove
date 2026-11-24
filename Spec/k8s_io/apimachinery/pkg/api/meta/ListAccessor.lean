/-
`meta.ListAccessor(obj)` (`k8s.io/apimachinery/pkg/api/meta/meta.go:69-86`, apimachinery
`v0.0.0-20261021173754-0b7d352f711c`) of a value whose dynamic type is in `meta.List`'s type set
(`metav1.ListInterface`'s methods): the type switch's first case (`case List: return t, nil`)
returns the same interface value, as a `meta.List`, and a nil error. It reads nothing. Proved
from the translated body (`Proof/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean`; k8s 7g
follow-up (B'), `notes/k8s-7g-listaccessor-bprime.md`: until then a trust-boundary axiom with a
row for the reflector's typed lists and one for the k8s driver's `*ObjList`, and before 7g a named
hypothesis of the reflector's `list`). The shape of `Accessor.spec`.

A typed nil pointer of such a type (a nil `*ObjList`) is in the type set too, and Go returns it
unchanged: `TestListAccessorObjList` (`examples/k8s/etcd3/trustspecs_test.go`). A nil `obj`, or one
outside the type set, takes the other cases (`ListMetaAccessor`, `errNotList`), which no caller
reaches and the spec does not state.

Callers: the k8s driver's checker (`Model.listResponseRV`, `Model.equalListResponse`,
`Replay.validateList`, on its `*ObjList`), and client-go's pager (`ListPager.list`, on the
reflector's typed lists `*v1.PodList`, ...: their type-set membership and their promoted
`ListMeta` accessors are the reflector's pending hypothesis `cache.typedListMeta`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.meta.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimeta

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- **`meta.ListAccessor(x)`** of an `x` whose dynamic type is in `meta.List`'s type set: `x`
itself and `nil`. -/
abbrev ListAccessor.spec : Prop :=
  ∀ (ii : GoInterfaceOk),
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.«meta».List''.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».ListAccessor)) (Val #(GoInterface.ok ii)))
  {{ RET (PairV #(GoInterface.ok ii : k8s_io.apimachinery.pkg.api.«meta».List'')
      #(interface.nil : GoInterface)); True }}

end spec

end apimeta
end EtcdGrove
end Perennial
