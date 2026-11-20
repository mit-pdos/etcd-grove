/-
`meta.SetList(list, objects)` (`k8s.io/apimachinery/pkg/api/meta/help.go`, names-only: reflection)
on the driver's list (the checker's `Model.list`: `list := s.NewListFunc()`, the driver's
`newObjList`, a fresh `*ObjList`; `items` the `DeepCopyObject`s of `*Obj` items): returns `nil`
and sets `list.Items` to a fresh, non-nil slice of the objects' structs; nothing else changes.
Stated at this type only (`spec_objList`). Its axiom will be `meta.SetList.wp_proof_objList`
(k8s 7g, `notes/k8s-7g-trust.md`); not provable from Perennial's `reflect` axioms, which have no
`FieldByName`, `AssignableTo`, `Index` or `Addr`.

Faithful (`help.go:294-334`, `conversion/helper.go:27-39`, `help.go:89-111`): `GetItemsPtr(list)`:
`EnforcePtr(list)` (a non-nil pointer: its `Elem`, the `ObjList` struct), `FieldByName("Items")`
(a `[]Obj`, kind slice: `Addr().Interface()`, a `*[]Obj`); `EnforcePtr` of that: the `Items`
field. Its type `[]Obj` is not `[]runtime.Object`, so `MakeSlice([]Obj, n, n)` with `n` the
objects' count (non-nil even for `n = 0`: `MakeSlice` allocates its array, `unsafe_NewArray`);
for each `i`, `dest` is element `i` (type `Obj`, not `RawExtension`); `TypeOf(objects[i])` is
`*Obj`, not assignable to `Obj`; `EnforcePtr(objects[i])` is the pointee (non-nil pointer: no
error); `Obj` is assignable to `Obj`, so `dest.Set(src)` copies the struct; then
`items.Set(slice)` writes `Items`. The objects are only read (fraction `dqo`), the objects slice
too (`dq`); the other fields of the list are untouched. Reads `objectSliceType` and
`rawExtensionObjectType`, package variables: `isPkgInit`. Go evidence:
`examples/k8s/etcd3/trustspecs_test.go` `TestSetListObjList` (0 to 3 objects, nil and empty
`objects`: `nil` error, `Items` non-nil and the objects' copies, later writes to the objects not
seen, the other fields unchanged). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Deep
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI k8sDeep

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- See the file header. -/
abbrev meta.SetList.spec_objList : Prop :=
  ∀ (p : Loc) (l : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList) (objs : GoSlice)
    (xs : List GoInterface) (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
    (dq dqo : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗ p ↦ l ∗
      objs ↦*{dq} xs ∗ [∗list] x;o ∈ xs;os, deepRep dqo x (.obj o) }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».SetList))
      (Val #(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #p))) (Val #objs))
  {{ RET #(GoInterface.nil); ∃ sl : GoSlice, ⌜sl ≠ slice.nil⌝ ∗ p ↦ { l with Items' := sl } ∗
      sl ↦* os ∗ objs ↦*{dq} xs ∗ [∗list] x;o ∈ xs;os, deepRep dqo x (.obj o) }}

end spec

end EtcdGrove
end Perennial
