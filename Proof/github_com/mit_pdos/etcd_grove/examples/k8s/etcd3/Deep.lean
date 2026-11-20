/-
Lean-first (no Rocq counterpart).

# The deep value of what the maintainers' checker passes to `reflect.DeepEqual` (k8s 7g step 1,
`notes/k8s-7g-trust.md`)

Trusted text: the vocabulary of `reflect.DeepEqual.spec_k8s` (`Spec/reflect/DeepEqualK8s.lean`).

`DeepV` is what `reflect.DeepEqual` compares of an interface value the checker builds from the
driver's objects and the errors the store and the checker's `Model` return: nothing of a nil
interface; of a `*Obj`, its struct; of a `*ObjList`, whether `Items` is nil and else its elements,
its resource version, its continue token, and whether `RemainingItemCount` is nil and else its
pointee; of a `*storage.StorageError`, its code, key, resource version and the deep value of its
(unexported) inner error; of an `*errors.errorString` (`errors.New`'s), its (unexported) text.
No other dynamic type has a deep value here: the spec says nothing of one.

`deepRep dq x d`: the interface value `x` has the deep value `d`, and the caller holds (with
fraction `dq`) every heap cell `DeepEqual` reads to compare it: the pointee of each pointer, the
elements `Items` holds (up to its length), `RemainingItemCount`'s pointee, and recursively the
inner error's. Each constructor fixes the dynamic type, so two values of different constructors
have different dynamic types, which `DeepEqual` never finds equal. Nil-ness of `Items` is
`= slice.nil`, the model's `== nil` on slices (`is_go_op_go_equals_slice_nil_l`), which is what
`DeepEqual`'s `IsNil` test reads; nil-ness of `RemainingItemCount` is `= null`.

`mapRep dq M D`: the map contents `M` (a `map[string]runtime.Object`'s) have the deep values `D`,
key by key (the same keys).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8sDeep

open Iris Iris.BI map

section pure
variable [GooseExts]

/-- **The deep value of an interface value** (see the file header). -/
inductive DeepV where
  /-- the nil interface -/
  | nil
  /-- a non-nil `*Obj` (the driver's object), its struct -/
  | obj (o : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
  /-- a non-nil `*ObjList`: `Items` (`none`: a nil slice), `ResourceVersion`, `Continue`,
  `RemainingItemCount` (`none`: a nil pointer) -/
  | list (items : Option (List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj))
      (rv : w64) (cont : GoString) (rem : Option w64)
  /-- a non-nil `*storage.StorageError`: `Code`, `Key`, `ResourceVersion`, the inner `err` -/
  | storageErr (code : w64) (key : GoString) (rv : w64) (inner : DeepV)
  /-- a non-nil `*errors.errorString`: its text -/
  | errString (s : GoString)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ObjList.Items` holds `items` (`none`: it is the nil slice). -/
def itemsRep (dq : DFrac) (sl : GoSlice) :
    Option (List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) → IProp GF
  | none => iprop(⌜sl = slice.nil⌝)
  | some xs => iprop(⌜sl ≠ slice.nil⌝ ∗ sl ↦*{dq} xs)

/-- `ObjList.RemainingItemCount` is `rem` (`none`: the nil pointer). -/
def remRep (dq : DFrac) (rp : Loc) : Option w64 → IProp GF
  | none => iprop(⌜rp = null⌝)
  | some n => iprop(rp ↦{dq} n)

/-- **The interface value `x` has the deep value `d`** (see the file header). -/
def deepRep (dq : DFrac) (x : GoInterface) : DeepV → IProp GF
  | .nil => iprop(⌜x = GoInterface.nil⌝)
  | .obj o => iprop(∃ p : Loc, ⌜x = interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty) #p⌝ ∗
      p ↦{dq} o)
  | .list items rv cont rem => iprop(∃ (p : Loc) (sl : GoSlice) (rp : Loc), ⌜x = interface.mkOk
      (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #p⌝ ∗
      p ↦{dq} github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.mk sl rv cont rp ∗
      itemsRep dq sl items ∗ remRep dq rp rem)
  | .storageErr code key rv inner => iprop(∃ (p : Loc) (e : GoInterface), ⌜x = interface.mkOk
      (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #p⌝ ∗
      p ↦{dq} k8s_io.apiserver.pkg.storage.StorageError.mk code key rv e ∗
      deepRep dq e inner)
  | .errString s => iprop(∃ p : Loc, ⌜x = interface.mkOk
      (go.GoType.PointerType errors.errorString.ty) #p⌝ ∗ p ↦{dq} errors.errorString.mk s)

/-- **A `map[string]runtime.Object`'s contents `M` have the deep values `D`**, key by key. -/
def mapRep (dq : DFrac) (M : GMap GoString GoInterface) (D : GMap GoString DeepV) : IProp GF :=
  iprop([∗map] _k ↦ x;d ∈ M;D, deepRep dq x d)

end defs

end k8sDeep
end EtcdGrove
end Perennial
