/-
Lean-first (no Rocq counterpart).

# The driver's objects in the heap (stage 6c of `notes/k8s-etcd3-plan.md`)

`driverSpec`: the store's `ObjSpec` of the driver: `driverCodec` and the ownership of an object,
`objAtD x o rv`: the `runtime.Object` `x` is a non-nil `*Obj` holding `o`'s name and value and a
resource version whose string form is `rv` (`rvStr`). `reflect.New(Obj)`'s allocation is the
empty object (`newObj`, by `reflNew_pointsto` at `Obj`'s Lean type).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Codec
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8setcd3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProofMode k8s

section tyOk
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- **The method-set fact the store asks of the driver's objects** (`ObjSpec.tyOk`, without the
ghost state): `*Obj` is in `runtime.Object`'s type set (its methods `GetObjectKind` and
`DeepCopyObject`, `k8setcd3.go`) and not in `runtime.Unstructured`'s (it has no
`UnstructuredContent`). `methodSet` is uninterpreted in the model, so this is a premise of the
results (as `v3rpc.ServerMethodSets`). -/
def objTyOk : Prop :=
  go.typeSetContains (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.ty)
      k8s_io.apimachinery.pkg.runtime.Object.ty = true ∧
    go.typeSetContains (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.ty)
      k8s_io.apimachinery.pkg.runtime.Unstructured.ty = false

end tyOk

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- The driver's `*Obj` type. -/
abbrev objTyD : go.GoType := github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.ty

/-- **An object of the driver in the heap** (see the file header). -/
def objAtD (x : GoInterface) (o : DObj) (rv : GoString) : IProp GF :=
  iprop(∃ (p : Loc) (n : w64),
    ⌜x = interface.mkOk (go.GoType.PointerType objTyD) #p ∧ p ≠ null ∧ rv = rvStr n⌝ ∗
    p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk o.1.1 o.1.2 n)

theorem objAtD_ne_nil (x : GoInterface) (o : DObj) (rv : GoString) :
    objAtD (GF := GF) x o rv ⊢ ⌜x ≠ GoInterface.nil⌝ := by
  unfold objAtD
  iintro ⟨%p, %n, %h, -⟩
  ipureintro
  rw [h.1]
  nofun

theorem objAtD_ptr (x : GoInterface) (o : DObj) (rv : GoString) :
    objAtD (GF := GF) x o rv ⊢
      ⌜∃ p : Loc, p ≠ null ∧ x = interface.mkOk (go.GoType.PointerType objTyD) #p⌝ := by
  unfold objAtD
  iintro ⟨%p, %n, %h, -⟩
  ipureintro
  exact ⟨p, h.2.1, h.1⟩

theorem objAtD_new (p : Loc) :
    reflectM.reflNew (GF := GF) objTyD p ⊢
      |==> objAtD (interface.mkOk (go.GoType.PointerType objTyD) #p) dzero [] := by
  iintro H
  ihave H := reflectM.reflNew_pointsto (GF := GF) objTyD p
    (V := github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj) $$ H
  icases (typedPointsto_not_null_dup _ _ _) $$ H with ⟨H, %Hn⟩
  imodintro
  unfold objAtD
  iexists p, (W64 0)
  isplitr
  · ipureintro; exact ⟨rfl, Hn, rfl⟩
  have hz : (zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj) =
      github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk dzero.1.1 dzero.1.2 (W64 0) := rfl
  rw [← hz]
  iexact H

/-- **The store's `ObjSpec` of the driver.** -/
def driverSpec : ObjSpec GF DObj where
  toObjCodec := driverCodec
  objAt := objAtD
  objAt_ne_nil := objAtD_ne_nil
  objTy := objTyD
  objAt_ptr := objAtD_ptr
  newObj := objAtD_new
  encErr _ := False

theorem driverSpec_tyOk (h : objTyOk) : (driverSpec (GF := GF)).tyOk := h

end defs

end k8setcd3
end EtcdGrove
end Perennial
