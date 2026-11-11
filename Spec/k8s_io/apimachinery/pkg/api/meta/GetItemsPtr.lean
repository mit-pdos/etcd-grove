/-
`meta.GetItemsPtr(l)` (`k8s.io/apimachinery/pkg/api/meta/help.go:80-111`) of a non-nil `*ObjList`
(the k8s etcd3 driver's list type, `examples/k8s/etcd3`): the address of its `Items` field, as a
`*[]Obj` interface, and no error.

Faithful: `EnforcePtr` of a `*ObjList` gives the struct, `FieldByName("Items")` is valid and of
kind `Slice`, and `items.Addr().Interface()` is the field's address at type `*[]Obj`
(`TestGetItemsPtr`). The trust boundary (stage 7e-2, `notes/k8s-7e-2-draft.md` §5.3, attacked T13):
an axiom, `Proof/k8s_io/apimachinery/pkg/api/meta/GetItemsPtr.lean` (`help.go`'s reflection is not
translated). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]
variable [dpkg : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev apimeta.GetItemsPtr.spec : Prop :=
  ∀ (pl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗ ⌜pl ≠ null⌝ }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».GetItemsPtr))
      (Val #(interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #pl)))
  {{ RET (PairV #(interface.mkOk (go.GoType.PointerType
        (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty))
        #(structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList go!"Items" pl) : GoInterface)
      #GoInterface.nil); True }}

end spec

end EtcdGrove
end Perennial
