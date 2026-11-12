/-
`meta.ExtractListWithAlloc(list)` (`k8s.io/apimachinery/pkg/api/meta/help.go`, names-only): the
list's items as fresh `runtime.Object`s. **A named hypothesis, boundary pending approval** (one of
the reflector's `list` callees; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): `?` in
`etc/link-lean-first-k8scache.txt`.

What the code does, for a typed list of the model (`*v1.PodList`, ...: its items a slice of
structs `T`, which do not implement `runtime.Object`, `*T` does): for each item it allocates a new
`T` (`reflect.New`), copies the item into it (a shallow copy: nested pointers, slices and maps are
shared) and returns the `*T`s, no error. The items' deep ownership moves to the copies; the list's
own is given up (the reflector does not read the list again).
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimeta

open Iris Iris.BI apimodel cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- `meta.ExtractListWithAlloc(list)` of a typed list: its items, fresh, each owned deeply. -/
abbrev ExtractListWithAlloc.spec : Prop :=
  ∀ (res : Res) (q : Loc) (os : List Obj) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗
      typedListAt res q os rv }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».ExtractListWithAlloc))
      (Val #(interface.mkOk (go.GoType.PointerType (resListTy res)) #q)))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); ⌜err = interface.nil⌝ ∗
      ∃ xs : List GoInterface, sl ↦* xs ∗ [∗list] x;o ∈ xs;os, apimodel.objAt x (DFrac.own 1) o }}

end spec

end apimeta
end EtcdGrove
end Perennial
