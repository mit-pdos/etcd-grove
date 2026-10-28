/-
`meta.ListAccessor(obj)` (`k8s.io/apimachinery/pkg/api/meta/meta.go`, names-only): the list's
metadata accessor. **A named hypothesis, boundary pending approval** (one of the reflector's `list`
callees, through the pager; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): `?` in
`etc/link-lean-first-k8scache.txt`.

What the code does, for a typed list of the model (`*v1.PodList`, ...): the type switch's first case
(`List`, `metav1.ListInterface`, which the list implements through its embedded `ListMeta`) returns
the list itself and no error; its `GetResourceVersion()` and `GetContinue()` (promoted from
`*ListMeta`, names-only) read the list's metadata: the version `rv` and the continue token, `""`
(`typedListAt`). Stated for that case only (the reflector's lists are those).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- **The list accessor of the typed list `q`** (persistent): `GetResourceVersion()` and
`GetContinue()` read its metadata (the list's ownership kept). -/
def listAccOk (res : Res) (q : Loc) (m : GoInterface) : IProp GF :=
  iprop(⌜m = interface.mkOk (go.GoType.PointerType (resListTy res)) #q⌝ ∗
    □ (∀ (os : List Obj) (rv : GoString) (Φ : val → IProp GF), typedListAt res q os rv -∗
      ▷ (typedListAt res q os rv -∗ Φ #rv) -∗
      WP (App (Val #(methods (go.GoType.PointerType (resListTy res)) go!"GetResourceVersion" #q))
        (Val #())) {{ Φ }}) ∗
    □ (∀ (os : List Obj) (rv : GoString) (Φ : val → IProp GF), typedListAt res q os rv -∗
      ▷ (typedListAt res q os rv -∗ Φ #(go!"")) -∗
      WP (App (Val #(methods (go.GoType.PointerType (resListTy res)) go!"GetContinue" #q))
        (Val #())) {{ Φ }}))

instance listAccOk_persistent (res : Res) (q : Loc) (m : GoInterface) :
    Persistent (listAccOk (GF := GF) res q m) := by
  unfold listAccOk; infer_instance

/-- `meta.ListAccessor(obj)` of a typed list: the list itself, no error. -/
abbrev ListAccessor.spec : Prop :=
  ∀ (res : Res) (q : Loc) (os : List Obj) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗
      typedListAt res q os rv }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».ListAccessor))
      (Val #(interface.mkOk (go.GoType.PointerType (resListTy res)) #q)))
  {{ (m err : GoInterface), RET (PairV #m #err); ⌜err = interface.nil⌝ ∗
      typedListAt res q os rv ∗ listAccOk res q m }}

end spec

end apimeta
end EtcdGrove
end Perennial
