/-
`meta.ListAccessor(obj)` (`k8s.io/apimachinery/pkg/api/meta/meta.go`, names-only): the list's
metadata accessor. **A trust-boundary axiom** (`Proof/k8s_io/apimachinery/pkg/api/meta/ListAccessor.lean`;
k8s 7g, decided by etcd-grove-03 2026-11-19, option A; before, a named hypothesis of the reflector's
`list`, through the pager, phase 4 of `notes/k8s-daemonset-plan.md`, fifth round).

What the code does, for a typed list of the model (`*v1.PodList`, ...): the type switch's first case
(`List`, `metav1.ListInterface`, which the list implements through its embedded `ListMeta`) returns
the list itself and no error; its `GetResourceVersion()` and `GetContinue()` (promoted from
`*ListMeta`, names-only) read the list's metadata: the version `rv` and the continue token, `""`
(`typedListAt`). Stated for that case (the reflector's lists are those) and, in a second row, for
the k8s driver's `*ObjList` (`examples/k8s/etcd3`, the maintainers' checker's `Model.list` results:
`listResponseRV`, `equalListResponse`, `validateList`; k8s 7g step 3 STOP 2b, option (B), decided by
etcd-grove-03): `*ObjList` has the methods of `metav1.ListInterface` (`GetResourceVersion`,
`SetResourceVersion`, `GetSelfLink`, `SetSelfLink`, `GetContinue`, `SetContinue`,
`GetRemainingItemCount`, `SetRemainingItemCount`, `k8setcd3.go`), so the type switch's first case
(`case List: return t, nil`, `meta.go:69-86`, apimachinery `v0.0.0-20261021173754-0b7d352f711c`)
returns the same interface value (type `*ObjList`, the same pointer, nil included) and a nil
error, reading nothing; the methods the caller then calls on it are translated driver code. Go
evidence: `examples/k8s/etcd3/trustspecs_test.go` `TestListAccessorObjList` (a fresh list, a list
with items and metadata, and a nil `*ObjList`: the result is the same pointer, error nil, and its
`GetContinue`/`SetContinue` act on the list).
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs
public import Proof.k8s_io.apimachinery.pkg.api.meta.Init
public import Code.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

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

/-- `meta.ListAccessor(obj)` of a typed list: the list itself, no error; of the k8s driver's
`*ObjList` (second row, any pointer, no ownership: nothing is read): the same interface value, no
error. See the file header. -/
abbrev ListAccessor.spec : Prop :=
  (∀ (res : Res) (q : Loc) (os : List Obj) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗
      typedListAt res q os rv }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».ListAccessor))
      (Val #(interface.mkOk (go.GoType.PointerType (resListTy res)) #q)))
  {{ (m err : GoInterface), RET (PairV #m #err); ⌜err = interface.nil⌝ ∗
      typedListAt res q os rv ∗ listAccOk res q m }}) ∧
  (∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».ListAccessor))
      (Val #(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #l)))
  {{ (m err : GoInterface), RET (PairV #m #err);
      ⌜m = interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #l ∧ err = interface.nil⌝ }})

end spec

end apimeta
end EtcdGrove
end Perennial
