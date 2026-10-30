/-
`meta.LenList(list)` (`k8s.io/apimachinery/pkg/api/meta/help.go`, names-only): the number of the
list's items, `0` if it is not a list. **A named hypothesis, boundary pending approval** (one of the
reflector's `list` callees, for its trace; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round):
`?` in `etc/link-lean-first-k8scache.txt`. Stated for what the reflector passes it: `nil`, a typed
list's `nil` pointer, or a typed list (read, kept): some number.
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

/-- What `LenList` is passed: `nil`, a typed list's `nil` pointer `q`, or the typed list `q`. -/
def lenListArg (res : Res) (obj : GoInterface) (q : Loc) (os : List Obj) (rv : GoString) :
    IProp GF :=
  iprop(⌜obj = interface.nil⌝ ∨
    ⌜obj = interface.mkOk (go.GoType.PointerType (resListTy res)) #q ∧ q = null⌝ ∨
    (⌜obj = interface.mkOk (go.GoType.PointerType (resListTy res)) #q⌝ ∗ typedListAt res q os rv))

/-- `meta.LenList(list)`: some number; the list kept. -/
abbrev LenList.spec : Prop :=
  ∀ (res : Res) (obj : GoInterface) (q : Loc) (os : List Obj) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» ∗
      lenListArg res obj q os rv }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.«meta».LenList)) (Val #obj))
  {{ (n : w64), RET #n; lenListArg res obj q os rv }}

end spec

end apimeta
end EtcdGrove
end Perennial
