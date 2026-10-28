/-
**The pager's contracts** (`k8s.io/client-go/tools/pager`; phase 4 of `notes/k8s-daemonset-plan.md`,
fifth round): what the reflector's list path through the pager is stated with. Lean-first.

* `pageRes res S obj err`: a page's (and the pager's) result: an error, printable (`fmt.argOk`),
  with no list (`nil`, or a typed list's `nil` pointer); or no error and a typed list of resource
  `res` (`typedListAt`, which has no continue token) with the caller's facts `S` about it.
* `fnOk fn res S` (persistent): `fn(opts)` (the reflector's closure over its list-watch) returns a
  `pageRes`, the options kept; `pfnOk` the same for a `ListPageFunc` `fn(ctx, opts)`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI apimodel cache

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A list's result**: see the file header. -/
def pageRes (res : Res) (S : Loc → List Obj → GoString → IProp GF) (obj err : GoInterface) :
    IProp GF :=
  iprop((⌜err ≠ interface.nil ∧ (obj = interface.nil ∨
        obj = interface.mkOk (go.GoType.PointerType (resListTy res)) #(null : Loc))⌝ ∗
      fmt.argOk err) ∨
    (⌜err = interface.nil⌝ ∗ ∃ (q : Loc) (os : List Obj) (rv : GoString),
      ⌜obj = interface.mkOk (go.GoType.PointerType (resListTy res)) #q⌝ ∗
      typedListAt res q os rv ∗ S q os rv))

/-- **A list function `fn(opts)`** returns a `pageRes` (persistent). -/
def fnOk (fn : GoFunc) (res : Res) (S : Loc → List Obj → GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (dq : DFrac)
      (lo : kd.meta.ListOptions) (Φ : val → IProp GF),
    kd.meta.ListOptions.own opts dq lo -∗
    ▷ (∀ (obj err : GoInterface), kd.meta.ListOptions.own opts dq lo -∗ pageRes res S obj err -∗
      Φ (PairV #obj #err)) -∗
    WP (App (Val #fn) (Val #opts)) {{ Φ }})

instance fnOk_persistent (fn : GoFunc) (res : Res) (S : Loc → List Obj → GoString → IProp GF) :
    Persistent (fnOk fn res S) := by
  unfold fnOk; infer_instance

/-- **A `ListPageFunc` `fn(ctx, opts)`** returns a `pageRes` (persistent). -/
def pfnOk (fn : GoFunc) (res : Res) (S : Loc → List Obj → GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions)
      (dq : DFrac) (lo : kd.meta.ListOptions) (Φ : val → IProp GF),
    kd.meta.ListOptions.own opts dq lo -∗
    ▷ (∀ (obj err : GoInterface), kd.meta.ListOptions.own opts dq lo -∗ pageRes res S obj err -∗
      Φ (PairV #obj #err)) -∗
    WP (App (App (Val #fn) (Val #ctx)) (Val #opts)) {{ Φ }})

instance pfnOk_persistent (fn : GoFunc) (res : Res) (S : Loc → List Obj → GoString → IProp GF) :
    Persistent (pfnOk fn res S) := by
  unfold pfnOk; infer_instance

end defs

end pager
end EtcdGrove
end Perennial
