/-
**The pager's contracts** (`k8s.io/client-go/tools/pager`; phase 4 of `notes/k8s-daemonset-plan.md`,
fifth round): what the reflector's list path through the pager is stated with. Lean-first.

* `pageRes res S obj err`: a page's (and the pager's) result: an error, printable (`fmtErrorOkOrNil`;
  `fmt.argOk` until fmt soundness 2, 2026-11-18: `Errorf`'s `%w` of it needs `Error() string`)
  and one `apierrors`' checks may read (`apierrors.apiErrOk`: the pager asks
  `apierrors.IsResourceExpired` of it; the apierrors-fix stage, 2026-11-17), with no list (`nil`, or a typed list's `nil` pointer); or no error and a typed list of resource
  `res` (`typedListAt`, which has no continue token) with the caller's facts `S` about it.
* `fnOk fn res S` (persistent): `fn(opts)` (the reflector's closure over its list-watch) returns a
  `pageRes`, the options kept; `pfnOk` the same for a `ListPageFunc` `fn(ctx, opts)`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs
public import Spec.fmt.ErrorOk
public import Proof.k8s_io.apimachinery.pkg.api.errors.View

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI apimodel cache

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A list's result**: see the file header. -/
def pageRes (res : Res) (S : Loc → List Obj → GoString → IProp GF) (obj err : GoInterface) :
    IProp GF :=
  iprop((⌜err ≠ interface.nil ∧ (obj = interface.nil ∨
        obj = interface.mkOk (go.GoType.PointerType (resListTy res)) #(null : Loc))⌝ ∗
      fmtErrorOkOrNil err ∗ apierrors.apiErrOk err) ∨
    (⌜err = interface.nil⌝ ∗ ∃ (q : Loc) (os : List Obj) (rv : GoString),
      ⌜obj = interface.mkOk (go.GoType.PointerType (resListTy res)) #q⌝ ∗
      typedListAt res q os rv ∗ S q os rv))

open Iris.ProofMode in
/-- A page result's error is `nil` or one `apierrors`' checks may read. -/
theorem pageRes_errOk (res : Res) (S : Loc → List Obj → GoString → IProp GF) (obj err : GoInterface) :
    pageRes res S obj err ⊢
      (⌜err = interface.nil⌝ ∨ apierrors.apiErrOk err) ∗ pageRes res S obj err := by
  unfold pageRes
  iintro (⟨%h, Hae, #Hok⟩ | ⟨%he, H⟩)
  · isplitr
    · iright; iexact Hok
    ileft; iframe Hae; isplitr
    · ipureintro; exact h
    iexact Hok
  · isplitr
    · ileft; ipureintro; exact he
    iright; isplitr
    · ipureintro; exact he
    iexact H

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

section underlying
variable [GooseExts] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [meta_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]

/-- **`meta.List`'s underlying interface** (`type List metav1.ListInterface`): two named types
deep, which Perennial's `≤u` (one `UnderlyingDirectedEq` step, no transitivity) does not reach, so
an interface method call on a `meta.List` does not step without it. Proved from the two
packages' type assumptions (`notes/perennial-changes.md`). -/
instance metaList_underlying :
    go.UnderlyingEq k8s_io.apimachinery.pkg.api.«meta».List''.ty
      k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.underlying :=
  ⟨(go.UnderlyingDirectedEq.underlying_unfold (t := k8s_io.apimachinery.pkg.api.«meta».List''.ty)).trans
    (go.UnderlyingDirectedEq.underlying_unfold
      (t := k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty))⟩

end underlying

end pager
end EtcdGrove
end Perennial
