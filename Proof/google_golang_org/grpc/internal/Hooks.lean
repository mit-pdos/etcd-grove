/-
**grpc's `internal` hook variables** (phase7-inits, 2026-11-25, `notes/phase7-endstate.md` §4; the
mechanism of phase 7 S2 core's `FromOutRaw.lean`, for every hook): the laws of the hook cells'
invariant `hookInv` (`cache/v3/Base.lean`), which `internal`'s, `codes`', `metadata`'s and grpc's
generated `Init.lean` use. Lean-first.

Go: `internal`'s hook variables (`internal.go`, `experimental.go`; no initializers) are set by the
`init`s of other packages (`metadata`'s `FromOutgoingContextRaw = fromOutgoingContextRaw`, `codes`'
`CanonicalString = canonicalString`, grpc's function values and closures in `dialoptions.go`,
`rpc_util.go` and `server.go`) and read by no translated code. The cells are another package's:
`internal`'s initializer allocates them, the others' write them, and a package fact is persistent. So
each cell lives in an invariant (`hookCell`), from which a package initializer, which holds its
exclusive package state `ownGoState σ`, takes it out for a plain store by lending that state
(`hookCell_acc`).

The generic laws (dsv-retire-2, 2026-11-25: in `Proof/runtime/InitInv.lean`, shared with the part
`Dsverify/`):

* `initInv_alloc`, `initInv_acc`: an init-time invariant (`initInv`, `cache/v3/Base.lean`), from its
  resource; with a package state, the resource out of the invariant, and back (also `grpclog`'s
  `cache`, `Component`'s proof).
* `hookCell_alloc`: a freshly allocated cell gives its `hookCell`.
* `hookCell_acc`: with a package state, the cell out of the invariant, and back.
* `wp_store_hook`: a package initializer's store in a hook cell.
* `wp_store_hookAny`, `wp_store_hookFunc`: the same through `internalInit`, for a hook of `hooksAny`
  (an `any`) and of `hooksFunc` (a `func()`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.runtime.PkgInit
public import Proof.runtime.InitInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace grpcInternal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open _root_.Perennial.go_etcd_io.etcd.cache.v3 (initInv)
open _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal
  (hookN hookInv hookCell hookCells hooksAny hooksFunc internalInit)

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

-- `hookCell_persistent`, `ownGoState_excl`, `initInv_alloc`, `initInv_acc`, `hookCell_alloc`,
-- `hookCell_acc`, `wp_store_hook`, `hookCells_mem`: `Proof/runtime/InitInv.lean` (dsv-retire-2,
-- 2026-11-25), which this module imports

/-- **A package initializer's store in an `any` hook of `internal`.** -/
theorem wp_store_hookAny (x : GoString) (h : x ∈ hooksAny) (w : GoInterface)
    (g : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    {{ internalInit (hG := hG) ∗ EtcdGrove.ownInitLb g σ0 }}
      (App (Val (GoInstruction (GoStore go.any))) (Val (PairV #(globalAddr x) #w)))
    {{ RET #(); EtcdGrove.ownInitLb g σ0 }} := by
  wp_start as ⟨Hi, Hown⟩
  unfold internalInit
  icases Hi with ⟨Ha, -, -⟩
  ihave Hc := (hookCells_mem _ x h) $$ Ha
  wp_apply (wp_store_hook (V := GoInterface) (t := go.any) _ _ g σ0) $$ [Hc Hown] as Hown
  · iframe Hc Hown
  iapply HΦ; iexact Hown

/-- **A package initializer's store in a `func()` hook of `internal`.** -/
theorem wp_store_hookFunc (x : GoString) (h : x ∈ hooksFunc) {t : go.GoType}
    [IntoValTyped (GF := GF) GoFunc t] (w : GoFunc) (g : GoString → IProp GF) (σ0 : GMap GoString Bool) :
    {{ internalInit (hG := hG) ∗ EtcdGrove.ownInitLb g σ0 }}
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #(globalAddr x) #w)))
    {{ RET #(); EtcdGrove.ownInitLb g σ0 }} := by
  wp_start as ⟨Hi, Hown⟩
  unfold internalInit
  icases Hi with ⟨-, Hf, -⟩
  ihave Hc := (hookCells_mem _ x h) $$ Hf
  wp_apply (wp_store_hook (V := GoFunc) (t := t) _ _ g σ0) $$ [Hc Hown] as Hown
  · iframe Hc Hown
  iapply HΦ; iexact Hown

end laws

end grpcInternal
end EtcdGrove
end Perennial
