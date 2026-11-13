/-
**etcd's `*cancellableContext` is a weak handler context** (k8s 7f-4, step 4). Lean-first.

`v3rpc.srvCtxWeak_cc`: from the handle (`v3rpc.ccHandle l c1 cd`) and `Err`'s triple
(`v3rpc.cancellableContext.Err.spec`), the wrapper `l` is a weak context described by `cd`
(`srvCtxWeak (ccCtx l) cd`): `Deadline`, `Done` and `Value` are promoted to the embedded
`WithCancel` child `c1` (`rw [method_unfold]`, the field load, `c1`'s `isContext` clause); `Err` is
the wrapper's own (its triple, at `b = false` and `b = true`); the Done channel's freshness and
`closedchan` are `c1`'s; `parentCancelCtx(l)` returns `c1`'s `*cancelCtx`, re-proved from its code
as Perennial's `context.wp_parentCancelCtx_self_of`, the wrapper's `Done`/`Value` stepping to
`c1`'s.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext__Err

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The wrapper is a weak context** (see the file header). -/
theorem v3rpc.srvCtxWeak_cc
    (wp_Err : v3rpc.cancellableContext.Err.spec (GF := GF) (hG := hG))
    (l : Loc) (c1 : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.ccHandle l c1 cd ⊢ srvCtxWeak (v3rpc.ccCtx l) cd := by
  iintro ⟨#Hpkg, #Hh⟩
  ihave #Hh' := Hh
  iunfold v3rpc.ccHandle at Hh'
  icases Hh' with ⟨%c, %γ, %cancel, %e, %γp, %Hc1, %Hγ, #Hf, #Hcf, #Hctx, #Hcc, #Hcancel, #HnL,
    #Hguard, #Hpool⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hctx' := Hctx
  iunfold context.isContext at Hctx'
  iunfold context.isContextDef at Hctx'
  icases Hctx' with ⟨#HDeadline, #HDone, -, #HValue, -, #HDoneFresh, -, #Hcci⟩
  unfold srvCtxWeak
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    rw [method_unfold (t := go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty)]
    wp_auto
    iapply HDeadline $$ []
    · itrivial
    inext
    iexact HΦ
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    rw [method_unfold (t := go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty)]
    wp_auto
    iapply HDone $$ []
    · itrivial
    inext
    iexact HΦ
  isplitl []
  · imodintro
    iintro %Φ Htok HΦ
    iapply wp_Err l c1 cd false $$ [Htok]
    · iframe #; iframe
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    inext
    iintro %err ⟨Htok, -⟩
    iapply HΦ $$ Htok
  isplitl []
  · imodintro
    iintro %Φ - HΦ
    rw [method_unfold (t := go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty)]
    wp_auto
    iapply HValue $$ []
    · itrivial
    inext
    iexact HΦ
  isplitl []
  · imodintro
    iintro %Φ #Hcl Htok HΦ
    iapply wp_Err l c1 cd true $$ [Htok]
    · iframe #; iframe
      simp only [↓reduceIte]
      iexact Hcl
    inext
    iintro %err ⟨Htok, Hp⟩
    simp only [↓reduceIte]
    icases Hp with ⟨%Hne, #He⟩
    iapply HΦ $$ [] He Htok
    ipureintro; exact Hne
  isplitl []
  · iexact HDoneFresh
  isplitl []
  · isplitl []
    · ipureintro
      unfold _root_.Perennial.context.stopCtx.ty
      intro h; cases h
    · imodintro
      iintro %ch %cch %Φ #Hd #Hcch %hne HΦ
      subst Hc1 Hγ
      wp_func_call
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty) (m := go!"Done")]
      wp_auto
      wp_apply _root_.Perennial.context.wp_cancelCtx_Done c _ _ $$ [$Pctx $Hcc] as %ch' %γch' ⟨#Hd', -⟩
      ihave #Hdd' := _root_.Perennial.context.isContextDone_doneGn _ _ _ $$ Hd'
      ihave %heq := dghostVar_agree _ _ _ _ _ $$ Hd Hdd'
      cases heq
      ihave #Hch := _root_.Perennial.context.isContextDone_is_chan _ _ _ $$ Hd'
      ihave %hnn := _root_.Perennial.context.isChan_ne_nil _ _ $$ Hch
      rw [decide_eq_false hne]
      wp_auto
      rw [decide_eq_false hnn]
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty) (m := go!"Value")]
      wp_auto
      wp_apply _root_.Perennial.context.wp_cancelCtx_Value c _ _ $$ [$Pctx $Hcc]
      wp_apply _root_.Perennial.context.wp_done_Load_known c _ _ ch $$ [$Pctx $Hcc $Hd]
      iapply HΦ
      unfold _root_.Perennial.context.isCancelCtx
      iexists _, _
      iexact Hcc
  · iexact Hcci

end laws

end EtcdGrove
end Perennial
