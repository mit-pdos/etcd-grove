/-
**A `channelContext` is a context the client takes** (2026-11-04, K4 of
`notes/k8s-compactor-plan.md`: Kubernetes' compactor loop runs its rounds under
`wait.ContextForChannel(stopCh)`). Lean-first.

`ContextForChannel(sc)` returns `channelContext{stopCh: sc}`, whose `Err()` is `nil` while `sc` is
open and `context.Canceled` once it is closed (`Spec/k8s_io/apimachinery/pkg/util/wait/`). It is no
`isContext` (Perennial's model: `parentCancelCtx` of an `isContext` finds a `*cancelCtx`, which
`channelContext.Value` does not give) and not quiet, but it meets grpc's `ctxErrs` (`ctxOk`'s third
case): at the descriptor `chanCd γi`, whose closed flag is the channel's done flag (its internal
names `γi`, `BroadcastInternal.lean`), the context is closed exactly when `sc` is, and
`Canceled`'s value is a client error grpc's `status` accepts (`canceledOk_of_init`: from
`context`'s package fact, an `*errorString` whose cell holds `"context canceled"`, and Perennial's
`wp_isCtxErr_Error`).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Err
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Perennial.Proof.context.NewErrorString

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `channelContext{stopCh: sc}` as a `context.Context`. -/
abbrev chanCtxVal (sc : GoChan) : GoInterfaceOk :=
  ⟨k8s_io.apimachinery.pkg.util.wait.channelContext.ty,
    #(k8s_io.apimachinery.pkg.util.wait.channelContext.mk sc)⟩

/-- The descriptor of a `channelContext` over a broadcast channel with internal names `γi`: closed
when the channel is (its done flag). -/
abbrev chanCd (γi : BroadcastInternalNames) : context.ContextDesc (IProp GF) :=
  ⟨∅, none, ⟨γi.doneGn, γi.doneGn⟩, iprop(True)⟩

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctx_sem : context.Assumptions] [errors_sem : _root_.Perennial.errors.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions] [rp_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
variable [peer_sem : google_golang_org.grpc.peer.Assumptions] [cl_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`context.Canceled`'s value is a client error grpc's `status` accepts** (see the file
header). -/
theorem canceledOk_of_init
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ globalAddr context.Canceled ↦□ e ⊢
      ⌜e ≠ GoInterface.nil ∧ clientErr e⌝ ∗ statusErrOk e ∗ errCellOk e := by
  iintro ⟨#Pctx, #He⟩
  ihave Hci : (context.isInit : IProp GF) $$ []
  · iapply context.isInit_access $$ Pctx
  iNamed Hci
  icases HCanceledCell with ⟨%x, #Hx, #Hcell⟩
  icombine He Hx gives %Heq
  subst Heq
  ihave #Hm : EtcdGrove.errMsgOk (GF := GF)
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ $$ []
  · iunfold EtcdGrove.errMsgOk
    iintro %Φ !> - HΦ
    iapply (context.wp_isCtxErr_Error
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) _ rfl) $$ [] HΦ
    unfold context.isCtxErr
    ileft
    iframe Hx
    iexists x
    iframe Hcell
    ipureintro; rfl
  have hl := errorString_leaf x
  have hty : go.GoType.PointerType _root_.Perennial.errors.errorString.ty ≠
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty := by
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
  ihave ⟨%Hc, #Hs⟩ := client.clientErr_statusErrOk_of_leaf _ hl.2.1 hl.2.2
    ErrorStringNoGRPCStatus.noGRPCStatus hty hAs $$ Hm
  isplitr
  · ipureintro; exact ⟨nofun, Hc⟩
  iframe Hs
  iapply errCellOk_of_cell x _ (by simp [clientErrMsgs]) $$ Hcell

/-- **A `channelContext` over a broadcast channel is a context the client takes** (see the file
header): `ctxOk` (its third case, `ctxErrs`) and `ctxErrClient`, at `chanCd γi`. -/
theorem chanCtx_ok (wp_Err : wait.channelContext.Err.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (sc : GoChan) (γs : ChanNames) (γi : BroadcastInternalNames) (Q : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait ∗
      isBroadcastChanInternal sc γs γi Q ⊢
    ctxOk (chanCtxVal sc) (chanCd γi) ∗ ctxErrClient (chanCtxVal sc) (chanCd γi) := by
  iintro ⟨#Pw, #Hint⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #He : ctxErrs (chanCtxVal sc) (chanCd γi) $$ []
  · unfold ctxErrs
    iintro !> %cl %Φ Hcl HΦ
    iapply (wp_Err sc γs γi Q cl) $$ [Hcl]
    · iframe Pw Hint
      rcases cl with _ | _ | _ <;> dsimp only
      · itrivial
      · iunfold context.ContextClosed at Hcl; iexact Hcl
      · itrivial
    inext
    iintro %err Hr
    icases Hr with (%Hn | ⟨#Hc, #Hd⟩)
    · obtain ⟨rfl, hcl⟩ := Hn
      iapply HΦ
      · rcases cl with _ | _ | _ <;> dsimp only
        · simp only [↓reduceIte]; itrivial
        · exact absurd rfl hcl
        · simp only [↓reduceIte]; itrivial
      · ipureintro; exact ⟨hAs, fun ii h => by cases h⟩
      · iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
      · iapply go_etcd_io.etcd.cache.v3.errCellOk_nil
      · ipureintro; left; rfl
    · ihave ⟨%Hne, #Hs, #Hcell⟩ := canceledOk_of_init hAs err $$ [Pctx Hc]
      · iframe Pctx Hc
      iapply HΦ
      · rcases cl with _ | _ | _ <;> dsimp only
        · rw [ite_cond_eq_false _ _ (eq_false Hne.1)]; iunfold context.ContextClosed; iexact Hd
        · ipureintro; exact Hne.1
        · rw [ite_cond_eq_false _ _ (eq_false Hne.1)]; iunfold context.ContextClosed; iexact Hd
      · ipureintro; exact Hne.2
      · iexact Hs
      · iexact Hcell
      · ipureintro; right; simp [handlerDescs]
  isplitr
  · iapply ctxOk_of_errs $$ He
  rw [ctxErrClient_eq_errs]; iexact He

end proofs

end EtcdGrove
end Perennial
