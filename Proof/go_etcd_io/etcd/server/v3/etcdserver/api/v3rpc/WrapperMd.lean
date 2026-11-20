/-
**etcd's stream wrapper: its names and `WithCancel` with the child's location** (k8s 7f-4, B1's
revision of T-b; perheap 1b, 2026-11-18). Lean-first.

When a client requires a leader, `newStreamInterceptor` (fork `673da07c8f`
`server/etcdserver/api/v3rpc/interceptor.go:244`) hands the handler a `serverStreamWithCtx` whose
`Context()` is `newCancellableContext(ss.Context())`: a `*cancellableContext` `l` whose embedded
`Context` field holds `c1 = WithCancel(ci)`, a `*cancelCtx` whose `Context` field holds grpc's run
context `ci`. Its incoming metadata is `ci`'s by two proved laws over Perennial's chain:
`metadata.ctxInMD_cancel` (`Proof/context/LibKeysChain.lean`) and `v3rpc.ctxInMD_cc`
(`SrvCtxWeakLaws.lean`), composed in `v3rpc.ctxInMD_wrapper`. Until perheap 1b two axioms said it,
over the pure `metadata.incomingOf` (`incomingOf_cancelCtx`, `v3rpc.incomingOf_cancellableContext`),
refuted: `notes/axiom-review/incomingof.md`. Here: the wrapper's names and
`v3rpc.wp_WithCancel_cancelCtx` (proved, from Perennial's linked specs: Perennial's
`wp_WithCancel_any` with the child's location and its `Context` field's persistent points-to).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.context.LibKeysChain
public import Perennial.Proof.context.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic

section names
variable [GooseExts] [GoGlobalContext]

/-- The `Context` field of etcd's `*cancellableContext` `l` (its embedded context, set by
`newCancellableContext`'s composite literal and never written after). -/
abbrev v3rpc.ccField [GoSemanticsFunctions] (l : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext go!"Context" l

/-- The `*cancellableContext` `l` as a `context.Context`. -/
abbrev v3rpc.ccCtx (l : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.cancellableContext.ty) #l

end names

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

variable [package_sem : _root_.Perennial.context.Assumptions]

open _root_.Perennial.context in
/-- **`WithCancel(parent)` for any context `parent`, with the child's location**: Perennial's
`context.wp_WithCancel_any`, whose proof (`wp_WithCancel_any_of`) builds the child as the
`*cancelCtx` `c` with `ctxField c ↦□ parent` and then hides both; restated here from the same
linked specs with them in the post (for `v3rpc.ctxInMD_wrapper`). -/
theorem v3rpc.wp_WithCancel_cancelCtx (parent : GoInterfaceOk) (s : ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ isContext parent s }}
      (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #(interface.ok parent)))
    {{ (c : Loc) (γ' : ContextNames) (cancel : GoFunc),
        RET (PairV #(interface.mkOk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)
          #cancel);
        cancelSpec cancel γ' iprop(True) ∗
        isContext (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)
          { s with PDone := iprop(True), Done_gn := γ' } ∗
        ctxValueFrom parent
          (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c) ∗
        ctxField c ↦□ (interface.ok parent : GoInterface) ∗ isCancelCtxOf c γ' iprop(True) }} := by
  have childCancelSpec_cancelCtx := childCancelSpec_cancelCtx_of (GF := GF) cancelCtx.wp_cancel
  have isContext_cancelCtx := isContext_cancelCtx_of (GF := GF) cancelCtx.wp_Done cancelCtx.wp_Err
      cancelCtx.wp_Value sync.atomic.Value.wp_Load
  have wp_WithCancel_gen := wp_WithCancel_gen_of (GF := GF) wp_withCancel cancelCtx.wp_cancel
  have wp_propagateCancel_any := wp_propagateCancel_any_of (GF := GF) cancelCtx.wp_propagateCancel
  iintro %Φ ⟨#Hpkg, #Hctx⟩ HΦ
  ihave #Hctx2 := Hctx
  iunfold isContext at Hctx2
  iunfold isContextDef at Hctx2
  icases Hctx2 with ⟨-, -, -, -, -, -, -, #Hcci⟩
  iapply wp_WithCancel_gen parent iprop(True) iprop(isContext parent s)
      (fun c γ => by
        iintro %Φ ⟨#Hpkg, #Hc, Hf, #Hctx⟩ HΦ
        ihave #Htt : □ (iprop(True) -∗ iprop(True)) $$ []
        · imodintro; iintro -; itrivial
        ihave #Hk := childCancelSpec_cancelCtx c γ iprop(True) iprop(True) $$ [$Hpkg $Hc $Htt]
        iapply wp_propagateCancel_any c parent s _ $$ [$Hpkg $Hf $Hctx $Hk] HΦ)
  · iframe #
    unfold isParentCtx; iright; iexists s; iframe #
  inext
  iintro %c %γ %cancel ⟨#Hcancel, #Hc, #Hf⟩
  ihave #Hdl := deadlineSpec_isContext _ _ $$ Hctx
  iapply HΦ $$ %c
  isplitl []
  · iexact Hcancel
  isplitl []
  · iapply isContext_cancelCtx c γ _ parent _ rfl rfl
    iframe #
  isplitl []
  · iapply ctxValueFrom_cancel c parent; iexact Hf
  isplitl []
  · iexact Hf
  · iexact Hc

end proofs

end EtcdGrove
end Perennial
