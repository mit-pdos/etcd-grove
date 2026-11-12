/-
**The incoming metadata of etcd's stream wrapper** (k8s 7f-4, B1's revision of T-b, decided by
etcd-grove-81 2026-11-12: per-constructor preservation on the stream path). Lean-first.

When a client requires a leader, `newStreamInterceptor` (fork `673da07c8f`
`server/etcdserver/api/v3rpc/interceptor.go:244`) hands the handler a `serverStreamWithCtx` whose
`Context()` is `newCancellableContext(ss.Context())`: a `*cancellableContext` `l` whose embedded
`Context` field holds `c1 = WithCancel(ci)`, a `*cancelCtx` whose `Context` field holds grpc's run
context `ci`. The handler's specification is grpc's, at `incomingOf ci`; the handler reads the
wrapper's metadata (`AuthInfoFromCtx(stream.Context())`). The two links preserve it:

* `metadata.incomingOf_cancelCtx` (`Proof/google_golang_org/grpc/metadata/Incoming.lean`,
  trusted): a `*cancelCtx` has its parent's;
* `v3rpc.incomingOf_cancellableContext` (here, trusted): a `*cancellableContext` has its `Context`
  field's;
* `v3rpc.incomingOf_wrapper` (proved): the composition;
* `v3rpc.wp_WithCancel_cancelCtx` (proved, from Perennial's linked specs): Perennial's
  `wp_WithCancel_any` with the child's location and its `Context` field's persistent points-to,
  which `wp_WithCancel_any` hides.

Both axioms conclude a pure fact from persistent points-tos of a field of one Go type, never from a
`Value` WP; a context whose `Value` loops provides no such points-to and is related to nothing but
the wrappers built over it (`Incoming.lean`, `incomingOf_cancelCtx`'s docstring;
`v3rpc.incomingOf_cancellableContext_field_unique` here). The refuted form (T-b,
`metadata.incomingOf_of_value`, from two `valueAt`s) is gone.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.google_golang_org.grpc.metadata.Incoming
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

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- (TRUSTED; k8s 7f-4, B1's revision of T-b) **etcd's `*cancellableContext` carries its embedded
context's incoming metadata**: `l` whose `Context` field holds `c` (`v3rpc.ccField l ↦□ c`) has
`c`'s incoming metadata. `type cancellableContext struct { context.Context; lock sync.RWMutex;
cancel context.CancelFunc; cancelReason error }` (fork `673da07c8f`
`server/etcdserver/api/v3rpc/interceptor.go:270-276`) overrides only `Err` (`:297`) and adds
`Cancel` (`:288`); `Value` is promoted, `(*l).Context.Value(key)`, and the field is written only by
`newCancellableContext`'s composite literal (`:280-283`). `metadata.FromIncomingContext(x)` (grpc
v1.84.0 `metadata/metadata.go:268-282`) is a function of `x.Value(mdIncomingKey{})`, so it answers on
`l` as on `c`. Like `metadata.incomingOf_cancelCtx`, it concludes from a points-to of one type's
field, not from a `Value` WP: each `*cancellableContext` is related to its one embedded context
(`v3rpc.incomingOf_cancellableContext_field_unique`), so a context whose `Value` loops equates
nothing but the wrappers built over it. -/
axiom v3rpc.incomingOf_cancellableContext (l : Loc) (c : GoInterfaceOk) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ⊢ (iprop(⌜metadata.incomingOf
      (GoInterface.ok (v3rpc.ccCtx l)) = metadata.incomingOf (GoInterface.ok c)⌝) : IProp GF)

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`v3rpc.incomingOf_cancellableContext` relates a wrapper to one embedded context only.** -/
theorem v3rpc.incomingOf_cancellableContext_field_unique (l : Loc) (c1 c2 : GoInterfaceOk) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c1) ∗ v3rpc.ccField l ↦□ (GoInterface.ok c2) : IProp GF) ⊢
      (iprop(⌜c1 = c2⌝) : IProp GF) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  ipureintro
  injection h

/-- **etcd's stream wrapper over `WithCancel(ci)` has `ci`'s incoming metadata**: the
`*cancellableContext` `l` whose field holds the `*cancelCtx` `c` whose field holds `ci`. -/
theorem v3rpc.incomingOf_wrapper (l c : Loc) (ci : GoInterfaceOk) :
    (v3rpc.ccField l ↦□
        (GoInterface.ok (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) ∗
      _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) : IProp GF) ⊢
      (iprop(⌜metadata.incomingOf (GoInterface.ok (v3rpc.ccCtx l)) =
        metadata.incomingOf (GoInterface.ok ci)⌝) : IProp GF) := by
  iintro ⟨#Hl, #Hc⟩
  ihave %h1 := v3rpc.incomingOf_cancellableContext l _ $$ Hl
  ihave %h2 := incomingOf_cancelCtx c ci $$ Hc
  ipureintro
  rw [h1, h2]

variable [package_sem : _root_.Perennial.context.Assumptions]

open _root_.Perennial.context in
/-- **`WithCancel(parent)` for any context `parent`, with the child's location**: Perennial's
`context.wp_WithCancel_any`, whose proof (`wp_WithCancel_any_of`) builds the child as the
`*cancelCtx` `c` with `ctxField c ↦□ parent` and then hides both; restated here from the same
linked specs with them in the post (for `v3rpc.incomingOf_wrapper`). -/
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
        ctxField c ↦□ (interface.ok parent : GoInterface) }} := by
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
  · iexact Hf

end proofs

end EtcdGrove
end Perennial
