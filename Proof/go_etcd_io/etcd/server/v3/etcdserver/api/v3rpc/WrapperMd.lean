/-
**The incoming metadata of etcd's stream wrapper** (k8s 7f-4, B1's revision of T-b, decided by
etcd-grove-81 2026-11-12: per-constructor preservation on the stream path). Lean-first.

When a client requires a leader, `newStreamInterceptor` (fork `673da07c8f`
`server/etcdserver/api/v3rpc/interceptor.go:244`) hands the handler a `serverStreamWithCtx` whose
`Context()` is `newCancellableContext(ss.Context())`: a `*cancellableContext` `l` whose embedded
`Context` field holds `c1 = WithCancel(ci)`, a `*cancelCtx` whose `Context` field holds grpc's run
context `ci`. The handler's specification is grpc's, at `incomingOf ci`; the handler reads the
wrapper's metadata (`AuthInfoFromCtx(stream.Context())`). What preserves it:

* `v3rpc.incomingOf_cancellableContext` (here, trusted; restated by incomingof Part A, approved by
  the user 2026-11-17 via etcd-grove-03): the wrapper over a `*cancelCtx` over `ci` has `ci`'s
  metadata, given `metadata.incomingKept ci` (`Proof/google_golang_org/grpc/metadata/Incoming.lean`:
  `ci`'s `*cancelCtx` children have its metadata, a conjunct of grpc's `srvRawStreamIs`, per run);
* `v3rpc.wp_WithCancel_cancelCtx` (proved, from Perennial's linked specs): Perennial's
  `wp_WithCancel_any` with the child's location and its `Context` field's persistent points-to,
  which `wp_WithCancel_any` hides.

The axiom concludes a pure fact from persistent points-tos of fields of one Go type each (never from
a `Value` WP, which a looping `Value` satisfies at every answer: the refuted T-b), guarded by
`incomingKept ci`, which only grpc's uninterpreted delivery gives (so the bare points-tos, which a
proof can build at any address in a fresh heap, conclude nothing: the old unguarded form fell to
`crossWorld`, `notes/axiom-review/incomingof.md`).
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

/-- (TRUSTED; k8s 7f-4, B1's revision of T-b; restated by incomingof Part A, approved by the user
2026-11-17 via etcd-grove-03) **etcd's stream wrapper over `WithCancel(ci)` has `ci`'s incoming
metadata**: the `*cancellableContext` `l` whose `Context` field holds the `*cancelCtx` `c`
(`v3rpc.ccField l ↦□ c`) whose `Context` field holds grpc's run context `ci` (`ctxField c ↦□ ci`),
given that `ci`'s `*cancelCtx` children have its metadata (`metadata.incomingKept ci`), has `ci`'s.
`type cancellableContext struct { context.Context; lock sync.RWMutex; cancel context.CancelFunc;
cancelReason error }` (fork `673da07c8f` `server/etcdserver/api/v3rpc/interceptor.go:270-276`)
overrides only `Err` (`:297`) and adds `Cancel` (`:288`); `Value` is promoted, `(*l).Context.Value(key)`,
and the field is written only by `newCancellableContext`'s composite literal (`:280-283`).
`metadata.FromIncomingContext(x)` (grpc v1.84.0 `metadata/metadata.go:268-282`) is a function of
`x.Value(mdIncomingKey{})`, so it answers on `l` as on `c`, and on `c` as on `ci` (Go test
`examples/axiomcx/incomingof` `TestWrapperInheritsIncoming`).

Why guarded (`notes/axiom-review/incomingof.md`): the unguarded form (`ccField l ↦□ c ⊢
incomingOf (ccCtx l) = incomingOf c`) had an antecedent a proof can build in a fresh heap at any
address and content (`crossWorld`), so it made `incomingOf` constant on `*cancellableContext` values,
which Go refutes (`TestIncomingNotConstant`'s shape). `incomingKept ci` is given only by grpc's
uninterpreted `acceptRun` (`srvRawStreamIs`); no proof builds it. The links are structural (one
cell each, two persistent points-tos of a cell agree), so a context whose `Value` loops is related to
nothing, and two run contexts of one run are not related to each other. -/
axiom v3rpc.incomingOf_cancellableContext (l c : Loc) (ci : GoInterfaceOk) :
    (metadata.incomingKept ci ∗ _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) ∗
      v3rpc.ccField l ↦□ (GoInterface.ok (interface.mk
        (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) : IProp GF) ⊢
    (iprop(⌜metadata.incomingOf (GoInterface.ok (v3rpc.ccCtx l)) =
      metadata.incomingOf (GoInterface.ok ci)⌝) : IProp GF)

end defs

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
linked specs with them in the post (for `v3rpc.incomingOf_cancellableContext`). -/
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
