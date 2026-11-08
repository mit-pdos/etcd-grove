/-
**The request context's etcd keys** (sweep repairs 1, B2, 2026-11-08; `notes/axiom-review/valuestarttime.md`):
what a context answers at `traceutil.StartTimeKey{}`, the key `EtcdServer.raftRequest` reads the
request's start time under. Until B2 an axiom (`context.ValueStartTime`) claimed it of every
`isContext`, which is false: `context.WithValue(ctx, StartTimeKey{}, 42)` is an `isContext`, and a
user `Context` may panic in `Value`.

* `startTimeOk ctx` (persistent): `ctx.Value(StartTimeKey{})` returns `nil` or a `time.Time`.
  Its producers: a gRPC run's context (`startTimeOk_of_grpcRunCtx`: `Value` of an etcd-named key is
  `nil`), a context with Perennial's `ctxValue` at the key (`startTimeOk_of_ctxValue`), hence a
  child of `Background()` by `WithCancel` or the deadline constructors (`startTimeOk_of_bgFrom`),
  and `WithValue`'s `Value` wand (the server's `Put`/`Txn`, `authStore.WithRoot`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- The key `traceutil.StartTimeKey{}` as `ctx.Value` takes it (the empty struct, as `any`). -/
abbrev startTimeKeyAny : GoInterface :=
  interface.mkOk go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty
    #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey)

/-- What `raftRequest` accepts of `Value(StartTimeKey{})`: `nil` or a `time.Time`. -/
def startTimeRes (v : GoInterface) : Prop :=
  v = GoInterface.nil ∨ ∃ t : time.Time, v = interface.mkOk _root_.Perennial.time.Time.ty #t

/-- **`ctx`'s start time is a time** (persistent; see the file header). -/
def context.startTimeOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ v : GoInterface, ⌜startTimeRes v⌝ -∗ Φ #v) -∗
    WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #startTimeKeyAny)) {{ Φ }})

instance context.startTimeOk_persistent (ctx : GoInterfaceOk) :
    Persistent (context.startTimeOk (GF := GF) ctx) := by
  unfold context.startTimeOk; infer_instance

theorem startTimeKeyAny_notIntPtr : context.notIntPtrKey startTimeKeyAny := by
  intro ki h
  simp only [interface.mkOk, GoInterface.ok.injEq] at h
  subst h
  unfold go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty
  simp

/-- A gRPC run's context answers `nil` (an etcd-named key). -/
theorem startTimeOk_of_grpcRunCtx (ci : GoInterfaceOk) :
    grpcRunCtx (GF := GF) ci ⊢ context.startTimeOk ci := by
  iintro #Hg
  unfold context.startTimeOk
  imodintro
  iintro %Φ HΦ
  iunfold grpcRunCtx at Hg
  icases Hg with ⟨#Hg, -⟩
  have hk : startTimeKeyAny = interface.mkOk
      (go.GoType.Named go!"go.etcd.io/etcd/pkg/v3/traceutil.StartTimeKey" [])
      #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey) := by
    unfold startTimeKeyAny go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty; rfl
  rw [hk]
  iapply Hg
  · ipureintro; unfold etcdPkgPrefix; decide
  inext
  iapply HΦ
  ipureintro; left; rfl

/-- A context with Perennial's `ctxValue` at the key answers as it says. -/
theorem startTimeOk_of_ctxValue (ctx : GoInterfaceOk) (R : GoInterface → Prop)
    (hR : ∀ v, R v → startTimeRes v) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.ctxValue ctx startTimeKeyAny R ⊢
      context.startTimeOk ctx := by
  iintro ⟨#Hpkg, #Hv⟩
  unfold context.startTimeOk
  imodintro
  iintro %Φ HΦ
  iapply context.ctxValue_Value ctx startTimeKeyAny R $$ [] [HΦ]
  · iframe #
  inext
  iintro %v %hv
  iapply HΦ; ipureintro; exact hR v hv

/-- A child of `Background()` (`ctxValueFrom backgroundCtxVal`: `WithCancel`, the deadline
constructors) answers `nil`. -/
theorem startTimeOk_of_bgFrom (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      context.ctxValueFrom context.backgroundCtxVal ctx ⊢ context.startTimeOk ctx := by
  iintro ⟨#Hpkg, #Hf⟩
  ihave #Hb := context.ctxValue_background (GF := GF) startTimeKeyAny
  unfold context.ctxValueFrom
  iapply startTimeOk_of_ctxValue ctx (· = GoInterface.nil) (fun v h => Or.inl h)
  iframe #
  iapply Hf
  · ipureintro; exact startTimeKeyAny_notIntPtr
  iexact Hb

end defs

end EtcdGrove
end Perennial
