/-
**What a context answers at the libraries' own keys** (premise-fixes-7, part A, 2026-11-11; the
Scope's A.2, decisions D4 and D5). Lean-first.

Several trust-boundary specs read a context's `Value` at a key of a library's own unexported type:
grpc's `metadata` (`mdIncomingKey{}`, `mdOutgoingKey{}`), grpc's `peer` (`peerKey{}`), otel's
`trace` (`currentSpanKey`). `context.isContext` says nothing of `Value` at those keys (its `#HValue`
covers only `&cancelCtxKey`), so a context of the program's own whose `Value` panics, or answers a
value the library then misuses, refuted them (`examples/premisefix/ctxvalue`, `TestBadContextPanics`
and `TestContradictions`).

* `context.valueAt ctx k R` (persistent): `ctx.Value(k)` returns, from any goroutine, a value
  satisfying the pure `R` (the pattern of `context.startTimeOk`; pure, so that Perennial's
  `ctxValue` laws and `WithValue`'s `Value` wand carry it).
* The results the libraries accept (`metadata.incomingRes`, `metadata.outgoingRes`, `peer.peerRes`,
  `trace.spanRes`): a value of another type than the library stores (nothing to misuse: the
  library's type assertion fails), or one the library made (the opaque, trusted predicates
  `metadata.transportMD`, `metadata.builtRawMD`, `peer.transportPeer`, `trace.otelSpan`; D4: only
  the owning package can store a value under its unexported key).
* `context.libCtxOk ctx`: the four facts, what callers carry. The metadata facts are deterministic
  (`Value` returns one value `v` on every call): the metadata is a function of the context
  (`metadata.incomingOf`/`outgoingOf`).

Producers (proved): a context with Perennial's `ctxValue` at the keys (`libCtxOk_of_ctxValueNil`),
hence `Background()`, `TODO()` and their children by `WithCancel` and the deadline constructors
(`libCtxOk_background`, `libCtxOk_todo`, `libCtxOk_bgFrom`), a `WithValue` at another key type
(`libCtxOk_of_valueWand`), and contexts answering `nil` at every key (`libCtxOk_of_nil`: k8s's
`channelContext`). The k8s keys are in `Proof/k8s_io/apiserver/pkg/audit/CtxKeys.lean`.
-/
module

public import Perennial.Proof.context
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import GeneratedProof.google_golang_org.grpc.metadata
public import GeneratedProof.google_golang_org.grpc.peer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-! ### The opaque "made by the library" predicates (TRUSTED; D4) -/

/-- (opaque; TRUSTED) **An `MD` grpc's server transport put in a stream's context**: the value
`metadata.NewIncomingContext` stores under `mdIncomingKey{}` when grpc's HTTP/2 server transport
reads a stream's headers (grpc v1.84.0 `internal/transport/http2_server.go`, `operateHeaders`:
`mdata[hf.Name] = append(mdata[hf.Name], v)` for each header field, then
`metadata.NewIncomingContext(s.ctx, mdata)`): a `metadata.MD` with one key per header field name,
lower case (HTTP/2 header names are), each key with at least one value. Nothing writes it after:
only grpc's `metadata` package reads or stores under the unexported key. -/
opaque metadata.transportMD [GooseExts] : GoInterface → Prop

/-- (opaque; TRUSTED) **A `rawMD` grpc's `metadata` stored** under `mdOutgoingKey{}`:
`metadata.NewOutgoingContext(ctx, md)` (`rawMD{md: md}`) or `AppendToOutgoingContext(ctx, kv...)`
(`rawMD{md: md.md, added: added}`, the pairs appended, each key lower-cased) (grpc v1.84.0
`metadata/metadata.go`), never written after, and with no two keys of `md` equal up to case (every
`MD` this repository's code passes to `NewOutgoingContext` is built by `metadata.Pairs`/`New`, which
lower-case). -/
opaque metadata.builtRawMD [GooseExts] : GoInterface → Prop

/-- (opaque; TRUSTED) **A `*Peer` grpc's server transport made**: the value `peer.NewContext` stores
under `peerKey{}` for a server stream (grpc v1.84.0 `internal/transport/http2_server.go`,
`operateHeaders`: `peer.NewContext(s.ctx, t.peer)`, `t.peer` set in `NewServerTransport` from the
connection): not nil; its `Addr` is the connection's non-nil `net.Addr`, whose `String()` returns;
its `AuthInfo` is nil (insecure) or the server credentials' handshake information, a
`credentials.TLSInfo` holding the chains `crypto/tls` verified, which contain no nil certificate. -/
opaque peer.transportPeer [GooseExts] : GoInterface → Prop

/-- (opaque; TRUSTED) **A span otel made**: the value `trace.ContextWithSpan` stores under
`currentSpanKey` for a span returned by otel's SDK tracer (`sdk/trace` `tracer.Start`: a
`*recordingSpan` or a `nonRecordingSpan`), by its no-op tracer (`noopSpan`), or the
`nonRecordingSpan` of `trace.ContextWithRemoteSpanContext` (otel v1.47.0 `trace/context.go`,
`sdk/trace/tracer.go`, `trace/noop.go`): a `trace.Span` whose methods return (`End`, `AddEvent`,
`RecordError`, `SpanContext`, `IsRecording`, `TracerProvider`, ...: each of these types' methods
returns, `*recordingSpan`'s under its own mutex; k8s 7f-4 Revision 2 lists `IsRecording`, which the
no-op tracer's `Start` calls), and whose `TracerProvider()` is one of
otel's, whose `Tracer(...).Start` returns another such span. -/
opaque trace.otelSpan [GooseExts] : GoInterface → Prop

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`ctx.Value(k)` returns a value satisfying the pure `R`** (persistent; from any goroutine). -/
def context.valueAt (ctx : GoInterfaceOk) (k : GoInterface) (R : GoInterface → Prop) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ v : GoInterface, ⌜R v⌝ -∗ Φ #v) -∗
    WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #k)) {{ Φ }})

instance context.valueAt_persistent (ctx : GoInterfaceOk) (k : GoInterface)
    (R : GoInterface → Prop) : Persistent (context.valueAt (GF := GF) ctx k R) := by
  unfold context.valueAt; infer_instance

/-- grpc's `mdIncomingKey{}` as `ctx.Value` takes it (the empty struct, as `any`). -/
abbrev metadata.mdIncomingKeyAny : GoInterface :=
  interface.mkOk google_golang_org.grpc.metadata.mdIncomingKey.ty
    #(zero_val google_golang_org.grpc.metadata.mdIncomingKey)

/-- grpc's `mdOutgoingKey{}` as `ctx.Value` takes it. -/
abbrev metadata.mdOutgoingKeyAny : GoInterface :=
  interface.mkOk google_golang_org.grpc.metadata.mdOutgoingKey.ty
    #(zero_val google_golang_org.grpc.metadata.mdOutgoingKey)

/-- grpc's `peerKey{}` as `ctx.Value` takes it. -/
abbrev peer.peerKeyAny : GoInterface :=
  interface.mkOk google_golang_org.grpc.peer.peerKey.ty
    #(zero_val google_golang_org.grpc.peer.peerKey)

/-- What `FromIncomingContext` accepts at `mdIncomingKey{}`: not an `MD` (its `, ok` assertion
fails), or the transport's (`transportMD`). -/
def metadata.incomingRes (v : GoInterface) : Prop :=
  (∀ vi : GoInterfaceOk, v = GoInterface.ok vi → vi.ty ≠ google_golang_org.grpc.metadata.MD.ty) ∨
    metadata.transportMD v

/-- What `FromOutgoingContext` accepts at `mdOutgoingKey{}`: not a `rawMD`, or one grpc's
`metadata` stored (`builtRawMD`). -/
def metadata.outgoingRes (v : GoInterface) : Prop :=
  (∀ vi : GoInterfaceOk, v = GoInterface.ok vi → vi.ty ≠ google_golang_org.grpc.metadata.rawMD.ty) ∨
    metadata.builtRawMD v

/-- What `peer.FromContext`'s callers accept at `peerKey{}`: not a `*Peer`, or the transport's. -/
def peer.peerRes (v : GoInterface) : Prop :=
  (∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
      vi.ty ≠ go.GoType.PointerType google_golang_org.grpc.peer.Peer.ty) ∨
    peer.transportPeer v

/-- What `trace.SpanFromContext`'s callers accept at `currentSpanKey`: `nil` or otel's span. -/
def trace.spanRes (v : GoInterface) : Prop :=
  v = GoInterface.nil ∨ trace.otelSpan v

/-- **`ctx`'s incoming metadata is the transport's** (persistent): `Value(mdIncomingKey{})` returns
one value `v` on every call, which `FromIncomingContext` accepts. -/
def metadata.incomingCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ v : GoInterface, ⌜metadata.incomingRes v⌝ ∗
    context.valueAt ctx metadata.mdIncomingKeyAny (· = v))

/-- **`ctx`'s outgoing metadata is grpc's** (persistent): `Value(mdOutgoingKey{})` returns one
value `v` on every call, which `FromOutgoingContext` accepts. -/
def metadata.outgoingCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ v : GoInterface, ⌜metadata.outgoingRes v⌝ ∗
    context.valueAt ctx metadata.mdOutgoingKeyAny (· = v))

/-- **`ctx`'s peer is the transport's** (persistent). -/
def peer.peerCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  context.valueAt ctx peer.peerKeyAny peer.peerRes

/-- **`ctx`'s span is otel's** (persistent). -/
def trace.spanValOk (ctx : GoInterfaceOk) : IProp GF :=
  context.valueAt ctx trace.spanKeyVal trace.spanRes

/-- **A context value, possibly nil, whose span is otel's** (persistent): what
`trace.SpanContextFromContext(ctx)` needs (`SpanFromContext` returns the no-op span for a nil
`ctx`, without calling `Value`: `examples/premisefix/k8sctx`). -/
def trace.spanValOkNil (ctx : GoInterface) : IProp GF :=
  iprop(⌜ctx = GoInterface.nil⌝ ∨ ∃ ci : GoInterfaceOk, ⌜ctx = GoInterface.ok ci⌝ ∗ trace.spanValOk ci)

/-- **A context's library values are well formed** (persistent): what callers carry. -/
def context.libCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(metadata.incomingCtxOk ctx ∗ metadata.outgoingCtxOk ctx ∗ peer.peerCtxOk ctx ∗
    trace.spanValOk ctx)

instance metadata.incomingCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (metadata.incomingCtxOk (GF := GF) ctx) := by
  unfold metadata.incomingCtxOk; infer_instance
instance metadata.outgoingCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (metadata.outgoingCtxOk (GF := GF) ctx) := by
  unfold metadata.outgoingCtxOk; infer_instance
instance peer.peerCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (peer.peerCtxOk (GF := GF) ctx) := by
  unfold peer.peerCtxOk; infer_instance
instance trace.spanValOk_persistent (ctx : GoInterfaceOk) :
    Persistent (trace.spanValOk (GF := GF) ctx) := by
  unfold trace.spanValOk; infer_instance
instance trace.spanValOkNil_persistent (ctx : GoInterface) :
    Persistent (trace.spanValOkNil (GF := GF) ctx) := by
  unfold trace.spanValOkNil; infer_instance
instance context.libCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (context.libCtxOk (GF := GF) ctx) := by
  unfold context.libCtxOk; infer_instance

/-- The four keys, for the laws' side conditions. -/
abbrev context.libKeys : List GoInterface :=
  [metadata.mdIncomingKeyAny, metadata.mdOutgoingKeyAny, peer.peerKeyAny, trace.spanKeyVal]

end defs

/-- The side condition of `context.libCtxOk_of_valueWand` at a key of the named types `tys`
(their `.ty` definitions): none of the libraries' key types. -/
syntax "context_libKeys_ne" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| context_libKeys_ne [$tys,*]) => `(tactic| (
      intro k hk k' h
      simp only [context.libKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        simp only [metadata.mdIncomingKeyAny, metadata.mdOutgoingKeyAny, peer.peerKeyAny,
          trace.spanKeyVal, interface.mkOk, GoInterface.ok.injEq] at h <;> subst h <;>
        simp [google_golang_org.grpc.metadata.mdIncomingKey.ty,
          google_golang_org.grpc.metadata.mdOutgoingKey.ty, google_golang_org.grpc.peer.peerKey.ty,
          go_opentelemetry_io.otel.trace.traceContextKeyType.ty, $tys,*]))

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem context.valueAt_mono (ctx : GoInterfaceOk) (k : GoInterface) (R R' : GoInterface → Prop)
    (h : ∀ v, R v → R' v) :
    context.valueAt (GF := GF) ctx k R ⊢ context.valueAt ctx k R' := by
  iintro #H
  unfold context.valueAt
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iintro %v %hv
  iapply HΦ
  ipureintro; exact h v hv

/-- A context answering `nil` at a key answers what each library accepts. -/
theorem context.libCtxOk_of_nil (ctx : GoInterfaceOk) :
    (□ ∀ k : GoInterface, ⌜k ∈ context.libKeys⌝ -∗
      context.valueAt (GF := GF) ctx k (· = GoInterface.nil)) ⊢ context.libCtxOk ctx := by
  iintro #H
  unfold context.libCtxOk metadata.incomingCtxOk metadata.outgoingCtxOk peer.peerCtxOk
    trace.spanValOk
  isplitl []
  · iexists GoInterface.nil
    isplitl []
    · ipureintro; left; intro vi h; cases h
    iapply H; ipureintro; simp
  isplitl []
  · iexists GoInterface.nil
    isplitl []
    · ipureintro; left; intro vi h; cases h
    iapply H; ipureintro; simp
  isplitl []
  · iapply context.valueAt_mono _ _ (· = GoInterface.nil)
    · intro v hv; subst hv; left; intro vi h; cases h
    iapply H; ipureintro; simp
  · iapply context.valueAt_mono _ _ (· = GoInterface.nil)
    · intro v hv; left; exact hv
    iapply H; ipureintro; simp

variable [package_sem : _root_.Perennial.context.Assumptions]

/-- A context with Perennial's `ctxValue` at a key answers as it says. -/
theorem context.valueAt_of_ctxValue (ctx : GoInterfaceOk) (k : GoInterface)
    (R : GoInterface → Prop) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ _root_.Perennial.context.ctxValue ctx k R ⊢
      context.valueAt ctx k R := by
  iintro ⟨#Hpkg, #Hv⟩
  unfold context.valueAt
  imodintro
  iintro %Φ HΦ
  iapply _root_.Perennial.context.ctxValue_Value ctx k R $$ [] [HΦ]
  · iframe #
  inext
  iintro %v %hv
  iapply HΦ; ipureintro; exact hv

theorem context.libKeys_notIntPtr (k : GoInterface) (hk : k ∈ context.libKeys) :
    _root_.Perennial.context.notIntPtrKey k := by
  intro ki h
  simp only [context.libKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [GoInterface.ok.injEq] at h <;> subst h
  · unfold google_golang_org.grpc.metadata.mdIncomingKey.ty; simp
  · unfold google_golang_org.grpc.metadata.mdOutgoingKey.ty; simp
  · unfold google_golang_org.grpc.peer.peerKey.ty; simp
  · unfold go_opentelemetry_io.otel.trace.traceContextKeyType.ty; simp

/-- **A context answering `nil` at every key Perennial's model knows** (`ctxValue ... (· = nil)`
at each library key) has `libCtxOk`. -/
theorem context.libCtxOk_of_ctxValueNil (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      (□ ∀ k : GoInterface, ⌜_root_.Perennial.context.notIntPtrKey k⌝ -∗
        _root_.Perennial.context.ctxValue ctx k (· = GoInterface.nil)) ⊢
      context.libCtxOk ctx := by
  iintro ⟨#Hpkg, #H⟩
  iapply context.libCtxOk_of_nil
  imodintro
  iintro %k %hk
  iapply context.valueAt_of_ctxValue
  iframe #
  iapply H
  ipureintro; exact context.libKeys_notIntPtr k hk

theorem context.libCtxOk_background :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      context.libCtxOk _root_.Perennial.context.backgroundCtxVal := by
  iintro #Hpkg
  iapply context.libCtxOk_of_ctxValueNil
  iframe #
  imodintro
  iintro %k -
  iapply _root_.Perennial.context.ctxValue_background

theorem context.libCtxOk_todo :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      context.libCtxOk _root_.Perennial.context.todoCtxVal := by
  iintro #Hpkg
  iapply context.libCtxOk_of_ctxValueNil
  iframe #
  imodintro
  iintro %k -
  iapply _root_.Perennial.context.ctxValue_todo

/-- A child of `Background()` (`WithCancel`, the deadline constructors). -/
theorem context.libCtxOk_bgFrom (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxValueFrom _root_.Perennial.context.backgroundCtxVal ctx ⊢
      context.libCtxOk ctx := by
  iintro ⟨#Hpkg, #Hf⟩
  iapply context.libCtxOk_of_ctxValueNil
  iframe #
  imodintro
  iintro %k %hk
  unfold _root_.Perennial.context.ctxValueFrom
  iapply Hf
  · ipureintro; exact hk
  iapply _root_.Perennial.context.ctxValue_background

theorem context.outgoingCtxOk_of_libCtxOk (ctx : GoInterfaceOk) :
    context.libCtxOk (GF := GF) ctx ⊢ metadata.outgoingCtxOk ctx := by
  iintro #H
  unfold context.libCtxOk
  icases H with ⟨-, #H, -⟩
  iexact H

/-- A child of `Background()` has grpc's outgoing metadata (none). -/
theorem context.outgoingCtxOk_bgFrom (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      _root_.Perennial.context.ctxValueFrom _root_.Perennial.context.backgroundCtxVal ctx ⊢
      metadata.outgoingCtxOk ctx := by
  iintro ⟨#Hpkg, #Hf⟩
  iapply context.outgoingCtxOk_of_libCtxOk
  iapply context.libCtxOk_bgFrom
  iframe #

/-- **A key `c'` delegates to `parent`** (`WithValue(parent, key, v)`'s `Value` wand, at a key of
another type than `key`) keeps `valueAt`. -/
theorem context.valueAt_of_valueWand (parent c' key : GoInterfaceOk) (v k : GoInterface)
    (R : GoInterface → Prop) (hk : ∀ k' : GoInterfaceOk, k = GoInterface.ok k' → k'.ty ≠ key.ty) :
    (□ (∀ (k : GoInterface) (R : GoInterface → Prop),
          ⌜k = GoInterface.ok key ∨ ∀ k' : GoInterfaceOk, k = GoInterface.ok k' → k'.ty ≠ key.ty⌝ -∗
          ⌜k = GoInterface.ok key → R v⌝ -∗
          (⌜k ≠ GoInterface.ok key⌝ -∗
            {{ True }} (App (Val #(methods parent.ty go!"Value" parent.v)) (Val #k))
            {{ (w : GoInterface), RET #w; ⌜R w⌝ }}) -∗
          {{ True }} (App (Val #(methods c'.ty go!"Value" c'.v)) (Val #k))
          {{ (w : GoInterface), RET #w; ⌜R w⌝ }})) -∗
      context.valueAt (GF := GF) parent k R -∗ context.valueAt c' k R := by
  iintro #Hw #Hp
  have hne : k ≠ GoInterface.ok key := by
    intro h; exact hk key h rfl
  unfold context.valueAt
  imodintro
  iintro %Φ HΦ
  iapply Hw $$ %k %R [] [] [] [] [HΦ]
  · ipureintro; right; exact hk
  · ipureintro; intro h; exact absurd h hne
  · iintro - !> %Ψ - HΨ
    iapply Hp
    iexact HΨ
  · itrivial
  · inext; iexact HΦ

/-- **`WithValue` at a key of none of the libraries' types keeps `libCtxOk`.** Its side condition
`hk` at a named key type `T` (`⟨T.ty, _⟩`): `by context_libKeys_ne [T.ty]`. -/
theorem context.libCtxOk_of_valueWand (parent c' key : GoInterfaceOk) (v : GoInterface)
    (hk : ∀ k ∈ context.libKeys, ∀ k' : GoInterfaceOk, k = GoInterface.ok k' → k'.ty ≠ key.ty) :
    (□ (∀ (k : GoInterface) (R : GoInterface → Prop),
          ⌜k = GoInterface.ok key ∨ ∀ k' : GoInterfaceOk, k = GoInterface.ok k' → k'.ty ≠ key.ty⌝ -∗
          ⌜k = GoInterface.ok key → R v⌝ -∗
          (⌜k ≠ GoInterface.ok key⌝ -∗
            {{ True }} (App (Val #(methods parent.ty go!"Value" parent.v)) (Val #k))
            {{ (w : GoInterface), RET #w; ⌜R w⌝ }}) -∗
          {{ True }} (App (Val #(methods c'.ty go!"Value" c'.v)) (Val #k))
          {{ (w : GoInterface), RET #w; ⌜R w⌝ }})) -∗
      context.libCtxOk (GF := GF) parent -∗ context.libCtxOk c' := by
  iintro #Hw #Hp
  unfold context.libCtxOk metadata.incomingCtxOk metadata.outgoingCtxOk peer.peerCtxOk
    trace.spanValOk
  icases Hp with ⟨⟨%vi, %hvi, #Hi⟩, ⟨%vo, %hvo, #Ho⟩, #Hpe, #Hsp⟩
  isplitl []
  · iexists vi; iframe %hvi
    iapply context.valueAt_of_valueWand parent c' key v _ _ (hk _ (by simp)) $$ Hw Hi
  isplitl []
  · iexists vo; iframe %hvo
    iapply context.valueAt_of_valueWand parent c' key v _ _ (hk _ (by simp)) $$ Hw Ho
  isplitl []
  · iapply context.valueAt_of_valueWand parent c' key v _ _ (hk _ (by simp)) $$ Hw Hpe
  · iapply context.valueAt_of_valueWand parent c' key v _ _ (hk _ (by simp)) $$ Hw Hsp

end laws

end EtcdGrove
end Perennial
