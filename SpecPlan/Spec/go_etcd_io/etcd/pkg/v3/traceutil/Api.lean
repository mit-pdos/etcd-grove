/-
# `pkg/v3/traceutil`: request traces (batch 4b): the vocabulary

A `*Trace` records a request's steps and fields and logs them if the request took long. Its
methods read and write its fields with no lock (`t.steps = append(t.steps, ...)`), so **a trace is
a resource, not a fact**: two goroutines may not use one trace at once. Every user keeps that
discipline: a request's trace is used by the goroutine serving the request (made by `EnsureTrace`,
found again in the context by `Get`/`EnsureTrace` further down the same call chain); the apply
thread's traces (`txn.Put` etc. at `context.TODO()`) are handed with the apply result to the request
goroutine (`raftRequest`, `Compact`), which steps and logs them; mvcc's transactions step the trace
they were begun with; the read loop's per-iteration trace stays in its goroutine.

(2c's and 3b's provisional `traceAt tr` was **persistent**, "its methods are safe to call": that is
false of the code (two `Step`s from two goroutines race on `t.steps`), so it is not offered; their
`traceAt` is this file's `traceOwn` (or `traceOpt` where the trace may be `nil`), threaded like 3e's
`Mvcc.traceOwn`.)

## Users (the pinned etcd)

* the server's request path (`etcdserver/v3_server.go`): `EnsureTrace` (`Range`, `Txn`, `Compact`,
  `RangeStream`), `Get` (`doSerialize`), `Step`, `AddField`, `LogIfLong`, and on the apply result's
  trace `GetStartTime`, `SetStartTime`, `InsertStep(0, ...)`, `LogIfLong`;
* `etcdserver/txn` (`Range`, `Put`, `DeleteRange`, `Txn`, `executeTxn`, `getPrevKV`): `EnsureTrace`,
  `Get`, `Step`, `StepWithFunction`, `AddField`, `StartSubTrace`, `StopSubTrace`;
* `etcdserver/apply/backend.go:69` (`Compaction`): `EnsureTrace(context.TODO(), ...)`;
* mvcc (`kvstore_txn.go`, `kv_view.go`, `kvstore.go`): `TODO()`, `Step`;
* the read-index loop (`etcdserver/read/read.go:109-144`): `EnsureTrace(context.Background(),
  ...)`, `Step`, `AddField`, `LogAllStepsIfLong`;
* the server's spans: `traceutil.Tracer.Start` (otel's tracer in the package variable).

Snippets: `examples/specreq/pkgleaves/trace.go` (`ReqRequestTrace`, `ReqApplyTraceHandoff`,
`ReqMvccTodoTrace`, `ReqReadLoopTrace`, `ReqSubTrace`, `ReqCtxTraceLent`).

## Vocabulary

* `traceOwn t` (exclusive, timeless): **the trace `t` is the caller's** (non-nil). Intended
  realization: the `Trace` struct at `t` but its `isEmpty` field, its fields slice and steps slice
  with their capacities, each step's fields slice (`fieldsOwn`), `lg` nil or a zap logger
  (`Zap.isLogger`), and `∃ e, traceEmpty t e` (`traceOwn_empty`).
* `traceEmpty t e` (persistent): **`t`'s `isEmpty` flag is `e`**, for good (written only at the
  trace's creation: `TODO()`'s are empty, `newTrace`'s not). Realization: the field's discarded
  points-to. `EnsureTrace` keeps a context's trace only if not empty, so this is what lets a caller
  learn that `EnsureTrace` returned the trace it already holds.
* `ctxTraceIs ctx o` (persistent): **what context `ctx` carries at `TraceKey{}`**: the non-nil
  trace `t` (`o = some t`), or none (`o = none`: nothing, another type, or a nil `*Trace`). Only the
  name: the trace's ownership is held separately. Realization: the triple of
  `ctx.Value(TraceKey{})` (persistent, from any goroutine).
* `fieldsOwn sl` (transparent): a slice of `Field`s, owned with its capacity (a trace keeps the
  variadic slices it is given, and its logger appends into a sub-trace's), each value `nil` or of a
  predeclared basic type (`fieldsFmt`: the logger formats them with `%v`; a basic value has no
  methods to call and is immutable, so formatting it later, from the logger, races with nothing).
* `traceOpt t` (transparent): `t` is `nil` or an owned trace (the apply layer's result traces).
* `tracerAt tr` (transparent, persistent): the package variable `Tracer` holds `tr` (otel's tracer,
  `Tracer.Start.spec`); `tracer_init` gives it from the package's initialization.

## Laws

`traceOwn_timeless`, `traceOwn_excl`, `traceOwn_ne_null`, `traceOwn_empty`, `traceEmpty_persistent`,
`traceEmpty_agree`, `ctxTraceIs_persistent`, `ctxTraceIs_agree`, and where a context's trace comes
from: `ctxTraceIs_background`, `ctxTraceIs_todo` (none), `ctxTraceIs_child` (a `WithCancel`/
`WithTimeout` child carries its parent's), `ctxTraceIs_value` (a `WithValue` at another key type
keeps it). `EnsureTrace`'s post gives the context it makes; `Tracer.Start`'s keeps it. A context
made elsewhere (grpc's per-call context) is introduced by its maker's spec (2a: none).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.pkg.v3.traceutil
public import SpecPlan.Spec.context.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import Perennial.Proof.fmt.Base

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section pure
variable [GooseExts] [GoGlobalContext]

/-- **The fields' values are formattable** (each `nil` or of a predeclared basic type: what the
trace's logger formats with `%v`). -/
def fieldsFmt (fs : List go_etcd_io.etcd.pkg.v3.traceutil.Field) : Prop :=
  ∀ ii : GoInterfaceOk, interface.ok ii ∈ fs.map (·.Value') → _root_.Perennial.fmt.IsBasicType ii.ty

/-- The key `TraceKey{}`, as an `any`. -/
def traceKey : GoInterface :=
  interface.mkOk go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty
    #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.TraceKey)

end pure

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The trace `t` is the caller's** (exclusive; see the header). -/
opaque traceOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) : IProp GF := iprop(True)

/-- **`t`'s `isEmpty` flag is `e`**, for good (persistent). -/
opaque traceEmpty [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (e : Bool) : IProp GF := iprop(True)

/-- **The context `ctx` carries the trace `o`** at `TraceKey{}` (persistent; see the header). -/
opaque ctxTraceIs [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (o : Option Loc) : IProp GF := iprop(True)

/-- **A slice of fields, owned with its capacity, its values formattable.** -/
def fieldsOwn (sl : GoSlice) : IProp GF :=
  iprop(∃ fs : List go_etcd_io.etcd.pkg.v3.traceutil.Field, sl ↦* fs ∗
    ownSliceCap go_etcd_io.etcd.pkg.v3.traceutil.Field sl (DFrac.own 1) ∗ ⌜fieldsFmt fs⌝)

/-- **`tr` is the tracer the package variable `Tracer` holds** (persistent: never written after the
package's initialization, in this scope: `tracer_init.spec`). -/
def tracerAt (tr : GoInterfaceOk) : IProp GF :=
  iprop(globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr)

/-- **`t` is `nil` or an owned trace.** -/
def traceOpt (t : Loc) : IProp GF :=
  if t = null then iprop(True) else traceOwn t

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def traceOwn_timeless.spec : Prop := ∀ t, Timeless (traceOwn (GF := GF) t)

def traceOwn_excl.spec : Prop := ∀ t, traceOwn (GF := GF) t ∗ traceOwn t ⊢ iprop(False)

def traceOwn_ne_null.spec : Prop := ∀ t, traceOwn (GF := GF) t ⊢ ⌜t ≠ null⌝

/-- **An owned trace has an emptiness flag** (every trace is made by `TODO` or `newTrace`, which
give it). What lets a caller holding only `traceOwn t` (2c's `ctxTrace`, a context's trace from
`Get`) lend it to a callee that begins with `EnsureTrace` (whose premise is `traceEmpty`). -/
def traceOwn_empty.spec : Prop := ∀ t, traceOwn (GF := GF) t ⊢ ∃ e, traceEmpty t e

def traceEmpty_persistent.spec : Prop := ∀ t e, Persistent (traceEmpty (GF := GF) t e)

def traceEmpty_agree.spec : Prop := ∀ t e e',
  traceEmpty (GF := GF) t e ∗ traceEmpty t e' ⊢ ⌜e = e'⌝

def ctxTraceIs_persistent.spec : Prop := ∀ ctx o, Persistent (ctxTraceIs (GF := GF) ctx o)

def ctxTraceIs_agree.spec : Prop := ∀ ctx o o',
  ctxTraceIs (GF := GF) ctx o ∗ ctxTraceIs ctx o' ⊢ ⌜o = o'⌝

/-- `Background()` carries no trace. -/
def ctxTraceIs_background.spec : Prop :=
  ⊢ ctxTraceIs (GF := GF) (GoInterface.ok context.backgroundCtxVal) none

/-- `TODO()` carries no trace. -/
def ctxTraceIs_todo.spec : Prop :=
  ⊢ ctxTraceIs (GF := GF) (GoInterface.ok context.todoCtxVal) none

/-- A child (`WithCancel`, `WithTimeout`) carries its parent's trace. -/
def ctxTraceIs_child.spec : Prop := ∀ ctx ctx' o,
  ctxTraceIs (GF := GF) ctx o ∗ Context.ctxChild ctx ctx' ⊢ ctxTraceIs ctx' o

/-- A `WithValue` at a key of another type keeps the parent's trace. -/
def ctxTraceIs_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk) o,
  ctxTraceIs (GF := GF) ctx o ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty⌝ ⊢ ctxTraceIs ctx' o

/-- **The package's tracer** (assumed of the package's initialization: `noop.NewTracerProvider().
Tracer(...)`, a non-nil interface value). **Scope**: `traceutil.Init`, which `embed` calls when
distributed tracing is configured (`--experimental-enable-distributed-tracing`), rewrites the
variable; a run that calls it is outside these specs (a decision of the user's, batch 4b's report). -/
def tracer_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ⊢ ∃ tr, tracerAt tr

end laws

end TraceUtil
end EtcdGrove
end Perennial
