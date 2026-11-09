/-
# zap, the ambient logger (batch W0): a trust boundary

`go.uber.org/zap` is translated names-only: every spec in this directory is **assumed**, true of
zap's code (`logger.go`, `field.go`, `zapcore/entry.go` at the pinned module) and its documented
behaviour: logging has no effect a Go program can observe through etcd's code (it writes to the
logger's sinks), `Panic` panics with the message, `Fatal` exits the process, and loggers are safe
for concurrent use.

## Vocabulary

* `isLogger l` (persistent): `l` is a `*zap.Logger` as one of zap's constructors returns it
  (`zap.New`, `NewNop`, `NewProduction`, `NewDevelopment`, `Config.Build`, and the derivations
  `Named`, `With`, `WithOptions` with zap's own options), never written afterwards: non-nil, its
  core one of zap's (`nopCore`, `ioCore` over a non-nil encoder, syncer and level, and zap's
  wrappers of those; not a user's core or `Hooks`), its clock, error output and stack level
  non-nil, its terminal hooks the defaults. A zero `zap.Logger{}` is not one: each of its logging
  methods dereferences a nil core and panics. Every spec that logs takes it; it is carried from
  the logger's creator (an example's `zap.NewNop()`, the server's configuration, the client's
  `Config.Logger`) by the specs that store a logger (the server's and the client's handles).
  Intended realization: an opaque persistent fact about the struct (`l ↦□ v` with `v`'s fields as
  above); it stays a boundary fact (zap is not verified here).
* `zapcore.entryOk ce` (exclusive): `ce` is a `*zapcore.CheckedEntry` that `Logger.Check` returned
  non-nil, at a level below `DPanicLevel`, not yet written. `CheckedEntry.Write` consumes it (a
  second `Write` of one entry reports the reuse to its error output; an entry at `DPanicLevel`
  under `Development()` or at `PanicLevel` panics in `Write`).

## Laws

`isLogger_persistent`, `isLogger_ne_null`.

## The specs

`NewNop`; `Logger.{Debug,Info,Warn,Error}` (return, no effect), `Logger.Panic` (panics with the
message), `Logger.Fatal` (never returns), `Logger.Check` (below `DPanicLevel`: `nil` or an entry);
`zapcore.CheckedEntry.Write`; the field constructors `String`, `Strings`, `ByteString`, `Bool`,
`Int`, `Int32`, `Int64`, `Uint`, `Uint32`, `Uint64`, `Duration`, `Stringer`, `Stack`, `Error`,
`NamedError`, `Any` (each returns some field; a field is a plain value the logger only formats).
A field constructor is total: `Stringer`, `Any`, `Error` keep their argument, which the logger
formats later (a `Stringer` whose `String` panics is recovered by zap's encoder into the
field's error key: `zapcore/field.go`, `encodeStringer`).
-/
module

public import GeneratedProof.go_uber_org.zap
public import Spec.PkgInit.go_uber_org.zap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Zap

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`l` is a zap logger** (persistent; see the header). -/
opaque isLogger [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) : IProp GF := iprop(True)

/-- **An entry `Check` returned, to write once** (exclusive). -/
opaque entryOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ce : Loc) : IProp GF := iprop(True)

def isLogger_persistent.spec : Prop := ∀ l, Persistent (isLogger (GF := GF) l)

def isLogger_ne_null.spec : Prop := ∀ l, isLogger (GF := GF) l ⊢ ⌜l ≠ null⌝

end res

end Zap
end EtcdGrove
end Perennial
