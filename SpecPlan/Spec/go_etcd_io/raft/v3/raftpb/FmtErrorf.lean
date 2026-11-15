/-
# `fmt.Errorf` with raftpb arguments: the trust boundary (verify round, 2026-11-09)

**Assumed.** Perennial's `fmt.Errorf.spec` (`Perennial/Spec/fmt/Errorf.lean`) admits only arguments of
predeclared basic types, or named integer types with no formatting method (`fmt.ArgsWf`): Go's
`fmt` calls an argument's `Format`/`GoString`/`Error`/`String` method, which Perennial's model of
`Errorf` (`errors.New(format)`, ignoring the arguments) does not. Two raftpb-side call sites pass
other arguments:

* `confchange.go:167`, `Changer.apply`'s "unexpected conf type %d" with `cc.GetType()`, a
  `raftpb.ConfChangeType` (whose method set has `String`);
* `confstate.go:49`, `ConfState.Equivalent`'s mismatch error, `%+#v` of four `*ConfState`s.

This spec admits, besides Perennial's arguments, **a raftpb enum value** (`ConfChangeType`,
`MessageType`, `EntryType`, `ConfChangeTransition`) and **a `*ConfState` the caller holds**
(`confStatePts`, any fraction, given back). It is true of Go's `fmt` at the pinned toolchain for
every format string (the verbs are not constrained):

* an enum: no `Format`/`GoString`/`Error` method; under `%v %s %q %x %X` Go calls `String()`
  (protoc-gen-go's `protoimpl.X.EnumStringOf(x.Descriptor(), n)`: the name from the file
  descriptor raftpb's initialization built, or the number; reads only, never panics); under `%d`
  it prints the integer by reflection and calls nothing (`fmt/print.go`, `handleMethods`);
* a `*ConfState`: no `Format`/`GoString`/`Error` method. Under `%v %s` Go calls `String()`
  (`protoimpl.X.MessageStringOf`: prototext marshaling, which reads the message); under `%#v`
  (`%+#v`) and the other verbs it prints the struct by reflection (`printValue` follows the
  top-level pointer only; nested pointers are printed as addresses), reading its fields. Either
  way it only reads what `confStatePts` holds (the `sizeCache` and `state` cells protobuf writes
  atomically are read non-atomically by reflection: a concurrent `Marshal` of the same message by
  another holder would be a benign race; assumed). A `fmt` panic inside a method would be
  recovered by `fmt` and printed; none of these methods panics.

The result is Perennial's: a non-nil error whose `Error()` returns some string (the model is
`errors.New(format)`); the arguments' slice and resources come back (the model never reads them).

**Users.** `Changer.apply.spec` (`confchange/Changer__apply.lean`), `ConfState.Equivalent.spec`
(`ConfState__Equivalent.lean`). Kept local to raftpb (the old tree's `Spec/fmt/Errorf.lean`,
`argsOk`/`stringMethodSpec`, was the general form; `SpecPlan/Spec/fmt/` is another group's on this branch):
the general fix is a Perennial change widening `ArgsWf` to named integer types whose `String` `%d`
does not call, and to read-only pointer arguments.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Api
public import Perennial.Proof.fmt.Base

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

/-- raftpb's enumeration types (protoc-gen-go enums: `String()` is the descriptor's name). -/
def pbEnumTys [GooseExts] [GoGlobalContext] : List go.GoType :=
  [raftpb.ConfChangeType.ty, raftpb.MessageType.ty, raftpb.EntryType.ty,
   raftpb.ConfChangeTransition.ty]

/-- **One argument of a raftpb `fmt.Errorf` call**: Perennial's (`nil`, or `fmt.ArgWf`), a raftpb
enum value, or a `*ConfState` held at `dq`. -/
inductive FmtArg [GooseExts] where
  | basic (v : GoInterface)
  | enum (t : go.GoType) (x : w32)
  | confState (p : Loc) (dq : DFrac) (cs : ConfState)

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The interface value the argument is passed as. -/
def FmtArg.val : FmtArg → GoInterface
  | .basic v => v
  | .enum t x => interface.mkOk t #x
  | .confState p _ _ => interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p

/-- What the caller holds of the argument (given back). -/
def FmtArg.own : FmtArg → IProp GF
  | .basic v => iprop(⌜v = GoInterface.nil ∨ ∃ ii, v = interface.ok ii ∧ _root_.Perennial.fmt.ArgWf ii⌝)
  | .enum t _ => iprop(⌜t ∈ pbEnumTys⌝)
  | .confState p dq cs => confStatePts p dq cs

end res

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]
variable [fmt_sem : _root_.Perennial.fmt.Assumptions]

/-- **Assumed.** `fmt.Errorf(format, args...)` with raftpb arguments (see the header): a non-nil
error whose `Error()` returns some string; the slice and the arguments' resources given back. -/
def fmtErrorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List FmtArg) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      args_sl ↦*{dq} (args.map FmtArg.val) ∗ [∗list] a ∈ args, FmtArg.own (GF := GF) a }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(interface.ok err);
      args_sl ↦*{dq} (args.map FmtArg.val) ∗ ([∗list] a ∈ args, FmtArg.own (GF := GF) a) ∗
      □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
        WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }}

end spec

end RaftPb
end EtcdGrove
end Perennial
