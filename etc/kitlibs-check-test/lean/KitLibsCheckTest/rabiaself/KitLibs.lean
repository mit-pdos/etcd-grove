/-
kitlibs-check's validation on rabia, **self-contained** (notes/dsv-kitlibs-check.md): rabia's landed premises
as a challenge's agent would write them, the library `Spec.lean` files not being shipped (they are
the reference solution): their definitions copied here (namespaces `zl`, `pb`, `rnd`, `sig`, each
opening the library's), the class's fields the same ten premises. kitlibs-check must accept it with
the fixed-module rule on (`etc/kitlibs-check-test/rabiaself.conf`'s `fixed=`: every module of the
statement's closure but those four `Spec.lean` and the validation's own). One edit beyond copying:
zerolog's `New` is written `github_com.rs.zerolog.New`; copied as `New`, it resolved to the rabia kit's
own `rabianet.New`, and kitlibs-check refused the field (a triple about the system's function).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.TopLevelDefs
public import Dsverify.Proof.github_com.rs.zerolog.Init
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Init
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Init
public import Dsverify.Proof.github_com.go_redis.redis.v8.Init
public import Dsverify.Proof.os.signal.Init
public import Dsverify.Code.rabia.internal.message
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Base
public import Dsverify.Proof.github_com.rs.zerolog.Base
public import Dsverify.Proof.os.signal.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Proof.math.rand.Base

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace rabia.examples.rabianet

namespace zl
open github_com.rs.zerolog

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- `(*Logger).M()` for `M` one of `Trace`, `Debug`, `Info`, `Warn`, `Error`, on a non-`nil`
logger: an event, with its token. -/
abbrev Logger.level.spec (ownEvent : Loc → IProp GF) (m : GoString) : Prop :=
  ∀ (l : Loc), l ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
    (App (Val (l @!! go.GoType.PointerType Logger.ty @!! m)) (Val #()))
  {{ (e : Loc), RET #e; ownEvent e }}

/-- `(*Event).Msg(msg)`: returns; the token is gone. -/
abbrev Event.Msg.spec (ownEvent : Loc → IProp GF) : Prop :=
  ∀ (e : Loc) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
    (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Msg")) (Val #msg))
  {{ RET #(); True }}

/-- `ParseLevel("warn")`. -/
abbrev ParseLevel.warn.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
    (App (Val (@! ParseLevel)) (Val #(go!"warn")))
  {{ RET (PairV #(W8 2) #interface.nil); True }}

/-- `SetGlobalLevel(l)`. -/
abbrev SetGlobalLevel.spec : Prop :=
  ∀ (lv : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
    (App (Val (@! SetGlobalLevel)) (Val #lv))
  {{ RET #(); True }}

/-- `New(w)`: some logger. -/
abbrev New.spec : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
    (App (Val (@! github_com.rs.zerolog.New)) (Val #w))
  {{ (lg : Logger), RET #lg; True }}

end spec

/-- The event specs, for the event token `ownEvent` (the file header). -/
structure EventSpecs [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] [github_com.rs.zerolog.Assumptions]
    (ownEvent : Loc → IProp GF) : Prop where
  level : ∀ m, m ∈ [go!"Trace", go!"Debug", go!"Info", go!"Warn", go!"Error"] →
    Logger.level.spec (GF := GF) ownEvent m
  /-- `(*Event).Str(k, x)` returns its receiver, the token kept. -/
  Event_Str : ∀ (e : Loc) (k : GoString) (x : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Str")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  /-- `(*Event).Int(k, x)` returns its receiver, the token kept. -/
  Event_Int : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Int")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  /-- `(*Event).Ints(k, x)` returns its receiver, the token kept. -/
  Event_Ints : ∀ (e : Loc) (k : GoString) (x : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Ints")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  /-- `(*Event).Int64(k, x)` returns its receiver, the token kept. -/
  Event_Int64 : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Int64")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  /-- `(*Event).Uint32(k, x)` returns its receiver, the token kept. -/
  Event_Uint32 : ∀ (e : Loc) (k : GoString) (x : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Uint32")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  /-- `(*Event).Bool(k, x)` returns its receiver, the token kept. -/
  Event_Bool : ∀ (e : Loc) (k : GoString) (x : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Bool")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  /-- `(*Event).Float64(k, x)` returns its receiver, the token kept. -/
  Event_Float64 : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Float64")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}
  Event_Msg : Event.Msg.spec (GF := GF) ownEvent

/-- **The hypotheses** (the file header). -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] (GF : BundledGFunctors)
    [HeapGS HasLC.hasLC GF] [go.Semantics] [github_com.rs.zerolog.Assumptions] : Prop where
  events : ∃ ownEvent : Loc → IProp GF, EventSpecs GF ownEvent
  ParseLevel_warn : ParseLevel.warn.spec (GF := GF)
  SetGlobalLevel : SetGlobalLevel.spec (GF := GF)
  New : New.spec (GF := GF)

end zl

namespace pb
open github_com.gogo.protobuf.proto

/-- **The hypotheses** (the file header). -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  /-- `proto.RegisterEnum("message.MsgType", MsgType_name, MsgType_value)` (`message.pb.go`'s
  first `init`): inside `message`'s initialization, once (the header). -/
  RegisterEnum : ∀ (σ : GMap GoString Bool) (nameMap valueMap : Loc),
    {{ (ownGoState σ : IProp GF) ∗
        globalAddr rabia.internal.message.MsgType_value ↦ valueMap }}
      (App (App (App (Val #(functions RegisterEnum [])) (Val #(go!"message.MsgType")))
        (Val #nameMap)) (Val #valueMap))
    {{ RET #(); ownGoState σ }}
  /-- `proto.RegisterType(x, name)` (`message.pb.go`'s first `init`). -/
  RegisterType : ∀ (σ : GMap GoString Bool) (x : GoInterface) (name : GoString),
    {{ (ownGoState σ : IProp GF) }}
      (App (App (Val #(functions RegisterType [])) (Val #x)) (Val #name))
    {{ RET #(); ownGoState σ }}
  /-- `proto.RegisterFile(filename, descriptor)` (`message.pb.go`'s second `init`). -/
  RegisterFile : ∀ (σ : GMap GoString Bool) (filename : GoString) (descriptor : GoSlice),
    {{ (ownGoState σ : IProp GF) }}
      (App (App (Val #(functions RegisterFile [])) (Val #filename)) (Val #descriptor))
    {{ RET #(); ownGoState σ }}

end pb

namespace rnd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `NewSource(seed)`: a fresh `Source`, with its token. -/
abbrev math.rand.NewSource.spec (isSource : GoInterface → IProp GF) : Prop :=
  ∀ (seed : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
      (App (Val (@! math.rand.NewSource)) (Val #seed))
    {{ (src : GoInterface), RET #src; isSource src }}

/-- `New(src)` of a source from `NewSource`: a fresh `*Rand`, with its token. -/
abbrev math.rand.New.spec (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF) : Prop :=
  ∀ (src : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand ∗ isSource src }}
      (App (Val (@! math.rand.New)) (Val #src))
    {{ (r : Loc), RET #r; ownRand r }}

/-- `r.Intn(n)` for `n > 0`, `r` from `New` (its token): some `x` in `[0, n)`; the token kept. -/
abbrev math.rand.Rand.Intn.spec (ownRand : Loc → IProp GF) : Prop :=
  ∀ (r : Loc) (n : w64), 0 < sint.Z n →
    {{ ownRand r }}
      (App (Val (r @!! go.GoType.PointerType math.rand.Rand.ty @!! go!"Intn")) (Val #n))
    {{ (x : w64), RET #x; ownRand r ∗ ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

/-- The specs of a `Rand` and its source, for the tokens `isSource` and `ownRand` (the header). -/
structure math.rand.RandSpecs [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF) : Prop where
  NewSource : math.rand.NewSource.spec (GF := GF) isSource
  New : math.rand.New.spec (GF := GF) isSource ownRand
  Rand_Intn : math.rand.Rand.Intn.spec (GF := GF) ownRand

/-- **The hypotheses** (the header). -/
class math.rand.Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  rands : ∃ (isSource : GoInterface → IProp GF) (ownRand : Loc → IProp GF),
    math.rand.RandSpecs GF isSource ownRand

end rnd

namespace sig
open os.signal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The signals `internal/system.SigListen` registers, as the `os.Signal` values of its slice
literal: `syscall.SIGINT` (2) and `syscall.SIGTERM` (15). -/
def quietSigs : List os.Signal :=
  [interface.mkOk syscall.Signal.ty #(W64 2), interface.mkOk syscall.Signal.ty #(W64 15)]

/-- `Notify(c, sigs...)` on a non-`nil` channel, for a non-empty list `sigs`, in a deployment where
none of `sigs` is sent: nothing (the environment assumption `NoSignals sigs`, the header). -/
abbrev NotifyQuiet.spec (sigs : List os.Signal) : Prop :=
  sigs ≠ [] → ∀ (c : GoChan) (sig : GoSlice) (dq : DFrac), c ≠ chan.nil →
    {{ isPkgInit (PROP := IProp GF) pkg_id.os.signal ∗ sig ↦*{dq} sigs }}
      (App (App (Val (@! os.signal.Notify)) (Val #c)) (Val #sig))
    {{ RET #(); sig ↦*{dq} sigs }}

end spec

/-- **The environment assumption** (the header): none of the signals `sigs` is sent to the
deployment's processes, so `Notify` registers a channel for exactly those (a non-empty list) that
never receives one. An assumption about how the kit is run, not a property of `os/signal`'s code. -/
class NoSignals [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (sigs : List os.Signal) (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  notifyQuiet : NotifyQuiet.spec (GF := GF) sigs

end sig

/-- rabia's landed premises, self-contained (the file header). -/
class KitLibs [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [github_com.rs.zerolog.Assumptions] : Prop where
  zerolog_init : github_com.rs.zerolog.InitHyp GF
  proto_init : github_com.gogo.protobuf.proto.InitHyp GF
  proto : pb.Hyps GF
  gogoproto_init : github_com.gogo.protobuf.gogoproto.InitHyp GF
  redis_init : github_com.go_redis.redis.v8.InitHyp GF
  signal_init : os.signal.InitHyp GF
  zerolog : zl.Hyps GF
  rand : rnd.math.rand.Hyps GF
  no_signals : sig.NoSignals sig.quietSigs GF

end rabia.examples.rabianet
end Perennial
