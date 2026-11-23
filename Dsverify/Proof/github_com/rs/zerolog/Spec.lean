/-
(The lab's `Proof/github_com/rs/zerolog/{Spec,Methods}.lean`, run `rabia-r1wake-1`.) zerolog's
specs Rabia's code uses, as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): zerolog v1.23.0
is translated names only in the part (the lab proved these over its model,
`harness/rpcmodel/zerolog`), so the specs are the fields of the class `Hyps` (a `Prop`), which every
theorem that calls them takes as an instance argument, up to the kit's closed statement; a proof
file uses the class's fields (`HypsLinked.lean` restates them as `wp_proof`s, linking tier).

Each is what zerolog v1.23.0 does, up to what it writes (the kit's logger writes to `os.Stdout`
or nothing; output is not modelled):
- a `Logger`'s level method (`Trace`, `Debug`, `Info`, `Warn`, `Error`: the five levels whose
  `Msg` neither panics nor exits; `Panic()`/`Fatal()` are not covered) on a non-`nil` `*Logger`
  (`(*Logger)(nil).Warn()` dereferences `nil` and panics) returns an event (`nil` when the level is
  disabled) with its token `ownEvent e`;
- an event's field methods (`Str`, `Int`, ...) take the token and return their receiver with it:
  an event is not safe for concurrent use (its methods append to its buffer), so the token is
  exclusive and one goroutine at a time holds it;
- `Msg` takes the token and returns (it writes the event and puts it back into zerolog's pool, so
  the token is gone);
- `ParseLevel("warn")` is `WarnLevel` (2), `SetGlobalLevel` returns, `New(w)` returns some logger
  (the lab's model's `Logger.mk w`; the real `Logger`'s fields differ).

`ownEvent` is abstract: the class says some predicate makes all the event specs true
(`∃ ownEvent, EventSpecs ownEvent`); real zerolog's is "`e` is `nil`, or a pooled `*Event` of one of
the five levels that the holder alone uses". The proofs name it `ownEvent` (chosen, with its specs
`eventSpecs`).
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.rs.zerolog

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

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
    (App (Val (@! New)) (Val #w))
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

section token
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- The event token `Hyps.events` says exists (chosen: a proof names it as a constant). -/
noncomputable def ownEvent [h : Hyps GF] : Loc → IProp GF := Classical.choose h.events

theorem eventSpecs [h : Hyps GF] : EventSpecs GF (ownEvent (GF := GF)) :=
  Classical.choose_spec h.events

end token

end Perennial.github_com.rs.zerolog
