/-
(The lab's `Proof/github_com/rs/zerolog/{Spec,Methods}.lean`, run `rabia-r1wake-1`.) zerolog's
specs Rabia's code uses, as **hypotheses** (notes/dsv-rabia.md, "The hypotheses"): zerolog v1.23.0
is translated names only in the part (the lab proved these over its model,
`harness/rpcmodel/zerolog`), so the specs are the fields of the class `Hyps` (a `Prop`), which every
theorem that calls them takes as an instance argument, up to the kit's closed statement; the lab's
names (`Logger.Warn.wp_proof`, `Event.Msg.wp_proof`, …) are theorems from it.

Each is what zerolog v1.23.0 does, up to what it writes (the kit's logger writes to `os.Stdout`
or nothing; output is not modelled): a `Logger`'s level method returns an event (`nil` when the level
is disabled), an event's field methods return their receiver, `Msg` returns, `ParseLevel("warn")`
is `WarnLevel` (2), `SetGlobalLevel` returns, `New(w)` returns some logger (the lab's model's
`Logger.mk w`; the real `Logger`'s fields differ).
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

/-- `(*Logger).M()` for `M` one of `Trace`, `Debug`, `Info`, `Warn`, `Error`: an event. -/
abbrev Logger.level.spec (m : GoString) : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
    (App (Val (l @!! go.GoType.PointerType Logger.ty @!! m)) (Val #()))
  {{ (e : Loc), RET #e; True }}

/-- `(*Event).Msg(msg)`. -/
abbrev Event.Msg.spec : Prop :=
  ∀ (e : Loc) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
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

/-- **The hypotheses** (the file header). -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] (GF : BundledGFunctors)
    [HeapGS HasLC.hasLC GF] [go.Semantics] [github_com.rs.zerolog.Assumptions] : Prop where
  level : ∀ m, m ∈ [go!"Trace", go!"Debug", go!"Info", go!"Warn", go!"Error"] →
    Logger.level.spec (GF := GF) m
  /-- `(*Event).Str(k, x)` returns its receiver. -/
  Event_Str : ∀ (e : Loc) (k : GoString) (x : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Str")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  /-- `(*Event).Int(k, x)` returns its receiver. -/
  Event_Int : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Int")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  /-- `(*Event).Ints(k, x)` returns its receiver. -/
  Event_Ints : ∀ (e : Loc) (k : GoString) (x : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Ints")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  /-- `(*Event).Int64(k, x)` returns its receiver. -/
  Event_Int64 : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Int64")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  /-- `(*Event).Uint32(k, x)` returns its receiver. -/
  Event_Uint32 : ∀ (e : Loc) (k : GoString) (x : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Uint32")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  /-- `(*Event).Bool(k, x)` returns its receiver. -/
  Event_Bool : ∀ (e : Loc) (k : GoString) (x : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Bool")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  /-- `(*Event).Float64(k, x)` returns its receiver. -/
  Event_Float64 : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Float64")) (Val #k)) (Val #x))
    {{ RET #e; True }}
  Event_Msg : Event.Msg.spec (GF := GF)
  ParseLevel_warn : ParseLevel.warn.spec (GF := GF)
  SetGlobalLevel : SetGlobalLevel.spec (GF := GF)
  New : New.spec (GF := GF)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

theorem Logger.Trace.wp_proof [h : Hyps GF] : Logger.level.spec (GF := GF) go!"Trace" :=
  h.level _ (by simp)

theorem Logger.Debug.wp_proof [h : Hyps GF] : Logger.level.spec (GF := GF) go!"Debug" :=
  h.level _ (by simp)

theorem Logger.Info.wp_proof [h : Hyps GF] : Logger.level.spec (GF := GF) go!"Info" :=
  h.level _ (by simp)

theorem Logger.Warn.wp_proof [h : Hyps GF] : Logger.level.spec (GF := GF) go!"Warn" :=
  h.level _ (by simp)

theorem Logger.Error.wp_proof [h : Hyps GF] : Logger.level.spec (GF := GF) go!"Error" :=
  h.level _ (by simp)

theorem Event.Str.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Str")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Str

theorem Event.Int.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Int")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Int

theorem Event.Ints.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : GoSlice),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Ints")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Ints

theorem Event.Int64.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Int64")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Int64

theorem Event.Uint32.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Uint32")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Uint32

theorem Event.Bool.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Bool")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Bool

theorem Event.Float64.wp_proof [h : Hyps GF] : ∀ (e : Loc) (k : GoString) (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Float64")) (Val #k)) (Val #x))
    {{ RET #e; True }} := h.Event_Float64

theorem Event.Msg.wp_proof [h : Hyps GF] : Event.Msg.spec (GF := GF) := h.Event_Msg
theorem ParseLevel.warn.wp_proof [h : Hyps GF] : ParseLevel.warn.spec (GF := GF) := h.ParseLevel_warn
theorem SetGlobalLevel.wp_proof [h : Hyps GF] : SetGlobalLevel.spec (GF := GF) := h.SetGlobalLevel
theorem New.wp_proof [h : Hyps GF] : New.spec (GF := GF) := h.New

end proof

end Perennial.github_com.rs.zerolog
