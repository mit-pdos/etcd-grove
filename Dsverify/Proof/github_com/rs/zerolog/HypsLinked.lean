/-
`zerolog`'s hypotheses as its functions' proofs (the linking tier, CLAUDE.md "Import tiers"): each
`<F>.wp_proof` is the field of the hypothesis class (`Spec.lean`) that states `<F>.spec`. A proof
file takes the class as an instance argument and uses its fields; only linking modules see these.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial.github_com.rs.zerolog

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

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
