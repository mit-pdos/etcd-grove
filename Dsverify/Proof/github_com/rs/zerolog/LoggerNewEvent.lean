/-
`(*Logger).newEvent(level, nil)` on a logger made by `New(nil)`, for the five levels `Trace`..`Error`
(dsv-retire-3, 2026-11-26, mit-pdos/etcd-grove#49 step 3), what the level methods `Trace`, `Debug`,
`Info`, `Warn`, `Error` call (`Logger__*.lean`): `should` compares the level with the logger's
(`TraceLevel`: never below) and with `GlobalLevel()` (an atomic load of `gLevel`'s cell, through the
invariant of zerolog's fact); disabled, it returns `nil`; enabled, `newEvent(l.w, level)` takes an
`*Event` from `eventPool` (`isPool`, its elements `eventElem`), truncates its buffer and appends `{`
(`enc.AppendBeginMarker`), sets its fields, and `e.Str(LevelFieldName, LevelFieldMarshalFunc(level))`
appends the level (`marshalSpec`; `Str` through its statement, `Event.Str.spec`, which the linking
module passes). The logger has no context, no hooks, no stack and no sampler (`newLogger`), so the
other branches are not taken. A lemma over the translation (defs tier), not a function's `wp_proof`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.EventTok
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.rs.zerolog

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

/-- `(*Event).Str(k, x)`'s statement (`Event__Str.lean`), for the event token `ownEvent`: the
receiver back, with its token. -/
abbrev Event.Str.spec (ownEvent : Loc → IProp GF) : Prop :=
  ∀ (e : Loc) (k : GoString) (x : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ ownEvent e }}
      (App (App (Val (e @!! go.GoType.PointerType Event.ty @!! go!"Str")) (Val #k)) (Val #x))
    {{ RET #e; ownEvent e }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

attribute [-instance] go.SliceSemantics.composite_literal_slice

/-- `l.newEvent(lv, nil)` for `lv` one of the five levels, on a logger made by `New(nil)` (the file
header). -/
theorem wp_Logger_newEvent (wp_Str : Event.Str.spec (GF := GF) eventTok)
    (l : Loc) (lg : Logger) (dq : DFrac) (lv : w8) (hlv : lv ∈ fiveLevels) (nf : GoFunc) (hnf : nf = func.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ∗ l ↦{dq} lg ∗ loggerOk lg }}
      (App (App (Val (l @!! go.GoType.PointerType Logger.ty @!! go!"newEvent")) (Val #lv)) (Val #nf))
    {{ (e : Loc), RET #e; l ↦{dq} lg ∗ eventTok e }} := by
  subst hnf
  haveI : go.NotInterface go.int8 := ⟨by simp [go.int8]⟩
  wp_start as ⟨Hl, #Hok⟩
  ihave #Hi := zerologInit_access $$ Hpkg
  unfold loggerOk loggerMade
  icases Hok with ⟨%w, #HD, %Hlg⟩
  unfold zerologInit
  icases Hi with ⟨⟨%p, #HgL, #Ig⟩, #HLFN, ⟨%f, #HLF, #Hmarsh⟩, #Henc, ⟨%ep, %pf, #HEP, %Hpf, #Hpool⟩, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_call
  wp_auto
  -- `wp_auto` does not find a field's load through the logger's points-to `l ↦{dq} lg` (its
  -- `Access` search fails there, 2026-11-26); each field read takes the field out with its generated
  -- `AccessStrict` instance and puts it back.
  icases (Logger.Logger_access_load_level (GF := GF) l lg dq).access_strict $$ Hl with ⟨Hlv, Hclose⟩
  wp_load
  ihave Hl := Hclose $$ Hlv
  wp_auto
  have hnlt : ¬ sint.Z lv < sint.Z lg.level' := by
    subst Hlg
    simp only [fiveLevels, List.mem_cons, List.not_mem_nil, or_false] at hlv
    rcases hlv with rfl | rfl | rfl | rfl | rfl <;> simp [newLogger] <;> decide
  rw [decide_eq_false hnlt]
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt32 $$ [] [-]
  · iPkgInit
  iinv Ig with ⟨%gv, >Hgv⟩ Hcl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists gv
  iframe Hgv
  iintro Hgv
  imod Hmask
  imod Hcl $$ [Hgv] with -
  · inext; iexists _; iexact Hgv
  imodintro
  wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    iframe Hl
    unfold eventTok
    ileft
    ipureintro; rfl
  icases (Logger.Logger_access_load_sampler (GF := GF) l lg dq).access_strict $$ Hl with ⟨Hf, Hclose⟩
  wp_auto
  ihave Hl := Hclose $$ Hf
  have hs : lg.sampler' = GoInterface.nil := by subst Hlg; rfl
  rw [hs]
  wp_auto
  icases (Logger.Logger_access_load_w (GF := GF) l lg dq).access_strict $$ Hl with ⟨Hf, Hclose⟩
  wp_auto
  ihave Hl := Hclose $$ Hf
  wp_func_call
  wp_call
  wp_auto
  wp_apply (sync.Pool.wp_Get ep pf iprop(True) eventElem) $$ [] as %x ⟨Hx, -⟩
  · iframe Hpool
  icases Hx with (Hx | %Hnil)
  rotate_left
  · exact absurd Hnil.1 Hpf
  unfold eventElem
  icases Hx with ⟨%le, %v, %bs, %Hx, He, Hb, Hcap⟩
  subst Hx
  wp_auto
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  rw [ite_eq_left ⟨by word, by word, by word⟩]
  icases ownSlice_slice_with_cap (W64 0) (W64 0) v.buf' bs ⟨by word, by word, by word⟩ $$ [$Hb $Hcap]
    with ⟨-, Hb, Hcap⟩
  wp_auto
  repeat (first | wp_method_call | wp_call | wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  wp_apply wp_slice_append (V := w8) (t := go.byte) _ _ _ _ _ $$ [$Hb $Hcap $Hsl]
    as %d ⟨Hb, Hcap, -⟩
  try wp_auto
  simp only
  icases (Logger.Logger_access_load_hooks (GF := GF) l lg dq).access_strict $$ Hl with ⟨Hf, Hclose⟩
  wp_auto
  ihave Hl := Hclose $$ Hf
  simp only
  have hlv' : lv ∈ fiveLevels := hlv
  simp only [fiveLevels, List.mem_cons, List.not_mem_nil, or_false] at hlv'
  have h6 : decide (lv = W8 6) = false := by
    rcases hlv' with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [h6]
  wp_auto
  unfold marshalSpec
  wp_apply Hmarsh $$ []
  · ipureintro; exact hlv
  wp_apply (wp_Str le _ _) $$ [He Hb Hcap] as Htok
  · unfold eventTok
    iright
    iexists _, _, w
    iframe He Hb Hcap HD
    ipureintro
    subst Hlg
    exact ⟨by simp, rfl, rfl, rfl, rfl, hlv⟩
  icases (Logger.Logger_access_load_context (GF := GF) l lg dq).access_strict $$ Hl with ⟨Hf, Hclose⟩
  wp_auto
  ihave Hl := Hclose $$ Hf
  have hctx : decide (lg.context' = slice.nil) = true := by subst Hlg; simp [newLogger]
  rw [hctx]
  wp_auto
  icases (Logger.Logger_access_load_stack (GF := GF) l lg dq).access_strict $$ Hl with ⟨Hf, Hclose⟩
  wp_auto
  ihave Hl := Hclose $$ Hf
  have hst : lg.stack' = false := by subst Hlg; rfl
  rw [hst]
  wp_auto
  iapply HΦ
  iframe Hl Htok

end proof

end github_com.rs.zerolog
end Perennial
