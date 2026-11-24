/-
`(*Options).String` (`db.go`), over Perennial's `fmt.Sprintf` (the real `Sprintf`, real `fmt` stage 1,
2026-11-24) and `time.Duration.String` (ps2 misc2, 2026-11-22; until then a trust-boundary axiom).
The options are not nil (`optsAt`); `String` reads the 15 fields and formats them: `Timeout` under
`%s` (a `time.Duration`, whose `String()` Perennial proves), the `bool`s under `%v`, `FreelistType`
converted to a string under `%s`, the `int`s under `%x`/`%d`, and whether `OpenFile` and `Logger`
are set under `%v` (the fork's 7d335aa3e: `%p` of their addresses until then).
-/
module

public import Spec.go_etcd_io.bbolt.Options__String
public import Proof.go_etcd_io.bbolt.Options
public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.time.Duration__String
public import Proof.fmt.SprintfPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section args
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open _root_.Perennial.fmt in
/-- A `time.Duration` is an argument `fmt` formats by its `String()`. -/
private theorem isArg_duration (hDur : _root_.Perennial.time.Duration.String.spec (GF := GF) (hG := hG))
    (x : time.Duration) :
    ⊢ isArg (GF := GF) (interface.mkOk time.Duration.ty #x) (.method fun _ => True) := by
  have h1 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Format")
  have h2 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Error")
  have h3 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"String")
  have h4 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"CanInterface")
  simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3 h4
  iapply (EtcdGrove.fmt.isArg_stringer ⟨time.Duration.ty, #x⟩ (by simpa using h1)
    (by simpa using h2) (by simpa [noArgStringSig] using h3) (by simpa using h4))
  unfold stringMethodSpec
  imodintro
  iintro %Φ HΦ
  wp_apply hDur x as %s -
  iapply HΦ

end args

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxRecDepth 20000 in
theorem Options.String.wp_proof (hSprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (hDur : _root_.Perennial.time.Duration.String.spec (GF := GF) (hG := hG)) :
    Options.String.spec (GF := GF) (hG := hG) := by
  intro l dq o
  wp_start as ⟨Ho, %Hlg⟩
  unfold optsAt
  icases Ho with ⟨%v, Hv, %Hv⟩
  icases (optsPt_eq l v dq).1 $$ Hv with
    ⟨⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, -⟩, %Hnn⟩
  wp_auto
  simp only [decide_eq_false Hnn]
  wp_auto
  -- `o.Logger != nil`: by the logger's case
  rcases hLg : v.Logger' with _ | li
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoInterface)
    try (isplitr; (ipureintro; rfl))
    iintro %al ⟨Hal, -⟩
    (try wp_auto)
    ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    -- the duration by its `String()`; the `bool`s, the free-list type (a string), the `int`s, and
    -- whether `OpenFile`/`Logger` are set, calling no method
    wp_apply hSprintf go!"{Timeout: %s, NoGrowSync: %v, NoFreelistSync: %v, PreLoadFreelist: %v, FreelistType: %s, ReadOnly: %v, MmapFlags: %x, InitialMmapSize: %d, PageSize: %d, MaxSize: %d, NoSync: %v, OpenFile: %v, Mlock: %v, Logger: %v, NoStatistics: %v}"
      [.lit go!"{Timeout: ", .dir none _root_.Perennial.fmt.verb_s, .lit go!", NoGrowSync: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", NoFreelistSync: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", PreLoadFreelist: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", FreelistType: ", .dir none _root_.Perennial.fmt.verb_s, .lit go!", ReadOnly: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", MmapFlags: ", .dir none _root_.Perennial.fmt.verb_x, .lit go!", InitialMmapSize: ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", PageSize: ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", MaxSize: ", .dir none _root_.Perennial.fmt.verb_d, .lit go!", NoSync: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", OpenFile: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", Mlock: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", Logger: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!", NoStatistics: ", .dir none _root_.Perennial.fmt.verb_v, .lit go!"}"] _ _
      [.method fun _ => True, .bool _, .bool _, .bool _, .str _, .bool _, .int _, .int _, .int _, .int _,
        .bool _, .bool _, .bool _, .bool _, .bool _] (DFrac.own 1) (by fmt_encode) (by fmt_fits)
      $$ [$Hfmt $Hal] as %str ⟨-, -⟩
    · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1)) = 4 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1)) = 5 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1)) = 6 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 7 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 8 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 9 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 10 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 11 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 12 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 13 from rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 14 from rfl,
        List.set_cons_succ, List.set_cons_zero]
      iapply BigSepL2.bigSepL2_cons.2
      isplitr
      · iapply isArg_duration hDur
      iapply (EtcdGrove.fmt.PureArgs.isArgs ?pa)
      case pa => fmt_pure
    try wp_auto
    iapply HΦ
    iexists v
    isplitl
    · iapply (optsPt_eq l v dq).2
      rw [hLg]
      iframe
      ipureintro; exact Hnn
    · ipureintro; exact Hv)

end proof

end bbolt
end EtcdGrove
end Perennial
