/-
`(*Options).String` (`db.go`), over Perennial's `fmt.Sprintf` and `time.Duration.String` (ps2 misc2,
2026-11-22; until then a trust-boundary axiom, when no `fmt.Sprintf` spec covered `%p`). The options
are not nil (`optsAt`); `String` reads the 15 fields and formats them: `Timeout` under `%s` (a
`time.Duration`, whose `String()` Perennial proves), the `bool`s under `%t`, `FreelistType` (a
string type without methods) under `%s`, the `int`s under `%x`/`%d`, `OpenFile` (a func) and
`Logger` (nil or of a pointer type: `loggerPtrOk`) under `%p`.
-/
module

public import Spec.go_etcd_io.bbolt.Options__String
public import Proof.go_etcd_io.bbolt.Options
public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.time.Duration__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

/-- `String`'s format. -/
private abbrev optsFmt : GoString :=
  go!"{Timeout: %s, NoGrowSync: %t, NoFreelistSync: %t, PreLoadFreelist: %t, FreelistType: %s, ReadOnly: %t, MmapFlags: %x, InitialMmapSize: %d, PageSize: %d, MaxSize: %d, NoSync: %t, OpenFile: %p, Mlock: %t, Logger: %p, NoStatistics: %t}"

set_option maxRecDepth 20000 in
private theorem fmtDirectives_optsFmt :
    _root_.Perennial.fmt.fmtDirectives optsFmt =
      some [⟨W8 115, false⟩, ⟨W8 116, false⟩, ⟨W8 116, false⟩, ⟨W8 116, false⟩, ⟨W8 115, false⟩,
        ⟨W8 116, false⟩, ⟨W8 120, false⟩, ⟨W8 100, false⟩, ⟨W8 100, false⟩, ⟨W8 100, false⟩,
        ⟨W8 116, false⟩, ⟨W8 112, false⟩, ⟨W8 116, false⟩, ⟨W8 112, false⟩, ⟨W8 116, false⟩] := by
  decide

section args
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open _root_.Perennial.fmt in
private theorem argOkAt_of_argWf' (mv : List w8) (d : Directive) (ii : GoInterfaceOk) (h : ArgWf ii) :
    ⊢ argOkAt (GF := GF) mv d (.ok ii) := by
  unfold argOkAt; ileft; ipureintro; exact h

open _root_.Perennial.fmt in
private theorem argWf_bool (b : Bool) : ArgWf (interface.mk go.bool #b) := by
  apply EtcdGrove.fmt.argWf_of_argsWf
  refine ArgsWf.cons_other go.bool #b _ ?_ ?_ ?_ .nil
  · simp [go.bool, go.string]
  · have hb : ¬ IsIntType go.bool := by
      simp [IsIntType, go.bool, go.int, go.int64, go.int32, go.int16,
        go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
    rintro (hi | ⟨hi, -⟩)
    · exact hb hi
    · rw [go.is_underlying] at hi; exact hb hi
  · exact Or.inr (Or.inl rfl)

open _root_.Perennial.fmt in
private theorem argWf_int (n : w64) : ArgWf (interface.mk go.int #n) :=
  EtcdGrove.fmt.argWf_of_argsWf (ArgsWf.cons_int _ _ _ (.int n) .nil)

open _root_.Perennial.fmt in
private theorem argWf_freelist (x : GoString) : ArgWf (interface.mk FreelistType.ty #x) := by
  apply EtcdGrove.fmt.argWf_of_argsWf
  have hs : FreelistType.ty ≠ go.string := by simp [FreelistType.ty, go.string]
  have hi : ¬ IsIntType FreelistType.ty := by
    simp [IsIntType, FreelistType.ty, go.int, go.int64, go.int32, go.int16, go.int8, go.uint,
      go.uint64, go.uint32, go.uint16, go.uint8]
  exact ArgsWf.cons_named_string _ _ _ hs hi go.IsUnderlying.is_underlying
    (NoFmtMethods.of_methodSetIs_nil FreelistType.ty) .nil

open _root_.Perennial.fmt in
/-- `%s` of a `time.Duration`: its `String()`. -/
private theorem argOkAt_duration (hDur : _root_.Perennial.time.Duration.String.spec (GF := GF) (hG := hG))
    (x : time.Duration) :
    ⊢ argOkAt (GF := GF) methodVerbs ⟨W8 115, false⟩ (interface.mkOk time.Duration.ty #x) := by
  unfold argOkAt
  iright; iright; ileft
  isplitr
  · ipureintro; refine ⟨by decide, rfl, fun h => absurd h (by decide)⟩
  unfold argOk
  iright; iright
  isplitr
  · unfold stringMethodSpec
    imodintro
    iintro %Φ HΦ
    wp_apply hDur x as %s -
    iapply HΦ
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Error")
    have h3 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"String")
    have h4 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"CanInterface")
    simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3 h4
    refine ⟨by simpa using h1, by simpa using h2, by simpa [noArgStringSig] using h3,
      by simpa using h4⟩

open _root_.Perennial.fmt in
/-- `%p` of the `OpenFile` func. -/
private theorem argOkAt_openFile (f : GoFunc) :
    ⊢ argOkAt (GF := GF) methodVerbs ⟨W8 112, false⟩
      (interface.mkOk (go.GoType.FunctionType (go.signature.Signature
        [go.string, go.int, _root_.Perennial.os.FileMode.ty] false
        [go.GoType.PointerType _root_.Perennial.os.File.ty, go.error])) #f) := by
  unfold argOkAt
  iright; iright; iright; iright
  ipureintro
  refine ⟨rfl, ?_⟩
  rw [go.is_underlying]
  trivial

open _root_.Perennial.fmt in
/-- `%p` of the logger: nil or of a pointer type (`loggerPtrOk`). -/
private theorem argOkAt_logger (lg : GoInterface) (h : loggerPtrOk lg) :
    ⊢ argOkAt (GF := GF) methodVerbs ⟨W8 112, false⟩ lg := by
  cases lg with
  | nil => unfold argOkAt; itrivial
  | ok li =>
    obtain ⟨t, l, ht, -⟩ := h
    unfold argOkAt
    iright; iright; iright; iright
    ipureintro
    refine ⟨rfl, ?_⟩
    rw [ht, go.is_underlying]
    trivial

end args

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

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
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk time.Duration.ty #v.Timeout', interface.mkOk go.bool #v.NoGrowSync',
      interface.mkOk go.bool #v.NoFreelistSync', interface.mkOk go.bool #v.PreLoadFreelist',
      interface.mkOk FreelistType.ty #v.FreelistType', interface.mkOk go.bool #v.ReadOnly',
      interface.mkOk go.int #v.MmapFlags', interface.mkOk go.int #v.InitialMmapSize',
      interface.mkOk go.int #v.PageSize', interface.mkOk go.int #v.MaxSize',
      interface.mkOk go.bool #v.NoSync',
      interface.mkOk (go.GoType.FunctionType (go.signature.Signature
        [go.string, go.int, _root_.Perennial.os.FileMode.ty] false
        [go.GoType.PointerType _root_.Perennial.os.File.ty, go.error])) #v.OpenFile',
      interface.mkOk go.bool #v.Mlock', v.Logger', interface.mkOk go.bool #v.NoStatistics']
  isplitr
  · ipureintro; rfl
  iintro %al ⟨Hal, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply hSprintf optsFmt _ _ (DFrac.own 1) $$ [$Hfmt $Hal] as %str ⟨-, -⟩
  · iapply (_root_.Perennial.fmt.argsOk_intro fmtDirectives_optsFmt)
    simp only [_root_.Perennial.fmt.argsOkAt]
    have hlg : loggerPtrOk v.Logger' := by rw [Hv.2.2.2.1]; exact Hlg
    isplitr; · iapply argOkAt_duration hDur
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_freelist _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_int _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_int _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_int _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_int _
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    isplitr; · iapply argOkAt_openFile
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    isplitr; · iapply argOkAt_logger _ hlg
    isplitr; · iapply argOkAt_of_argWf'; exact argWf_bool _
    itrivial
  try wp_auto
  iapply HΦ
  iexists v
  isplitl
  · iapply (optsPt_eq l v dq).2
    iframe
    ipureintro; exact Hnn
  · ipureintro; exact Hv

end proof

end bbolt
end EtcdGrove
end Perennial
