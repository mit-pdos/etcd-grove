/-
`Open`'s log calls (U11g): the methods it calls and its format strings' verbs (`fmtVerbs`, by
`decide`), and the arguments it passes (a `bool` under `%t`, the options under `%s`).
-/
module

public import Spec.go_etcd_io.bbolt.Options__String
public import Proof.go_etcd_io.bbolt.Mmap.Logger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section fmts

theorem infof_mem : go!"Infof" ∈ boltLogMethods := by decide
theorem errorf_mem' : go!"Errorf" ∈ boltLogMethods := by decide

set_option maxRecDepth 20000 in
theorem fmtVerbs_opening :
    fmtVerbs go!"Opening db file (%s) with mode %s and with options: %s" =
      some [W8 115, W8 115, W8 115] := by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_failed : fmtVerbs go!"Opening bbolt db (%s) failed: %v" = some [W8 115, W8 118] :=
  by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_success : fmtVerbs go!"Opening bbolt db (%s) successfully" = some [W8 115] := by
  decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_openErr : fmtVerbs go!"failed to open db file (%s): %v" = some [W8 115, W8 118] :=
  by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_lockErr :
    fmtVerbs go!"failed to lock db file (%s), readonly: %t, error: %v" =
      some [W8 115, W8 116, W8 118] := by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_statErr :
    fmtVerbs go!"failed to get db file's stats (%s): %v" = some [W8 115, W8 118] := by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_metaErr :
    fmtVerbs go!"failed to read db file's meta pages (%s): %v" = some [W8 115, W8 118] := by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_initErr :
    fmtVerbs go!"failed to initialize db file (%s): %v" = some [W8 115, W8 118] := by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_psErr :
    fmtVerbs go!"failed to get page size from db file (%s): %v" = some [W8 115, W8 118] := by
  decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_mapErr : fmtVerbs go!"failed to map db file (%s): %v" = some [W8 115, W8 118] :=
  by decide
set_option maxRecDepth 20000 in
theorem fmtVerbs_txErr : fmtVerbs go!"starting readwrite transaction failed: %v" = some [W8 118] :=
  by decide

end fmts

section args
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
/-- A `bool` is a good log argument under any verb. -/
theorem logArgOk_bool (R : IProp GF) (v : w8) (b : Bool) :
    ⊢ logArgOk (GF := GF) R v (interface.mkOk go.bool #b) := by
  iapply logArgOk_of_argWf
  apply fmt.argWf_of_argsWf
  refine _root_.Perennial.fmt.ArgsWf.cons_other go.bool #b _ ?_ ?_ ?_ .nil
  · simp [go.bool, go.string]
  · have hb : ¬ _root_.Perennial.fmt.IsIntType go.bool := by
      simp [_root_.Perennial.fmt.IsIntType, go.bool, go.int, go.int64, go.int32, go.int16,
        go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
    rintro (hi | ⟨hi, -⟩)
    · exact hb hi
    · rw [go.is_underlying] at hi; exact hb hi
  · exact Or.inr (Or.inl rfl)

omit hos in
/-- **The options, under `%s`**, lending `optsAt` to their `String()`. -/
theorem options_logArgOk (hStr : Options.String.spec (GF := GF) (hG := hG)) (l : Loc) (dq : DFrac)
    (o : OptsM) (ho : loggerPtrOk o.logger) :
    ⊢ logArgOk (GF := GF) (optsAt l dq o) (W8 115)
      (interface.mkOk (go.GoType.PointerType Options.ty) #l) := by
  simp only [logArgOk]
  iright; iright; ileft
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType Options.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType Options.ty) go!"Error")
    have h3 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType Options.ty) go!"String")
    simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3
    refine ⟨by simpa using h1, by simp [h2], by simpa [noArgStringSig] using h3, by decide⟩
  unfold stringMethodWith
  imodintro
  iintro %Φ HR HΦ
  wp_apply hStr l dq o $$ [HR] as %s HR
  · iframe; ipureintro; exact ho
  iapply HΦ $$ HR

end args

end bbolt
end EtcdGrove
end Perennial
