/-
`db.close()` (U11, `notes/bbolt-proof-plan.md`; design §3.11 "Open", "Close"): the unlocked close,
over owned fields. `Open`'s early failures call it with nothing mapped (`mapFields … none`); the
locked `DB.Close` with the mapping's cells gathered (`some`). Also `db.munmap()` with nothing
mapped (`DB.munmap.spec_none`: `munmap(db)` returns at once, `invalidate` clears the fields).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Munmap
public import Spec.os.File__Close
public import Spec.os.File__Fd
public import Spec.syscall.Flock

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section close
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.munmap()` with nothing mapped**: `munmap(db)` returns `nil` (no `dataref`), and
`invalidate` clears `datasz`. -/
abbrev DB.munmap.spec_none : Prop :=
  ∀ (db : Loc) (dsz : w64),
  {{ mapFields (GF := GF) db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ dsz }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ RET #interface.nil; mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 }}

theorem DB.munmap.wp_proof_none : DB.munmap.spec_none (GF := GF) (hG := hG) := by
  intro db dsz
  wp_start as ⟨Hmf, Hsz⟩
  simp only [mapFields]
  icases Hmf with ⟨Hdr, Hd, Hm0, Hm1⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  wp_bind (App (Val #(functions munmap [])) _)
  wp_func_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  iframe

/-- What `close` unmaps: nothing, or a mapping of the file at `p` with its cells. -/
def closeMapRes (p : GoString) : MapSt → IProp GF
  | none => iprop(emp)
  | some (b, l) => iprop(∃ (m : OsMeta) (vf : Nat → val), ⌜0 < l ∧ m.maps !! b = some l⌝ ∗
      osMeta p (DFrac.own 1) (some m) ∗ cellsR b 0 l vf)

/-- `db.munmap()` of what `close` unmaps: the fields cleared, the error formattable. -/
theorem DB.munmap.wp_closeRes (hMunmap : DB.munmap.spec (GF := GF) (hG := hG))
    (db : Loc) (lg : GoInterface) (ms : MapSt) (p : GoString) (hdb : db ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
        db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
        mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
        closeMapRes p ms }}
      (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
    {{ (err : GoInterface), RET #err; mapFields db (DFrac.own 1) (none : MapSt) ∗
        db.[DB, go!"datasz"] ↦ W64 0 ∗ fmtErrorOkOrNil err }} := by
  iintro %Φ ⟨#Hpkg, #Hos, #Hlg, #Hlgok, Hmf, Hdsz, Hmr⟩ HΦ
  rcases ms with _ | ⟨b, l⟩
  · simp only [closeMapRes, mapLen]
    wp_apply DB.munmap.wp_proof_none db (W64 ((0 : Nat) : Int)) $$ [Hmf Hdsz] as ⟨Hmf, Hdsz⟩
    · iframe
    iapply HΦ
    iframe
    unfold fmtErrorOkOrNil
    itrivial
  · simp only [closeMapRes, mapLen]
    icases Hmr with ⟨%m, %vf, %hm, Hosm, Hc⟩
    wp_apply hMunmap db b l lg p m vf hdb hm.1 hm.2 $$ [Hmf Hdsz Hosm Hc] as %err ⟨Hmf, Hdsz, Hr⟩
    · iframe; iframe #
    iapply HΦ
    iframe
    icases Hr with (⟨%he, -⟩ | ⟨-, #HeS, -⟩)
    · subst he; unfold fmtErrorOkOrNil; itrivial
    · iapply fmtErrorOkOrNil_of $$ HeS

omit hos in
theorem errs_head_exists (sl : GoSlice) (es : List GoInterface)
    (h : es.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) (hl : sint.Z (W64 0) < sint.Z sl.len) :
    ∃ x, es[0]? = some x := by
  have h1 := h.1
  have e1 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
  have e2 : sint.Z (W64 0) = 0 := rfl
  have hp : 0 < es.length := by omega
  exact ⟨es[0], List.getElem?_eq_getElem hp⟩

/-- **`db.close()` of a closed database**: `opened` is false, nothing happens. -/
abbrev DB.close.spec_closed : Prop :=
  ∀ (db : Loc) (dq : DFrac),
  {{ (db.[DB, go!"opened"] ↦{dq} (false : Bool) : IProp GF) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ RET #(interface.nil : GoInterface); db.[DB, go!"opened"] ↦{dq} (false : Bool) }}

/-- **`db.close()` over owned fields** (`Open`'s early failures, with nothing mapped; `DB.Close`,
with the mapping gathered): `opened`, `freelist`, `ops.writeAt` cleared, the mapping unmapped
(`invalidate` clears its fields whatever `munmap` returned), the file unlocked and closed if
there is one (`db.file` nil after `OpenFile` failed), `file` and `path` cleared. The mapping's
and the file's resources are lost (what `close` leaves of them is no one's: the database is
closed, D9), and so is the error (`Open` ignores it, `DB.Close`'s post says nothing of it). -/
abbrev DB.close.spec_owned : Prop :=
  ∀ (db : Loc) (lg : GoInterface) (dqr : DFrac) (fli : GoInterface) (wa : GoFunc) (s : GoString)
    (ms : MapSt) (p : GoString) (f : Loc),
  db ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗ db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ fli ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ wa ∗ db.[DB, go!"path"] ↦ s ∗
      mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
      closeMapRes p ms ∗
      db.[DB, go!"file"] ↦ f ∗
      (⌜f = null⌝ ∨ ∃ (fd : w64) (name : GoString) (d : OsFd), fileOwn f fd name (DFrac.own 1) ∗
        osFd fd (DFrac.own 1) d) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ (err : GoInterface), RET #err; db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ false ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ func.nil ∗ db.[DB, go!"path"] ↦ (go!"" : GoString) ∗
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      db.[DB, go!"file"] ↦ null }}

theorem DB.close.wp_proof_closed : DB.close.spec_closed (GF := GF) (hG := hG) := by
  intro db dq
  wp_start as Hop
  wp_auto
  iapply HΦ
  iframe

theorem DB.close.wp_proof_owned [os.Assumptions] [syscall.Assumptions]
    (hMunmap : DB.munmap.spec (GF := GF) (hG := hG))
    (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hFlock : syscall.Flock.spec (GF := GF) (hG := hG))
    (hClose : os.File.Close.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    DB.close.spec_owned (GF := GF) (hG := hG) := by
  intro db lg dqr fli wa s ms p f hdb
  wp_start as ⟨#Hos, #Hlg, #Hlgok, Hro, Hop, Hfl, Hwa, Hpath, Hmf, Hdsz, Hmr, Hfile, Hf⟩
  wp_auto
  ihave Herrs : (∃ (sl : GoSlice) (es : List GoInterface), errs_ptr ↦ sl ∗ sl ↦* es ∗
      ownSliceCap GoInterface sl (DFrac.own 1) : IProp GF) $$ [errs]
  · iexists slice.nil, []
    iframe
    isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  icases Herrs with ⟨%sl, %es, errs, Hsl, Hcap⟩
  -- `munmap`, its error appended
  wp_apply DB.munmap.wp_closeRes hMunmap db lg ms p hdb $$ [Hmf Hdsz Hmr] as %err ⟨Hmf, Hdsz, #HeS⟩
  · iframe; iframe #
  try wp_auto
  rcases err with _ | ii
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl2 ⟨Hsl, Hcap, -⟩
  try wp_auto
  all_goals
    iclear HeS
    try wp_auto
    ihave Herrs : (∃ (sl : GoSlice) (es : List GoInterface), errs_ptr ↦ sl ∗ sl ↦* es ∗
        ownSliceCap GoInterface sl (DFrac.own 1) : IProp GF) $$ [errs Hsl Hcap]
    · iexists _, _; iframe
    icases Herrs with ⟨%slE, %esE, errs, Hsl, Hcap⟩
    by_cases hf : f = null
    · subst hf
      rw [decide_eq_true rfl]
      try wp_auto
      ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
      wp_if_destruct
      · obtain ⟨x, hx⟩ := errs_head_exists _ _ Hsll Hif
        icases ownSlice_elem_acc (0 : Int) x _ _ _ (by omega) (by simpa using hx) $$ Hsl
          with ⟨He, Hsl⟩
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hif⟩),
          show sint.Z (W64 0) = (0 : Int) from rfl]
        try wp_auto
        iapply HΦ
        iframe
      · try wp_auto
        iapply HΦ
        iframe
    · rw [decide_eq_false hf]
      icases Hf with (%hf' | ⟨%fd, %name, %d, Hfo, Hfd⟩)
      · exact absurd hf' hf
      try wp_auto
      wp_func_call
      try wp_auto
      wp_apply hFd f fd name (DFrac.own 1) $$ [Hfo] as Hfo
      · rw [← fileOwn_eq]; iexact Hfo
      try wp_auto
      wp_apply hFlock fd _ _ d $$ [Hfd] as %e Hfd
      · iframe; iframe #
      try wp_auto
      by_cases he : e = 0
      subst he
      simp only [errnoErr, ↓reduceIte]
      try wp_auto
      rotate_left
      obtain ⟨ii, hii⟩ : ∃ ii, errnoErr e = GoInterface.ok ii :=
        ⟨⟨syscall.Errno.ty, #e⟩, by simp only [errnoErr, he, ↓reduceIte, interface.mkOk]⟩
      have hS := hErr e he
      rw [hii] at hS ⊢
      ihave #HeS := hS
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei -
      · iframe
        fmt_args_intro
        isplitl
        · fmt_arg_method; iapply fmtErrorOk_argOk $$ HeS
        · itrivial
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl3 ⟨Hsl, Hcap, -⟩
      try wp_auto
      all_goals
        ihave Herrs : (∃ (sl : GoSlice) (es : List GoInterface), errs_ptr ↦ sl ∗ sl ↦* es ∗
            ownSliceCap GoInterface sl (DFrac.own 1) : IProp GF) $$ [errs Hsl Hcap]
        · iexists _, _; iframe
        icases Herrs with ⟨%slE, %esE, errs, Hsl, Hcap⟩
        try wp_auto
        wp_apply hClose f fd name d $$ [Hfo Hfd] as %err2 ⟨Hfo, #HeC⟩
        · iframe; iframe #; try (rw [← fileOwn_eq]; iexact Hfo)
        try wp_auto
        rcases err2 with _ | ii2
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply hErrorf _ _ _ _ $$ [$Hsl2] as %ei -
        · iframe
          fmt_args_intro
          isplitl
          · fmt_arg_method; iapply fmtErrorOk_argOk
            iapply fmtErrorOkOrNil_ne (GoInterface.ok _) (fun h => nomatch h) $$ HeC
          · itrivial
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl3 ⟨Hsl, Hcap, -⟩
        all_goals
          try wp_auto
          ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
          wp_if_destruct
          · obtain ⟨x, hx⟩ := errs_head_exists _ _ Hsll Hif
            icases ownSlice_elem_acc (0 : Int) x _ _ _ (by omega) (by simpa using hx) $$ Hsl
              with ⟨He, Hsl⟩
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hif⟩),
              show sint.Z (W64 0) = (0 : Int) from rfl]
            try wp_auto
            iapply HΦ
            iframe
          · try wp_auto
            iapply HΦ
            iframe

end close

end bbolt
end EtcdGrove
end Perennial
