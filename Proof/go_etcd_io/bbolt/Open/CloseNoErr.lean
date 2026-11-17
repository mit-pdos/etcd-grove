/-
`db.close()` over owned fields with no error of the environment (S3a, `notes/bbolt-integration-plan.md`):
under **no I/O error** (`NoIoErr Sio`) and **no error of `flock`, `mmap`, `munmap`** (`NoMapLockErr Sio`,
pending the user's review), every inode covered, `munmap` returns `nil` (`DB.munmap.specNoErr`), the
`LOCK_UN` `funlock` errno 0 (`syscall.Flock.specNoErr`) and the file's `Close` `nil`
(`os.File.Close.specNoErr`): no error is appended, and `close` returns `nil`. What
`DB.Close_noErr.spec` rests on.
-/
module

public import Proof.go_etcd_io.bbolt.Open.Close
public import Proof.go_etcd_io.bbolt.Mmap.MunmapNoErr
public import Spec.os.File__CloseNoErr
public import Spec.syscall.FlockNoErr

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

/-- `db.munmap()` of what `close` unmaps, with no error: the fields cleared. -/
theorem DB.munmap.wp_closeResNoErr (hMunmap : DB.munmap.specNoErr (GF := GF) (hG := hG))
    (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (db : Loc) (lg : GoInterface) (ms : MapSt) (p : BFile) (hdb : db ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
        db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
        mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
        closeMapRes p ms }}
      (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
    {{ RET #(interface.nil : GoInterface); mapFields db (DFrac.own 1) (none : MapSt) ∗
        db.[DB, go!"datasz"] ↦ W64 0 }} := by
  iintro %Φ ⟨#Hpkg, #Hos, #Hlg, #Hlgok, Hmf, Hdsz, Hmr⟩ HΦ
  rcases ms with _ | ⟨b, l⟩
  · simp only [closeMapRes, mapLen]
    wp_apply DB.munmap.wp_proof_none db (W64 ((0 : Nat) : Int)) $$ [Hmf Hdsz] as ⟨Hmf, Hdsz⟩
    · iframe
    iapply HΦ
    iframe
  · simp only [closeMapRes, mapLen]
    icases Hmr with ⟨%m, %vf, %hm, Hosm, Hc⟩
    wp_apply hMunmap Sio hS db b l lg p m vf hdb hm.1 hm.2 $$ [Hmf Hdsz Hosm Hc] as ⟨Hmf, Hdsz, -⟩
    · iframe; iframe #
    iapply HΦ
    iframe

/-- **`db.close()` over owned fields, with no error** (`DB.close.spec_owned` under the premises): `nil`
returned. -/
abbrev DB.close.spec_ownedNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (db : Loc) (lg : GoInterface) (dqr : DFrac) (fli : GoInterface) (wa : GoFunc) (s : GoString)
    (ms : MapSt) (p : BFile) (f : Loc),
  db ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗ db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ true ∗ db.[DB, go!"freelist"] ↦ fli ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ wa ∗ db.[DB, go!"path"] ↦ s ∗
      mapFields db (DFrac.own 1) ms ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen ms : Int) ∗
      closeMapRes p ms ∗
      db.[DB, go!"file"] ↦ f ∗
      (⌜f = null⌝ ∨ ∃ (fd : w64) (name : GoString) (d : OsFd), fileOwn f fd name (DFrac.own 1) ∗
        osFd fd (DFrac.own 1) d ∗ lockToks fd d) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"close")) (Val #()))
  {{ RET #(interface.nil : GoInterface); db.[DB, go!"readOnly"] ↦{dqr} false ∗
      db.[DB, go!"opened"] ↦ false ∗ db.[DB, go!"freelist"] ↦ interface.nil ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦ func.nil ∗ db.[DB, go!"path"] ↦ (go!"" : GoString) ∗
      mapFields db (DFrac.own 1) (none : MapSt) ∗ db.[DB, go!"datasz"] ↦ W64 0 ∗
      db.[DB, go!"file"] ↦ null }}

theorem DB.close.wp_proof_ownedNoErr [os.Assumptions] [syscall.Assumptions]
    (hMunmap : DB.munmap.specNoErr (GF := GF) (hG := hG))
    (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hFlock : syscall.Flock.specNoErr (GF := GF) (hG := hG))
    (hClose : os.File.Close.specNoErr (GF := GF) (hG := hG)) :
    DB.close.spec_ownedNoErr (GF := GF) (hG := hG) := by
  intro Sio _ _ hS db lg dqr fli wa s ms p f hdb
  wp_start as ⟨#Hos, #Hlg, #Hlgok, Hro, Hop, Hfl, Hwa, Hpath, Hmf, Hdsz, Hmr, Hfile, Hf⟩
  wp_auto
  -- `munmap`: `nil`, nothing appended
  wp_apply DB.munmap.wp_closeResNoErr hMunmap Sio hS db lg ms p hdb $$ [Hmf Hdsz Hmr] as ⟨Hmf, Hdsz⟩
  · iframe; iframe #
  try wp_auto
  by_cases hf : f = null
  · subst hf
    rw [decide_eq_true rfl]
    try wp_auto
    iapply HΦ
    iframe
  · rw [decide_eq_false hf]
    icases Hf with (%hf' | ⟨%fd, %name, %d, Hfo, Hfd, Hlt⟩)
    · exact absurd hf' hf
    iunfold lockToks at Hlt
    icases Hlt with ⟨Hlo, Hfl⟩
    try wp_auto
    wp_func_call
    try wp_auto
    wp_apply hFd f fd name (DFrac.own 1) $$ [Hfo] as Hfo
    · rw [← fileOwn_eq]; iexact Hfo
    try wp_auto
    wp_apply hFlock Sio hS fd (W64 8) d none false rfl (fun h => absurd rfl h) (Or.inl rfl)
      $$ [Hfd Hfl] as %e ⟨%he, Hout⟩
    · iframe; iframe #
    have he0 : e = 0 := by
      rcases he with he | ⟨hn, -⟩
      · exact he
      · exact absurd rfl hn
    subst he0
    unfold lockOut
    icases Hout with ⟨%d', Hfd, Hfl, %hd'⟩
    ihave Hlo : lockTok LockKind.ofd fd d' $$ [Hlo]
    · rcases hd'.1 with rfl | rfl
      · iexact Hlo
      · iapply (lockTok_setLk_ne fd d none (by decide)).2; iexact Hlo
    simp only [errnoErr, ↓reduceIte]
    try wp_auto
    wp_apply hClose Sio hS f fd name d' $$ [Hfo Hfd Hlo Hfl] as Hfo
    · unfold lockToks; iframe; iframe #
    try wp_auto
    iapply HΦ
    iframe

end close

end bbolt
end EtcdGrove
end Perennial
