/- Lean-first (no Rocq counterpart). The proof of `Open`: the file opened, locked and its size
read; a stored database (a fresh file with a valid meta is made one, `stored_of_bytes`) has a
valid meta (`readPageSize`), any other file is laid out by `init` (and is then one); the ghost
state, the two mutexes and the guarded `RWMutex` (unmapped) are allocated, and `mmap(0)` maps the
file. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Open
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.flock
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__close
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__readPageSize
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__init
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmap
public import Spec.os.OpenFile
public import Spec.os.File__Name
public import Spec.os.File__Close
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.OpenLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem Open.wp_proof (wp_OpenFile : os.OpenFile.spec (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_flock : flock.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FClose : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_close : DB.close.spec (GF := GF) (hG := hG))
    (wp_readPageSize : DB.readPageSize.spec (GF := GF) (hG := hG))
    (wp_init : DB.init.spec (GF := GF) (hG := hG))
    (wp_mmap : DB.mmap.spec (GF := GF) (hG := hG)) :
    Open.spec (GF := GF) (hG := hG) := by
  intro path t vo
  wp_start as ⟨#Hpkg, #Hos, Hfile⟩
  imod dbFile_norm path t vo $$ Hfile with ⟨%mo, Hm, Hst⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, %e1, %e2, #He1, #He2, %He12, %eof, #Heof, %Heof⟩
  (try wp_auto)
  irename «$r0» => Hdb
  generalize «$r0_ptr» = db at *
  iStructNamed Hdb
  rw [show (W64 2 ||| W64 64 : w64) = W64 0x42 from rfl]
  wp_apply wp_OpenFile path (W32 438) (DFrac.own 1) mo (fun _ => rfl) $$ [Hm]
    as %f %err (⟨%fd, %Hfd, Hf, Hfdo, Hm⟩ | ⟨%Herr, %mo', -, Hm⟩)
  · iframe; iframe #
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexists mo'; iexact Hm
  obtain ⟨rfl, Hfd⟩ := Hfd
  rw [openMeta_of]
  generalize openMetaOf mo = m
  (try wp_auto)
  wp_apply wp_Name f fd path (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_flock f fd path (DFrac.own 1) (DFrac.own 1) _ true $$ [Hf Hfdo] as %err1 ⟨Hf, Hfdo⟩
  · iframe; iframe #
  cases err1 with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_FClose f fd path _ $$ [Hf Hfdo] as %e Hf
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexists some m; iexact Hm
  | nil =>
  (try wp_auto)
  wp_apply wp_Stat f fd path (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) _ m $$ [Hf Hfdo Hm]
    as %fi %err2 ⟨Hf, Hfdo, Hm, Hfi⟩
  · iframe; iframe #
  icases Hfi with (⟨%fs, %Hfi, Hfs⟩ | %Hfi)
  rotate_left
  · obtain ⟨Herr2, rfl⟩ := Hfi
    cases err2 with
    | nil => exact absurd rfl Herr2
    | ok ie =>
    (try wp_auto)
    wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f (DFrac.own 1) fd path _ path m
        (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 file Hf Hfdo]
      as ⟨-, -, -, -, -, file, Hf⟩
    · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexists some m; iexact Hm
  obtain ⟨rfl, rfl⟩ := Hfi
  (try wp_auto)
  wp_apply wp_Size fs (W64 m.size) $$ [Hfs] as -
  · iexact Hfs
  imod (update_into_persistently (P := typedPointsto (GF := GF) db.[DB, go!"file"] f (DFrac.own 1)))
    $$ file with #file
  imod (update_into_persistently (P := typedPointsto (GF := GF) db.[DB, go!"path"] path (DFrac.own 1)))
    $$ path with #Hpath
  icases openSt_facts path t vo m $$ Hst with ⟨Hst, %Hmf⟩
  obtain ⟨Hsz40, Hmok, Hmaps⟩ := Hmf
  have hsZ : sint.Z (W64 (m.size : Int)) = m.size := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  (try wp_auto)
  rw [hsZ, show sint.Z (W64 16384) = 16384 from rfl]
  -- a stored database has a valid meta; any other file is for `init`
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ b : Bool, valid_ptr ↦ b ∗
      validSt (GF := GF) path t vo m b ∗ db_ptr ↦ db ∗
      os.ownFile (GF := GF) f fd path (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) ⟨path, true, true⟩ ∗ osMeta (GF := GF) path (DFrac.own 1) (some m) ∗
      db.[DB, go!"dataref"] ↦ (zero_val DB).dataref' ∗ db.[DB, go!"datasz"] ↦ (zero_val DB).datasz' ∗
      db.[DB, go!"meta0"] ↦ (zero_val DB).meta0' ∗ db.[DB, go!"meta1"] ↦ (zero_val DB).meta1' ∗
      «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ null ∗ «$res1_ptr» ↦ e ∗ ∃ mo', osMeta (GF := GF) path (DFrac.own 1) mo')))
    with [Hst valid db Hf Hfdo Hm dataref datasz meta0 meta1 «$res0» «$res1»]
  · icases openSt_metas path t vo m (by omega) $$ Hst with ⟨%X, HX, %HXl, HXs⟩
    wp_apply wp_readPageSize db f DFrac.discard fd path (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
        (DFrac.own 1) ⟨path, true, true⟩ m X rfl HXl (by omega) $$ [Hf Hfdo Hm HX]
      as %ps %ok %err3 ⟨-, Hf, Hfdo, Hm, HX, %Hrd⟩
    · iframe; iframe #
    cases err3 with
    | ok ie =>
      (try wp_auto)
      wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd path _ path m
          (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
        as ⟨-, -, -, -, -, -, Hf⟩
      · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      isplitr
      · ipureintro; simp
      iframe
    | nil =>
    have Hrd := Hrd rfl
    (try wp_auto)
    cases ok with
    | false =>
      (try wp_auto)
      icases HXs with (⟨%_, HXs⟩ | ⟨%Hv, -⟩)
      rotate_left
      · exfalso; obtain ⟨i, hi, hv⟩ := Hv; exact Hrd.2 rfl i hi hv
      ihave Hv := HXs $$ HX
      ileft
      isplitr
      · ipureintro; trivial
      iexists false
      iframe
    | true =>
      by_cases hps : ps = W64 4096
      · subst hps
        (try wp_auto)
        icases HXs with (⟨%Hv, -⟩ | ⟨%_, HXs⟩)
        · exfalso; obtain ⟨i, hi, hv, -⟩ := Hrd.1 rfl; exact Hv i hi hv
        ihave Hv := HXs $$ HX
        ileft
        isplitr
        · ipureintro; trivial
        iexists true
        iframe
      · (try wp_auto)
        simp only [decide_eq_false hps, Bool.not_false]
        (try wp_auto)
        wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd path _ path m
            (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
          as ⟨-, -, -, -, -, -, Hf⟩
        · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
        (try wp_auto)
        iright
        iexists e2
        isplitr
        · ipureintro; exact ⟨rfl, He12.2⟩
        iframe
  · unfold openSt at *
    icases Hst with (⟨%Ht, Hi⟩ | Hs)
    rotate_left
    · unfold dbStoredAt
      icases Hs with ⟨%mp, %mxc, %tail, %B, -, -, -, -, %H⟩
      exfalso; have := H.1.2.2.2.2.2.2.2.1; omega
    ileft
    isplitr
    · ipureintro; trivial
    iexists false
    iframe
    simp only [validSt]
    iframe
    (try (ipureintro; exact Ht))
  iintro (⟨%Hv, %b, valid, Hvs, db, Hf, Hfdo, Hm, dataref, datasz, meta0, meta1, «$res0», «$res1»⟩ |
    ⟨%e, %Hv, db, «$res0», «$res1», %mo', Hm⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨He, rfl⟩
    · iexists mo'; iexact Hm
  subst Hv
  (try wp_auto)
  -- `init` when no meta is valid
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ m' : OsMeta,
      db.[DB, go!"filesz"] ↦ W64 (m'.size : Int) ∗ osMeta (GF := GF) path (DFrac.own 1) (some m') ∗
      dbStoredAt (GF := GF) path t vo m' ∗ db_ptr ↦ db ∗
      os.ownFile (GF := GF) f fd path (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) ⟨path, true, true⟩ ∗
      db.[DB, go!"dataref"] ↦ (zero_val DB).dataref' ∗ db.[DB, go!"datasz"] ↦ (zero_val DB).datasz' ∗
      db.[DB, go!"meta0"] ↦ (zero_val DB).meta0' ∗ db.[DB, go!"meta1"] ↦ (zero_val DB).meta1' ∗
      «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ null ∗ «$res1_ptr» ↦ e ∗ ∃ mo', osMeta (GF := GF) path (DFrac.own 1) mo')))
    at next with [Hvs filesz db Hf Hfdo Hm dataref datasz meta0 meta1 «$res0» «$res1»]
  · cases b with
    | true =>
      simp only [validSt]
      (try wp_auto)
      ileft
      isplitr
      · ipureintro; trivial
      iexists m
      iframe
    | false =>
      simp only [validSt, initAt]
      icases Hvs with ⟨%Ht, %xs, Hb, %Hxs⟩
      obtain ⟨Hxl, -, -, Hsz30, -⟩ := Hxs
      obtain ⟨rfl, rfl⟩ := Ht
      (try wp_auto)
      wp_apply wp_init db f fd path (DFrac.own 1) (DFrac.own 1) m xs Hmok Hmaps Hxl (by omega)
          $$ [filesz Hf Hfdo Hm Hb] as %err4 ⟨Hf, Hfdo, Hres⟩
      · iframe; iframe #
      icases Hres with (⟨%He, Hfsz, Hm, Hb⟩ | ⟨%He, %sz, %m', Hfsz, Hm⟩)
      · subst He
        imod stored_of_init path m xs Hxl Hmok Hmaps Hsz30 $$ Hb with Hs
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; trivial
        iexists { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384 }
        rw [show (max (m.size : Int) 16384) = ((max m.size 16384 : Nat) : Int) by omega]
        iframe
      · cases err4 with
        | nil => exact absurd rfl He
        | ok ie =>
        (try wp_auto)
        wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd path _ path m'
            (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
          as ⟨-, -, -, -, -, -, Hf⟩
        · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        isplitr
        · ipureintro; simp
        iframe
  sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
