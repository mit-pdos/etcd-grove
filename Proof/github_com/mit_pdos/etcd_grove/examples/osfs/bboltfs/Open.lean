/- Lean-first (no Rocq counterpart). The proof of `Open`: the file opened, locked and its size
read; a stored database (a fresh file with a valid meta is made one, `stored_of_bytes`) has a
valid meta (`readPageSize`), any other file is laid out by `init` (and is then one); the ghost
state, the two mutexes and the guarded `RWMutex` (unmapped) are allocated, and `mmap(0)` maps the
file. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Open
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.flock
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__close
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__readPageSize
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__init
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmap
public import Spec.os.OpenFile
public import Proof.os.OpenFile
public import Spec.os.File__Name
public import Spec.os.File__Close
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.OpenLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- `os.OpenFile(path, O_RDWR|O_CREATE, 0666)` of the database file: creating it if there is none
(`specCreate`, with the whole history), or opening the file there (`spec`). -/
theorem wp_OpenFile_db (wp_OpenFile : os.OpenFile.spec (GF := GF) (hG := hG))
    (wp_Create : os.OpenFile.specCreate (GF := GF) (hG := hG))
    (d b : GoString) (R : Roots) (V : Hist) (j : Ino) (t : Nat) (vo : Option w64) (n : Nat)
    (hr : RootsOk R) (hb : NameOk b) (hd : lookupH R V d = some (.dir j)) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own 1) R V ∗
        (⌜lookupH R V (child d b) = none ∧ t = 1 ∧ vo = none ∧ n = 4⌝ ∨
          ∃ (i : Ino) (m : OsMeta), ⌜lookupH R V (child d b) = some (.file i)⌝ ∗
            osMeta (GF := GF) i (DFrac.own 1) m ∗ openSt (GF := GF) i t vo n m) }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0x42))) (Val #(W32 438)))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); ∃ V' : Hist,
        osTree (DFrac.own 1) R V' ∗
        ((∃ (fd : w64) (i : Ino) (m : OsMeta),
            ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ lookupH R V' (child d b) = some (.file i)⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗
            osMeta i (DFrac.own 1) m ∗ openSt (GF := GF) i t vo n m) ∨
         (⌜err ≠ interface.nil ∧ f = null⌝ ∗ openFail (GF := GF) R V' (child d b))) }} := by
  iintro %Φ ⟨#Hos, Ht, Hf⟩ HΦ
  icases Hf with (%Ha | ⟨%i, %m, %hl, Hm, Hst⟩)
  · obtain ⟨hn, rfl, rfl, rfl⟩ := Ha
    wp_apply wp_Create d b (W32 438) R V j hb hd hn $$ [Ht]
      as %f %err (⟨%fd, %i, %h, Ht, Hm, Hf, Hfd⟩ | ⟨%h, (Ht | ⟨%i, Ht, Hm⟩)⟩)
    · iframe; iframe #
    · iapply HΦ
      iexists _; iframe Ht
      ileft
      iexists fd, i, newMeta
      iframe Hf Hfd Hm
      isplitr
      · ipureintro; exact ⟨h.1, h.2, lookupH_create _ hr hd hb hn⟩
      iapply openSt_new
    · iapply HΦ
      iexists V; iframe Ht
      iright
      isplitr; · ipureintro; exact h
      unfold openFail; iright; ipureintro; exact hn
    · iapply HΦ
      iexists _; iframe Ht
      iright
      isplitr; · ipureintro; exact h
      unfold openFail; ileft
      iexists i, newMeta; iframe Hm
      ipureintro; exact lookupH_create _ hr hd hb hn
  · wp_apply wp_OpenFile (child d b) (W32 438) 1 R V i hl $$ [Ht]
      as %f %err ⟨Ht, (⟨%fd, %h, Hf, Hfd⟩ | %h)⟩
    · iframe; iframe #
    · iapply HΦ
      iexists V; iframe Ht
      ileft
      iexists fd, i, m
      iframe
      ipureintro; exact ⟨h.1, h.2, hl⟩
    · iapply HΦ
      iexists V; iframe Ht
      iright
      isplitr; · ipureintro; exact h
      unfold openFail; ileft
      iexists i, m; iframe Hm
      ipureintro; exact hl

theorem Open.wp_proof (wp_OpenFile : os.OpenFile.spec (GF := GF) (hG := hG))
    (wp_Create : os.OpenFile.specCreate (GF := GF) (hG := hG))
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
  intro _ d nm R V j t vo n vp hr hb hd hvp
  wp_start as ⟨#Hpkg, #Hos, Ht, Hfile⟩
  imod dbFile_norm R V (child d nm) t vo n $$ Hfile with Hfile
  ihave ⟨%e2, #He2, %He2⟩ := pkgFacts_errPageSize $$ Hpkg
  (try wp_auto)
  irename «$r0» => Hdb
  generalize «$r0_ptr» = db at *
  iStructNamed Hdb
  rw [show (W64 2 ||| W64 64 : w64) = W64 0x42 from rfl]
  wp_apply wp_OpenFile_db wp_OpenFile wp_Create d nm R V j t vo n hr hb hd $$ [Ht Hfile]
    as %f %err ⟨%V', Ht, (⟨%fd, %i, %m, %Hfd, Hf, Hfdo, Hm, Hst⟩ | ⟨%Herr, Hfail⟩)⟩
  · iframe; iframe #
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iexists V'; iframe Ht
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · iexact Hfail
  obtain ⟨rfl, Hfd, hl⟩ := Hfd
  (try wp_auto)
  wp_apply wp_Name f fd (child d nm) (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_flock f fd (child d nm) (DFrac.own 1) (DFrac.own 1) _ true $$ [Hf Hfdo] as %err1 ⟨Hf, Hfdo⟩
  · iframe; iframe #
  cases err1 with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_FClose f fd (child d nm) _ $$ [Hf Hfdo] as %e Hf
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    iexists V'; iframe Ht
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · unfold openFail; ileft; iexists _, m; iframe Hm; ipureintro; exact hl
  | nil =>
  (try wp_auto)
  wp_apply wp_Stat f fd (child d nm) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) _ m $$ [Hf Hfdo Hm]
    as %fi %err2 ⟨Hf, Hfdo, Hm, Hfi⟩
  · iframe; iframe #
  icases Hfi with (⟨%fs, %Hfi, Hfs⟩ | %Hfi)
  rotate_left
  · obtain ⟨Herr2, rfl⟩ := Hfi
    cases err2 with
    | nil => exact absurd rfl Herr2
    | ok ie =>
    (try wp_auto)
    wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f (DFrac.own 1) fd (child d nm) _ i m
        (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 file Hf Hfdo]
      as %_errc ⟨-, -, -, -, -, file, Hf⟩
    · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iexists V'; iframe Ht
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · unfold openFail; ileft; iexists _, m; iframe Hm; ipureintro; exact hl
  obtain ⟨rfl, rfl⟩ := Hfi
  (try wp_auto)
  wp_apply wp_Size fs (W64 m.size) $$ [Hfs] as -
  · iexact Hfs
  imod (update_into_persistently (P := typedPointsto (GF := GF) db.[DB, go!"file"] f (DFrac.own 1)))
    $$ file with #file
  imod (update_into_persistently (P := typedPointsto (GF := GF) db.[DB, go!"path"] (child d nm) (DFrac.own 1)))
    $$ path with #Hpath
  icases openSt_facts i t vo n m $$ Hst with ⟨Hst, %Hmf⟩
  obtain ⟨Hsz40, Hmok, Hmaps⟩ := Hmf
  have hsZ : sint.Z (W64 (m.size : Int)) = m.size := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  (try wp_auto)
  rw [hsZ, show sint.Z (W64 16384) = 16384 from rfl]
  -- a stored database has a valid meta; any other file is for `init`
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ b : Bool, valid_ptr ↦ b ∗
      validSt (GF := GF) i t vo n m b ∗ db_ptr ↦ db ∗
      os.ownFile (GF := GF) f fd (child d nm) (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗ osMeta (GF := GF) i (DFrac.own 1) m ∗
      db.[DB, go!"dataref"] ↦ (zero_val DB).dataref' ∗ db.[DB, go!"datasz"] ↦ (zero_val DB).datasz' ∗
      db.[DB, go!"meta0"] ↦ (zero_val DB).meta0' ∗ db.[DB, go!"meta1"] ↦ (zero_val DB).meta1' ∗
      «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ null ∗ «$res1_ptr» ↦ e ∗ ∃ mo', osMeta (GF := GF) i (DFrac.own 1) mo')))
    with [Hst valid db Hf Hfdo Hm dataref datasz meta0 meta1 «$res0» «$res1»]
  · icases openSt_metas i t vo n m (by omega) $$ Hst with ⟨%X, HX, %HXl, HXs⟩
    wp_apply wp_readPageSize db f DFrac.discard fd (child d nm) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
        (DFrac.own 1) ⟨i, true, true⟩ m X rfl HXl (by omega) $$ [Hf Hfdo Hm HX]
      as %ps %ok %err3 ⟨-, Hf, Hfdo, Hm, HX, %Hrd⟩
    · iframe; iframe #
    cases err3 with
    | ok ie =>
      (try wp_auto)
      wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd (child d nm) _ i m
          (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
        as %_errc ⟨-, -, -, -, -, -, Hf⟩
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
        wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd (child d nm) _ i m
            (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
          as %_errc ⟨-, -, -, -, -, -, Hf⟩
        · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
        (try wp_auto)
        iright
        iexists e2
        isplitr
        · ipureintro; exact ⟨rfl, He2⟩
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
    iexists V'; iframe Ht
    iright
    isplitr
    · ipureintro; exact ⟨He, rfl⟩
    · unfold openFail; ileft; iexists _, mo'; iframe Hm; ipureintro; exact hl
  subst Hv
  (try wp_auto)
  -- `init` when no meta is valid
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ m' : OsMeta,
      db.[DB, go!"filesz"] ↦ W64 (m'.size : Int) ∗ osMeta (GF := GF) i (DFrac.own 1) m' ∗
      dbStoredAt (GF := GF) i t vo n m' ∗ db_ptr ↦ db ∗
      os.ownFile (GF := GF) f fd (child d nm) (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) ⟨i, true, true⟩ ∗
      db.[DB, go!"dataref"] ↦ (zero_val DB).dataref' ∗ db.[DB, go!"datasz"] ↦ (zero_val DB).datasz' ∗
      db.[DB, go!"meta0"] ↦ (zero_val DB).meta0' ∗ db.[DB, go!"meta1"] ↦ (zero_val DB).meta1' ∗
      «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ GoInterface.nil) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ null ∗ «$res1_ptr» ↦ e ∗ ∃ mo', osMeta (GF := GF) i (DFrac.own 1) mo')))
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
      obtain ⟨rfl, rfl, rfl⟩ := Ht
      (try wp_auto)
      wp_apply wp_init db f fd (child d nm) i (DFrac.own 1) (DFrac.own 1) m xs Hmok Hmaps Hxl (by omega)
          $$ [filesz Hf Hfdo Hm Hb] as %err4 ⟨Hf, Hfdo, Hres⟩
      · iframe; iframe #
      icases Hres with (⟨%He, Hfsz, Hm, Hb⟩ | ⟨%He, %sz, %m', Hfsz, Hm⟩)
      · subst He
        imod stored_of_init i m xs Hxl Hmok Hmaps Hsz30 $$ Hb with Hs
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; trivial
        iexists { m with size := max m.size 16384, lo := max m.size 16384, hi := max m.size 16384,
                         dur := durOf 0 (initFile xs) }
        rw [show (max (m.size : Int) 16384) = ((max m.size 16384 : Nat) : Int) by omega]
        iframe
      · cases err4 with
        | nil => exact absurd rfl He
        | ok ie =>
        (try wp_auto)
        wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd (child d nm) _ i m'
            (fun h => absurd rfl h) $$ [dataref datasz meta0 meta1 Hf Hfdo]
          as %_errc ⟨-, -, -, -, -, -, Hf⟩
        · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        isplitr
        · ipureintro; simp
        iframe
  iintro (⟨%Hv, %m', filesz, Hm, Hs, db, Hf, Hfdo, dataref, datasz, meta0, meta1, «$res0», «$res1»⟩ |
    ⟨%e, %Hv, db, «$res0», «$res1», %mo', Hm⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hv
    (try wp_auto)
    iapply HΦ
    iexists V'; iframe Ht
    iright
    isplitr
    · ipureintro; exact ⟨He, rfl⟩
    · unfold openFail; ileft; iexists _, mo'; iframe Hm; ipureintro; exact hl
  subst Hv
  iunfold dbStoredAt at Hs
  icases Hs with ⟨%mp, %mxc, %tail, %B, Hmx, Hps, Htail, #HB, %Hso⟩
  obtain ⟨⟨hmx, hclean, hmp, hpg, htl, hok', hmaps', h16', h40'⟩, ht, hvo, hn⟩ := Hso
  subst hn
  icases osBytes_split2 i mxc 0 $$ Hmx with ⟨Hmx1, Hmx2⟩
  imod open_ghost db (child d nm) i mp mxc B t vo vp hvp hmx hmp ht hvo $$ [failed Hmx2 HB]
    with ⟨%γ, %Hγ, HM, Hcur1, Hcur2, Hmap1, Hmap2, Hout1, Hout2, Hcls, Hown, #Hlast, #Htx⟩
  · iframe; iframe #
  obtain ⟨Hγvp, Hγi⟩ := Hγ
  subst Hγi
  imod sync.init_Mutex (metaR (GF := GF) γ db (child d nm)) ⊤ db.[DB, go!"metalock"] $$ metalock [HM] with #Hmeta
  · inext; iexact HM
  icases (mapFields_join db none).2 $$ [dataref meta0 meta1] with ⟨Hflds1, Hflds2⟩
  · iframe
  imod sync.init_RWMutex (mapR (GF := GF) γ db f fd (child d nm)) db.[DB, go!"mmaplock"] $$ [Hmap2 Hflds2] mmaplock
    with Hrs
  · inext; unfold mapR mapBody; iexists none; iframe; unfold mapRest; iempintro
  icases sync.ownRWMutex_slots_guard _ _ $$ Hrs with ⟨Hrs, #Hguard⟩
  icases (ownFile_halves f fd (child d nm)).1 $$ Hf with ⟨Hf1, Hf2⟩
  icases (osFd_halves fd _).1 $$ Hfdo with ⟨Hfd1, Hfd2⟩
  (try wp_auto)
  wp_apply wp_mmap γ db f fd (child d nm) (W64 0) mp false (curPgid mp) none m' rfl (by decide) (by decide) (by omega)
      $$ [Hcur1 Hmap1 Hout1 Hflds1 filesz datasz Hf1 Hfd1 Hm Hmx1 Htail Hcur2 Hf2 Hfd2 Hout2 Hps]
    as %err5 ⟨%st', %m'', Hcur1, Hmap1, Hout1, Hflds1, Hw, %Hm'', Hres⟩
  · iframe #
    unfold writerFile mmapPre writerExtra
    iframe
    have hl8 : mxc.length = 8192 := by
      have := congrArg List.length hmx; rw [List.length_map] at this; rw [this, hmp.1]
    isplitr
    · ipureintro
      exact ⟨by have := hmp.2.2.1; have := hmp.2.2.2.1; omega, hpg, hl8, htl,
        fun _ => ⟨hmx, hclean, rfl, Hfd, h16', h40', by simp only [mapLen]; omega⟩⟩
    dsimp only
    iframe
    ipureintro; exact hmaps'
  icases Hres with (⟨%He5, %base, %len, %γm, %Hst', Htok, #Hinv, Hwc⟩ | ⟨%He5, Hx⟩)
  · subst He5
    obtain ⟨rfl, Hmaps'', Hlen, -, Hbase, Hl41⟩ := Hst'
    imod sync.init_Mutex (rwR (GF := GF) γ db f fd (child d nm)) ⊤ db.[DB, go!"rwlock"] $$ rwlock
        [Hcur1 Hmap1 Hout1 Hflds1 Hw Hcls Htok Hwc] with #Hrw
    · inext
      unfold rwR
      ileft
      iexists mp, false, curPgid mp, some (base, len, γm), m''
      iframe
      isplitr
      · ipureintro; intro _; rw [Hm''.2]; exact hok'
      dsimp only
      iframe; iframe #
      ipureintro; exact ⟨Hmaps'', by omega, Hbase, Hl41⟩
    ihave Hrds := (BigSepL.bigSepL_impl (Ψ := fun _ _ => dbReader (GF := GF) γ db)) $$ Hrs []
    · imodintro
      iintro %_ %_ %_ Hr
      unfold dbReader; iexists f, fd, (child d nm); iframe; iframe #
    imod threadPool.init dbPoolN (dbReader (GF := GF) γ db) ⊤ _
        (sync.threadBound_le_actualMaxReaders (ThreadBoundLe.le (GF := GF) (2 ^ 30))) $$ Hrds with ⟨%γp, #Hpool⟩
    (try wp_auto)
    iapply HΦ
    iexists V'; iframe Ht
    ileft
    isplitr
    · ipureintro; rfl
    iexists γ
    isplitr
    · ipureintro; exact ⟨Hγvp, hl⟩
    iframe Hown Hlast Htx
    isplitr
    · unfold isDB; isplitr
      · iexists f, fd, (child d nm); iframe #
      · iexists γp; iframe #
    iframe Hpath
  · obtain ⟨Herr5, rfl⟩ := He5
    unfold writerExtra
    icases Hx with ⟨-, Hf2, Hfd2⟩
    iunfold writerFile at Hw
    icases Hw with ⟨%mxw, %tailw, %fszw, Hfsz, Hdsz, Hf1, Hfd1, Hm, -, -, -⟩
    ihave Hf := (ownFile_halves f fd (child d nm)).2 $$ [Hf1 Hf2]
    · iframe
    ihave Hfd := (osFd_halves fd _).2 $$ [Hfd1 Hfd2]
    · iframe
    unfold mapFields
    icases Hflds1 with ⟨Hd, H0, H1⟩
    icases (pointsto_halves _ _).1 $$ Hdsz with ⟨Hdsz, -⟩
    cases err5 with
    | nil => exact absurd rfl Herr5
    | ok ie =>
    (try wp_auto)
    wp_apply wp_close db (DFrac.own (1 : Qp).half) slice.nil (W64 0) null null f DFrac.discard fd (child d nm) _ γ.ino
        m'' (fun h => absurd rfl h) $$ [Hd Hdsz H0 H1 Hf Hfd]
      as %_errc ⟨-, -, -, -, -, -, Hf⟩
    · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    iexists V'; iframe Ht
    iright
    isplitr
    · ipureintro; exact ⟨by simp, rfl⟩
    · unfold openFail; ileft; iexists _, m''; iframe Hm; ipureintro; exact hl

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
