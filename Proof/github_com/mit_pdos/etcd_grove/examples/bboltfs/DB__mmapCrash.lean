/- Lean-first (no Rocq counterpart). The proof of `db.mmap(minsz)`'s crash-aware spec: as
`DB__mmap.lean`'s, with `DB.munmap.specCrash`, `Mmap.specCrashS`/`Munmap.specCrashS` (whose
obligations are `writer_okS`), and the writer's halves of the meta pages and its `OsMeta` out of its
idle state (`csOwn_idle`, `writer_thrBytes`) for the new mapping's cells. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmap
public import Proof.os.CrashStSpec

@[expose] public section

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

/-- The writer's half of its idle state's bytes (`writerFileC`): the meta pages and the tail. -/
theorem writer_thrBytes (p : GoString) (m : OsMeta) (bs : List (w8 × Bool)) (hwm : Nat)
    (h2 : 2 ≤ hwm) (hl : 4096 * hwm ≤ bs.length) :
    thrBytes (GF := GF) p ⟨m, bs, 8192, 4096 * hwm, .idle⟩ ⊣⊢
      osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) (bs.take 8192) ∗
      osBytes (GF := GF) p (4096 * hwm) (DFrac.own (1 : Qp).half) (bs.drop (4096 * hwm)) := by
  have h := idle_thrBytes (GF := GF) p m (bs.take 8192) ((bs.drop 8192).take (4096 * hwm - 8192))
    (bs.drop (4096 * hwm)) 8192 (4096 * hwm) (by simp only [List.length_take]; omega)
    (by simp only [List.length_take, List.length_drop]; omega)
  have e : bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++ bs.drop (4096 * hwm)) = bs := by
    rw [show bs.drop (4096 * hwm) = (bs.drop 8192).drop (4096 * hwm - 8192) by
      rw [List.drop_drop, show 8192 + (4096 * hwm - 8192) = 4096 * hwm by omega],
      List.take_append_drop, List.take_append_drop]
  rw [e] at h
  exact h

/-- What `munmap` leaves the writer besides `mappingResC`, in the state `st`. -/
def unmapRestC (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat) :
    MapSt → IProp GF
  | some (base, len, _) => iprop(⌜m.maps = {[base := len]} ∧ 0 < base.addr⌝)
  | none => iprop(csOwn (GF := GF) p γc (some ⟨m, bs, fa, fb, .idle⟩) ∗ ⌜m.maps = ∅⌝)

/-- `mmap_prep` over the crash invariant. -/
theorem mmap_prepC (γ : DBNames) (f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat) (st : MapSt)
    (h2 : 2 ≤ hwm) (hl : bs.length = m.size) (hcc : commitClean m bs) :
    osInv (GF := GF) ∗ csInv (GF := GF) dbCrashN p γc (dbOk p) ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ csOwn (GF := GF) p γc (some ⟨m, bs, fa, fb, .idle⟩) ∗
      mmapPre (GF := GF) γ f fd p mp fl hwm m st ∗ mapRest (GF := GF) γ f fd p 1 st ⊢
    |={⊤}=> ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ writerExtra (GF := GF) γ f fd p mp fl hwm ∗
      ghostVar γ.out (1 : Qp).half false ∗
      ([∗list] r ∈ List.range' 2 (hwm - 2), ∃ B, pageIs (GF := GF) p r B) ∗
      mappingResC (GF := GF) p γc m bs fa fb (mapSlice st) ∗
      unmapRestC (GF := GF) p γc m bs fa fb st ∗
      ⌜∀ base len γm, st = some (base, len, γm) → 0 < base.addr⌝ := by
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only [mmapPre, mapRest, mapSlice, unmapRestC]
    iintro ⟨#Hos, #Hci, Hcur, Hout, Hm, ⟨%Hmaps, Hx, Ho, Hps⟩, -⟩
    imodintro
    iframe
    unfold mappingResC
    isplitl []
    · ileft; ipureintro; rfl
    isplitl
    · iframe; ipureintro; exact Hmaps
    · ipureintro; intro _ _ _ h; cases h
  · dsimp only [mmapPre, mapRest, mapSlice, unmapRestC]
    iintro ⟨#Hos, #Hci, Hcur, Hout, Hm, ⟨%Hf, Htok, Hwc⟩, ⟨-, Htok2, #Hinv, Hf2, Hfd2⟩⟩
    obtain ⟨Hmaps, Hlen, Hbase, Hlen41⟩ := Hf
    icombine Htok Htok2 as Htok
    ihave Hc := mapInv_close γ p base len γm $$ [Htok]
    · iframe; iframe #
    imod Hc
    icases Hc with >Hc
    iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells at Hc
    icases Hc with ⟨%mp', %fl', %hwm', Hcur2, %Hl, Hpc, Hmc⟩
    icombine Hcur Hcur2 gives % ⟨_, Heq⟩
    simp only [Prod.mk.injEq] at Heq
    obtain ⟨rfl, rfl, rfl⟩ := Heq
    icases Hmc with (Hout2 | ⟨Hout2, %mc, Hm0, Hm1, %Hmc⟩)
    · icombine Hout Hout2 gives % ⟨_, Heq⟩
      cases Heq
    icases pagesCells_split p base (hwm - 2) 2 $$ Hpc with ⟨Hps, Hpc⟩
    rw [show 4096 * 2 = 8192 by rfl]
    ihave Hall := mapCells_gather base hwm len h2 Hl mc Hmc.1 $$ [Hwc Hm0 Hm1 Hpc]
    · iframe
    iunfold cellsAny at Hall
    icases Hall with ⟨%vf, Hall⟩
    imodintro
    iframe
    unfold writerExtra mappingResC
    iframe
    isplitl [Hall Hm]
    · iright
      iexists base, W64 len, vf
      have hl' : (W64 (len : Int)).toNat = len := by
        rw [BitVec.toNat_ofInt]; omega
      rw [hl']
      iframe; iframe #
      ipureintro
      refine ⟨rfl, Hbase, ?_, ?_, hl, hcc⟩
      · have := sint_Z_W64_nat len (by omega); simp only [sint.Z] at this; omega
      · rw [Hmaps]; simp
    · isplit
      · ipureintro; exact ⟨Hmaps, Hbase⟩
      · ipureintro; intro b l g h; cases h; exact Hbase

/-- `mmap_unmapped` over the crash invariant: the writer's state, with other mappings, none if
`munmap` succeeded. -/
theorem mmap_unmappedC (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool))
    (fa fb : Nat) (st : MapSt) (err : GoInterface) :
    unmappedResC (GF := GF) p γc m bs fa fb (mapSlice st) err ∗
      unmapRestC (GF := GF) p γc m bs fa fb st ⊢
      ∃ M : GMap Loc Nat, csOwn (GF := GF) p γc (some ⟨{ m with maps := M }, bs, fa, fb, .idle⟩) ∗
        ⌜err = interface.nil → M = ∅⌝ := by
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only [unmapRestC]
    iintro ⟨-, Hm, %Hmaps⟩
    iexists m.maps; iframe; ipureintro; exact fun _ => Hmaps
  · dsimp only [unmapRestC, mapSlice]
    iintro ⟨Hu, %Hr⟩
    obtain ⟨Hmaps, Hbase⟩ := Hr
    unfold unmappedResC
    icases Hu with (%Hnil | ⟨%b, %l, %vf, %e, %Heq, Hu⟩)
    · exfalso
      have := congrArg GoSlice.ptr Hnil.1; simp [slice.nil] at this; subst this
      simp [null] at Hbase
    · obtain ⟨Hsl, rfl⟩ := Heq
      have hb : b = base := (congrArg GoSlice.ptr Hsl).symm
      subst hb
      icases Hu with (⟨%He, Hm⟩ | ⟨%He, (Hm | ⟨Hm, -⟩)⟩)
      · iexists _; iframe; ipureintro
        intro _; simp only [Hmaps]; exact GMap.delete_singleton _ _
      · iexists _; iframe; ipureintro
        exact fun h => absurd h (errnoErr_ne_nil e He)
      · iexists m.maps; iframe; ipureintro
        exact fun h => absurd h (errnoErr_ne_nil e He)

theorem DB.mmap.wp_proof_crash (wp_munmap : DB.munmap.specCrash (GF := GF) (hG := hG))
    (wp_mmapSize : mmapSize.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Mmap : golang_org.x.sys.unix.Mmap.specCrashS (GF := GF) (hG := hG))
    (wp_Madvise : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG))
    (wp_Munmap : golang_org.x.sys.unix.Munmap.specCrashS (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_meta : Page.«meta».spec (GF := GF) (hG := hG)) :
    DB.mmap.specCrash (GF := GF) (hG := hG) := by
  intro γ γc db f fd p minsz mp fl hwm st m bs Hfl Hmin0 Hmin
  wp_start as ⟨#Hpkg, #Hos, #Hci, #Hfile, #Hguard, Hcur, Hmap, Hout, Hflds, Hw, Hpre⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, -⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlocked, HR⟩
  unfold mapR mapBody
  icases HR with ⟨%st0, Hmap0, Hflds0, HR⟩
  icombine Hmap Hmap0 gives % ⟨_, Heq⟩
  subst Heq
  unfold writerFileC
  icases Hw with ⟨%fsz, Hfsz, Hdsz, Hf, Hfd, Hown, %Hw⟩
  icases csOwn_wf' _ _ _ $$ Hown with ⟨Hown, %Hwf⟩
  have hl : bs.length = m.size := Hwf.1
  obtain ⟨h2, hsz, Hw'⟩ := Hw
  obtain ⟨hmp, hcc, hfsz, hfd0, h16, hsz30, hml⟩ := Hw' Hfl
  subst hfsz
  wp_auto
  have _hsz : sint.Z (W64 (m.size : Int)) = m.size := sint_Z_W64_nat _ (by omega)
  wp_join iprop(∃ s : w64, size_ptr ↦ s ∗ minsz_ptr ↦ minsz ∗
      ⌜sint.Z minsz ≤ sint.Z s ∧ (m.size : Int) ≤ sint.Z s ∧ sint.Z s ≤ 2 ^ 40 ∧ sint.Z s ≤ 2 ^ 30⌝)
    with [size minsz] as ⟨%s, size, minsz, %Hs⟩
  · iexists minsz; iframe; ipureintro; omega
  · iexists _; iframe; ipureintro; omega
  wp_apply wp_mmapSize s as %sz %Hsz2
  · ipureintro; omega
  (try wp_auto)
  ihave Hp := mmap_prepC γ f fd p mp fl hwm γc m bs 8192 (4096 * hwm) st h2 hl hcc
    $$ [Hcur Hout Hown Hpre HR]
  · iframe; iframe #
  imod Hp with ⟨Hcur, Hout, Hx, Ho, Hps, Hmr, Hrest, %Hpos⟩
  icases (mapFields_join db st).1 $$ [Hflds Hflds0] with ⟨Hd, H0, H1⟩
  · iframe
  wp_apply wp_munmap db (DFrac.own 1) (mapSlice st) (W64 (mapLen st)) (mapPtr0 st) (mapPtr1 st) p γc
      m bs 8192 (4096 * hwm) (fun _ => rfl)
    $$ [Hd Hdsz H0 H1 Hmr] as %err ⟨Hd, Hdsz, H0, H1, Hun⟩
  · iframe
  rw [mapSlice_ite st Hpos (fun st => W64 (mapLen st)) (W64 0) rfl,
    mapSlice_ite st Hpos mapPtr0 null rfl, mapSlice_ite st Hpos mapPtr1 null rfl]
  ihave Hm := mmap_unmappedC p γc m bs 8192 (4096 * hwm) st err $$ [Hun Hrest]
  · iframe
  icases Hm with ⟨%M1, Hown, %HM1⟩
  imod ghostVar_update_halves none γ.map st st $$ Hmap Hmap0 with ⟨Hmap, Hmap0⟩
  icases (mapFields_join db none).2 $$ [Hd H0 H1] with ⟨Hflds, Hflds0⟩
  · iframe
  have hcc1 : ∀ M : GMap Loc Nat, commitClean { m with maps := M } bs :=
    fun M => commitClean_meta hcc rfl rfl
  have hpost : ∀ M : GMap Loc Nat, 2 ≤ hwm ∧ 4096 * hwm ≤ ({ m with maps := M } : OsMeta).size ∧
      (fl = false → (bs.map Prod.fst).take 8192 = mp ∧ commitClean { m with maps := M } bs ∧
        m.size = ({ m with maps := M } : OsMeta).size ∧ 0 ≤ fd.toInt ∧
        4 * 4096 ≤ ({ m with maps := M } : OsMeta).size ∧
        ({ m with maps := M } : OsMeta).size ≤ 2 ^ 30 ∧ mapLen none ≤ 2 ^ 30) :=
    fun M => ⟨h2, hsz, fun _ => ⟨hmp, hcc1 M, rfl, hfd0, h16, hsz30, by simp only [mapLen]; omega⟩⟩
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    iapply HΦ
    iexists none, { m with maps := M1 }
    iframe
    isplitr [Hx]
    · ipureintro; exact hpost M1
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iright
    iframe
    ipureintro; simp
  | nil =>
  have HM1' := HM1 rfl
  subst HM1'
  (try wp_auto)
  wp_apply wp_Fd f fd p _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have Hsz0 : 0 < (sz).toInt := by simp only [sint.Z] at Hsz2; omega
  wp_apply wp_Mmap fd (W64 0) sz _ _ _ ⟨p, true, true⟩ dbCrashN γc (dbOk p) { m with maps := ∅ } bs
      8192 (4096 * hwm) rfl rfl Hsz0 (by decide) (by left; decide) dbCrashN_disj
      (fun base => writer_okS (m := { m with maps := ∅ }) 8192 (4096 * hwm) hl (hcc1 ∅) _)
    $$ [Hfd Hown] as %sl %e ⟨Hfd, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%base, %Hok, Hown, %bs0, %Hbs, Hcells⟩ | ⟨%Herr, Hown⟩)
  rotate_left
  · obtain ⟨He, rfl⟩ := Herr
    unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    iapply HΦ
    iexists none, { m with maps := ∅ }
    iframe
    isplitr [Hx]
    · ipureintro; exact hpost ∅
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iright
    iframe
    ipureintro; simp [interface.mkOk]
  obtain ⟨rfl, rfl⟩ := Hok
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  wp_apply wp_Madvise ⟨base, sz, sz⟩ _ (by decide) as %e2 -
  (try wp_auto)
  wp_join (Q := fun v => iprop(err_ptr ↦ errnoErr e2 ∗ ⌜∃ b : Bool, v = #b ∧ (b = true → e2 ≠ 0)⌝))
    at (if: _ then _ else #false) with [err]
  · by_cases he2 : e2 = 0
    · subst he2; unfold errnoErr; rw [if_pos rfl]
      wp_auto
      iframe; ipureintro; exact ⟨false, rfl, by simp⟩
    · unfold errnoErr; rw [if_neg he2]
      wp_auto
      iframe; ipureintro; exact ⟨_, rfl, fun _ => he2⟩
  iintro ⟨err, %Hv⟩
  obtain ⟨bb, hv, Hbb⟩ := Hv
  subst hv
  cases bb with
  | true =>
    have he2 := Hbb rfl
    (try wp_auto)
    wp_apply wp_Munmap base sz p dbCrashN γc (dbOk p)
        { m with maps := <[base := sz.toNat]> (∅ : GMap Loc Nat) } bs 8192 (4096 * hwm) _ Hsz0
        (GMap.lookup_insert _ _ _) dbCrashN_disj
        (writer_okS (m := { m with maps := <[base := sz.toNat]> (∅ : GMap Loc Nat) }) 8192 (4096 * hwm) hl (hcc1 _) _)
      $$ [Hown Hcells] as %e3 Hm3
    · iframe; iframe #
    ihave Hm : ∃ M2 : GMap Loc Nat,
        csOwn (GF := GF) p γc (some ⟨{ m with maps := M2 }, bs, 8192, 4096 * hwm, .idle⟩) $$ [Hm3]
    · icases Hm3 with (⟨-, Hm⟩ | ⟨-, (Hm | ⟨Hm, -⟩)⟩) <;> (iexists _; iexact Hm)
    icases Hm with ⟨%M2, Hown⟩
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    iapply HΦ
    iexists none, { m with maps := M2 }
    iframe
    isplitr [Hx]
    · ipureintro; exact hpost M2
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iright
    iframe
    ipureintro; exact ⟨errnoErr_ne_nil e2 he2, rfl⟩
  | false =>
  -- the writer's halves of its `OsMeta` and of the meta pages, out of its idle state
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm, Hb⟩, %Hwf2⟩
  icases (writer_thrBytes p _ bs hwm h2 (by omega)).1 $$ Hb with ⟨Hmx, Htail⟩
  obtain ⟨mxc, hmxc_def⟩ : ∃ mxc, mxc = bs.take 8192 := ⟨_, rfl⟩
  rw [← hmxc_def]
  have hmxc : mxc.length = 8192 := by rw [hmxc_def, List.length_take]; omega
  have hmxmp : mxc.map Prod.fst = mp := by rw [hmxc_def, List.map_take, hmp]
  -- the new mapping: its cells against the committed pages and the meta windows
  have hlen : (sz.toNat : Int) = sint.Z sz := by have := Hsz2.2.1; word
  ihave %Hbd := cellsR_bounds base sz.toNat _ (by omega) $$ Hcells
  have hl2 : 4096 * hwm ≤ sz.toNat := by omega
  icases mapCells_scatter base hwm sz.toNat h2 hl2 _ $$ Hcells with ⟨Hwc, Hc0, Hc1, Hpc⟩
  have hb : ({ m with maps := <[base := sz.toNat]> (∅ : GMap Loc Nat) } : OsMeta).maps !! base =
      some sz.toNat := GMap.lookup_insert _ _ _
  rw [show 8192 = 4096 * 2 by rfl]
  iapply pages_agree _ rfl p _ _ base sz.toNat hb (by simp) _ (hwm - 2) 2 _ (by omega)
    $$ Hos Hm Hps Hpc
  iintro Hm Hps
  iapply window_agree _ rfl p _ _ base sz.toNat hb (by simp) _ _ mxc 16 64 _ (by omega) (by omega)
    $$ Hos Hm Hmx Hc0
  iintro Hm Hmx Hc0
  iapply window_agree _ rfl p _ _ base sz.toNat hb (by simp) _ _ mxc 4112 64 _ (by omega) (by omega)
    $$ Hos Hm Hmx Hc1
  iintro Hm Hmx Hc1
  -- fold the writer's idle state back
  rw [hmxc_def]
  ihave Hown := (csOwn_idle (GF := GF) p γc
      ⟨{ m with maps := <[base := sz.toNat]> (∅ : GMap Loc Nat) }, bs, 8192, 4096 * hwm, .idle⟩ rfl).2
    $$ [Hv Hm Hmx Htail]
  · iframe Hv Hm
    isplitl
    · iapply (writer_thrBytes p _ bs hwm h2 (by omega)).2; iframe
    · ipureintro; exact Hwf2
  rw [← hmxc_def]
  -- the new mapping's invariant
  have hw0 : (((mxc.map Prod.fst).drop 16).take 64).length = 64 := by
    rw [List.length_take, List.length_drop, List.length_map, hmxc]; rfl
  have hw1 : (((mxc.map Prod.fst).drop 4112).take 64).length = 64 := by
    rw [List.length_take, List.length_drop, List.length_map, hmxc]; rfl
  iunfold writerExtra at Hx
  icases Hx with ⟨Hcur2, Hf2, Hfd2⟩
  ihave Hc : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells γ p base sz.toNat
      $$ [Hcur2 Hps Ho Hc0 Hc1]
  · iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells
    iexists mp, fl, hwm
    iframe Hcur2 Hps
    isplitr
    · ipureintro; exact hl2
    iright
    iframe Ho
    iexists (((mxc.map Prod.fst).drop 16).take 64 ++ ((mxc.map Prod.fst).drop 4112).take 64)
    rw [List.take_left' hw0, List.drop_left' hw0]
    iframe
    ipureintro
    refine ⟨by simp only [List.length_append, hw0, hw1], fun hfl => ?_⟩
    rw [hmxmp]
  ihave Hinv := mapInv_alloc γ p base sz.toNat (by have := Hsz2.2.1; word) $$ Hc
  imod Hinv with ⟨%γm, Htok, #Hinv⟩
  icases (ghostVar_split_half γm 1 ()).1 $$ Htok with ⟨Htok, Htok2⟩
  imod ghostVar_update_halves (some (base, sz.toNat, γm)) γ.map none none $$ Hmap Hmap0 with ⟨Hmap, Hmap0⟩
  icases (mapFields_join db none).1 $$ [Hflds Hflds0] with ⟨Hd, H0, H1⟩
  · iframe
  dsimp only [mapSlice, mapPtr0, mapPtr1]
  (try wp_auto)
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h4096 : sint.Z (W64 4096) = 4096 := rfl
  wp_apply wp_pageAt
  · ipureintro; refine ⟨Hbd.1, by decide, ?_⟩; show sint.Z (W64 0) < sint.Z sz; omega
  wp_apply wp_meta
  · ipureintro; simp only [Loc.add, h0]; omega
  (try wp_auto)
  wp_apply wp_pageAt
  · ipureintro; refine ⟨Hbd.1, by decide, ?_⟩; show sint.Z (W64 4096) < sint.Z sz; omega
  wp_apply wp_meta
  · ipureintro; simp only [Loc.add, h4096]; omega
  (try wp_auto)
  rw [h0, h4096, loc_add_0, loc_add_assoc]
  have hszeq : W64 (sz.toNat : Int) = sz := by word
  icases (mapFields_join db (some (base, sz.toNat, γm))).2 $$ [Hd H0 H1] with ⟨Hflds, Hflds0⟩
  · dsimp only [mapSlice, mapPtr0, mapPtr1]; rw [hszeq]; iframe
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0 Htok2 Hf2 Hfd2]
  · iframe #; inext; iexists (some (base, sz.toNat, γm)); iframe; unfold mapRest; dsimp only; iframe; iframe #; ipureintro; exact Hbd.1
  (try wp_auto)
  iapply HΦ
  iexists (some (base, sz.toNat, γm)), { m with maps := <[base := sz.toNat]> (∅ : GMap Loc Nat) }
  iframe
  isplitr [Htok Hwc]
  · simp only [mapLen]
    rw [hszeq]
    iframe
    ipureintro
    exact ⟨h2, hsz, fun _ => ⟨hmp, hcc1 _, trivial, hfd0, h16, hsz30,
      by have := Hsz2.2.2.2.2 (by omega); omega⟩⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  ileft
  isplitr
  · ipureintro; trivial
  iexists base, sz.toNat, γm
  iframe
  iframe #
  ipureintro
  refine ⟨rfl, rfl, by omega, by omega, Hbd.1, by omega⟩

end proof

end bboltfs
end EtcdGrove
end Perennial
