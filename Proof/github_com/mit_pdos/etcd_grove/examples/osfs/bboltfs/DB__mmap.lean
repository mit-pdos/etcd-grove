/- Lean-first (no Rocq counterpart). The proof of `db.mmap(minsz)`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__munmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.mmapSize
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.pageAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Page__meta
public import Spec.os.File__Fd
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Madvise
public import Spec.golang_org.x.sys.unix.Munmap
public import Perennial.Proof.sync.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.MapInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmapLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

theorem DB.mmap.wp_proof (wp_munmap : DB.munmap.spec (GF := GF) (hG := hG))
    (wp_mmapSize : mmapSize.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Mmap : golang_org.x.sys.unix.Mmap.spec (GF := GF) (hG := hG))
    (wp_Madvise : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG))
    (wp_Munmap : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_meta : Page.«meta».spec (GF := GF) (hG := hG)) :
    DB.mmap.spec (GF := GF) (hG := hG) := by
  intro γ db f fd p minsz mp fl hwm st m Hfl Hmin0 Hmin Hsz
  wp_start as ⟨#Hpkg, #Hos, #Hfile, #Hguard, Hcur, Hmap, Hout, Hflds, Hw, Hpre⟩
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
  unfold writerFile
  icases Hw with ⟨%mxc, %tail, %fsz, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail, %Hw⟩
  have hfsz : fsz = m.size := (Hw.2.2.2.2 Hfl).2.2.1
  have hsz30 : m.size ≤ 2 ^ 30 := (Hw.2.2.2.2 Hfl).2.2.2.2.2.1
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
  ihave Hp := mmap_prep γ f fd p mp fl hwm m st Hw.1 Hw.2.1 $$ [Hcur Hout Hm Hpre HR]
  · iframe; iframe #
  imod Hp with ⟨Hcur, Hout, Hx, Ho, Hps, Hmr, Hrest, %Hpos⟩
  icases (mapFields_join db st).1 $$ [Hflds Hflds0] with ⟨Hd, H0, H1⟩
  · iframe
  wp_apply wp_munmap db (DFrac.own 1) (mapSlice st) (W64 (mapLen st)) (mapPtr0 st) (mapPtr1 st) γ.ino m (fun _ => rfl)
    $$ [Hd Hdsz H0 H1 Hmr] as %err ⟨Hd, Hdsz, H0, H1, Hun⟩
  · iframe
  rw [mapSlice_ite st Hpos (fun st => W64 (mapLen st)) (W64 0) rfl,
    mapSlice_ite st Hpos mapPtr0 null rfl, mapSlice_ite st Hpos mapPtr1 null rfl]
  ihave Hm := mmap_unmapped γ.ino m st err $$ [Hun Hrest]
  · iframe
  icases Hm with ⟨%m1, Hm, %Hm1⟩
  imod ghostVar_update_halves none γ.map st st $$ Hmap Hmap0 with ⟨Hmap, Hmap0⟩
  icases (mapFields_join db none).2 $$ [Hd H0 H1] with ⟨Hflds, Hflds0⟩
  · iframe
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    iapply HΦ
    iexists none, m1
    iframe
    rw [Hm1.1]
    iframe
    isplitr
    · ipureintro
      exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun hfl => ⟨(Hw.2.2.2.2 hfl).1, ⟨(Hw.2.2.2.2 hfl).2.1.1, by (try simp only); rw [Hm1.2.1.1, Hm1.2.1.2]; exact (Hw.2.2.2.2 hfl).2.1.2⟩,
        (Hw.2.2.2.2 hfl).2.2.1, (Hw.2.2.2.2 hfl).2.2.2.1, (Hw.2.2.2.2 hfl).2.2.2.2.1,
        (Hw.2.2.2.2 hfl).2.2.2.2.2.1, by simp only [mapLen]; omega⟩⟩
    isplitr
    · ipureintro; exact ⟨rfl, trivial⟩
    iright
    iframe
    ipureintro; simp
  | nil =>
  have Hmaps1 := Hm1.2.2 rfl
  (try wp_auto)
  wp_apply wp_Fd f fd p _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  have Hsz0 : 0 < (sz).toInt := by simp only [sint.Z] at Hsz2; omega
  wp_apply wp_Mmap fd (W64 0) sz _ _ _ ⟨γ.ino, true, true, none, some true⟩ m1 rfl rfl Hsz0 (by decide) (by left; decide)
    $$ [Hfd Hm] as %sl %e ⟨Hfd, Hres⟩
  · iframe; iframe #
  icases Hres with (⟨%base, %Hok, Hm, %bs, %Hbs, Hcells⟩ | ⟨%Herr, Hm⟩)
  rotate_left
  · obtain ⟨He, rfl⟩ := Herr
    unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    iapply HΦ
    iexists none, m1
    iframe
    rw [Hm1.1]
    iframe
    isplitr
    · ipureintro
      exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun hfl => ⟨(Hw.2.2.2.2 hfl).1, ⟨(Hw.2.2.2.2 hfl).2.1.1, by (try simp only); rw [Hm1.2.1.1, Hm1.2.1.2]; exact (Hw.2.2.2.2 hfl).2.1.2⟩,
        (Hw.2.2.2.2 hfl).2.2.1, (Hw.2.2.2.2 hfl).2.2.2.1, (Hw.2.2.2.2 hfl).2.2.2.2.1,
        (Hw.2.2.2.2 hfl).2.2.2.2.2.1, by simp only [mapLen]; omega⟩⟩
    isplitr
    · ipureintro; exact ⟨rfl, trivial⟩
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
    wp_apply wp_Munmap base sz γ.ino { m1 with maps := <[base := sz.toNat]> m1.maps } _ Hsz0
      (GMap.lookup_insert _ _ _) $$ [Hm Hcells] as %e3 Hm3
    · iframe; iframe #
    ihave Hm : ∃ m2 : OsMeta, osMeta (GF := GF) γ.ino (DFrac.own 1) m2 ∗
        ⌜m2.size = m.size ∧ m2.dhi = m.dhi ∧ m2.dlo = m.dlo⌝ $$ [Hm3]
    · icases Hm3 with (⟨-, Hm⟩ | ⟨-, (Hm | ⟨Hm, -⟩)⟩) <;>
        (iexists _; iframe; ipureintro; exact ⟨Hm1.1, Hm1.2.1.1, Hm1.2.1.2⟩)
    icases Hm with ⟨%m2, Hm, %Hm2⟩
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlocked Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    iapply HΦ
    iexists none, m2
    iframe
    rw [Hm2.1]
    iframe
    isplitr
    · ipureintro
      exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun hfl => ⟨(Hw.2.2.2.2 hfl).1, ⟨(Hw.2.2.2.2 hfl).2.1.1, by (try simp only); rw [Hm2.2.1, Hm2.2.2]; exact (Hw.2.2.2.2 hfl).2.1.2⟩,
        (Hw.2.2.2.2 hfl).2.2.1, (Hw.2.2.2.2 hfl).2.2.2.1, (Hw.2.2.2.2 hfl).2.2.2.2.1,
        (Hw.2.2.2.2 hfl).2.2.2.2.2.1, by simp only [mapLen]; omega⟩⟩
    isplitr
    · ipureintro; exact ⟨rfl, trivial⟩
    iright
    iframe
    ipureintro; exact ⟨errnoErr_ne_nil e2 he2, rfl⟩
  | false =>
  -- the new mapping: its cells against the committed pages and the meta windows
  have hlen : (sz.toNat : Int) = sint.Z sz := by have := Hsz2.2.1; word
  ihave %Hbd := cellsR_bounds base sz.toNat _ (by omega) $$ Hcells
  have hl : 4096 * hwm ≤ sz.toNat := by omega
  icases mapCells_scatter base hwm sz.toNat Hw.1 hl _ $$ Hcells with ⟨Hwc, Hc0, Hc1, Hpc⟩
  have hb : ({ m1 with maps := <[base := sz.toNat]> m1.maps } : OsMeta).maps !! base = some sz.toNat :=
    GMap.lookup_insert _ _ _
  rw [show 8192 = 4096 * 2 by rfl]
  iapply pages_agree _ rfl γ.ino _ _ base sz.toNat hb (by simp) _ (hwm - 2) 2 _ (by omega)
    $$ Hos Hm Hps Hpc
  iintro Hm Hps
  iapply window_agree _ rfl γ.ino _ _ base sz.toNat hb (by simp) _ _ mxc 16 64 _ (by omega) (by omega)
    $$ Hos Hm Hmx Hc0
  iintro Hm Hmx Hc0
  iapply window_agree _ rfl γ.ino _ _ base sz.toNat hb (by simp) _ _ mxc 4112 64 _ (by omega) (by omega)
    $$ Hos Hm Hmx Hc1
  iintro Hm Hmx Hc1
  -- the new mapping's invariant
  have hmxc : mxc.length = 8192 := Hw.2.2.1
  have hw0 : (((mxc.map Prod.fst).drop 16).take 64).length = 64 := by
    rw [List.length_take, List.length_drop, List.length_map, hmxc]; rfl
  have hw1 : (((mxc.map Prod.fst).drop 4112).take 64).length = 64 := by
    rw [List.length_take, List.length_drop, List.length_map, hmxc]; rfl
  iunfold writerExtra at Hx
  icases Hx with ⟨Hcur2, Hf2, Hfd2⟩
  ihave Hc : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.mapCells γ γ.ino base sz.toNat
      $$ [Hcur2 Hps Ho Hc0 Hc1]
  · iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.mapCells
    iexists mp, fl, hwm
    iframe Hcur2 Hps
    isplitr
    · ipureintro; exact hl
    iright
    iframe Ho
    iexists (((mxc.map Prod.fst).drop 16).take 64 ++ ((mxc.map Prod.fst).drop 4112).take 64)
    rw [List.take_left' hw0, List.drop_left' hw0]
    iframe
    ipureintro
    refine ⟨by simp only [List.length_append, hw0, hw1], fun hfl => ?_⟩
    rw [(Hw.2.2.2.2 hfl).1]
  ihave Hinv := mapInv_alloc γ γ.ino base sz.toNat (by have := Hsz2.2.1; word) $$ Hc
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
  iexists (some (base, sz.toNat, γm)), { m1 with maps := <[base := sz.toNat]> m1.maps }
  iframe
  simp only [mapLen]
  rw [hszeq, Hm1.1]
  iframe
  isplitr
  · ipureintro
    exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, Hw.2.2.2.1, fun hfl => ⟨(Hw.2.2.2.2 hfl).1, ⟨(Hw.2.2.2.2 hfl).2.1.1, by (try simp only); rw [Hm1.2.1.1, Hm1.2.1.2]; exact (Hw.2.2.2.2 hfl).2.1.2⟩,
      (Hw.2.2.2.2 hfl).2.2.1, (Hw.2.2.2.2 hfl).2.2.2.1, (Hw.2.2.2.2 hfl).2.2.2.2.1,
      (Hw.2.2.2.2 hfl).2.2.2.2.2.1, by have := Hsz2.2.2.2.2 (by omega); omega⟩⟩
  isplitr
  · ipureintro; exact ⟨rfl, trivial⟩
  ileft
  isplitr
  · ipureintro; trivial
  iexists base, sz.toNat, γm
  iframe
  iframe #
  ipureintro
  refine ⟨rfl, ?_, by omega, by omega, Hbd.1, by omega⟩
  simp only [Hmaps1]; rfl

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
