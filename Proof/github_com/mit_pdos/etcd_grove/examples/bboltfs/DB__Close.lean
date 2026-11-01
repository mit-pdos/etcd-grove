/- Lean-first (no Rocq counterpart). The proof of `db.Close()`: with the three locks, the
closed state is ruled out (three halves of `own`); with a mapping, its invariant is closed with
the whole of its token and every cell gathered for `close`'s `Munmap`; the closed flag is set
(`cls`), the meta pages' bytes leave `metalock`, and `rwlock` gets the committer's token. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Close
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__close
public import Perennial.Proof.sync.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.MapInv

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

theorem ownFile_join (f : Loc) (fd : w64) (p : GoString) :
    os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ⊢ os.ownFile (GF := GF) f fd p (DFrac.own 1) := by
  conv => rhs; rw [← Qp.half_add_half 1]
  exact ((ownFile_fractional f fd p).fractional _ _).2

theorem osFd_join (fd : w64) (d : OsFd) :
    osFd (GF := GF) fd (DFrac.own (1 : Qp).half) d ∗ osFd (GF := GF) fd (DFrac.own (1 : Qp).half) d ⊢
      osFd (GF := GF) fd (DFrac.own 1) d := by
  conv => rhs; rw [← Qp.half_add_half 1]
  exact ((osFd_fractional fd d).fractional _ _).2

theorem errnoErr_ne_nil' (e : w64) (h : e ≠ 0) : errnoErr e ≠ interface.nil := by
  unfold errnoErr; rw [if_neg h]; simp

/-- After `close`'s successful `Munmap` of the whole mapping: the file's `OsMeta`, of the same
size, with no mapping. -/
theorem close_unmapped (p : GoString) (m : OsMeta) (base : Loc) (len : Nat) (err : GoInterface)
    (hm : m.maps = {[base := len]}) (hb : 0 < base.addr) (herr : err = interface.nil) :
    unmappedRes (GF := GF) p m ⟨base, W64 len, W64 len⟩ err ⊢
      ∃ m', osMeta (GF := GF) p (DFrac.own 1) (some m') ∗
        ⌜m'.size = m.size ∧ m'.ok = m.ok ∧ m'.maps = ∅⌝ := by
  unfold unmappedRes
  iintro (%Hnil | ⟨%b, %l, %vf, %e, %Heq, Hu⟩)
  · exfalso
    have := congrArg GoSlice.ptr Hnil.1; simp [slice.nil] at this; subst this
    simp [null] at hb
  · obtain ⟨Hsl, rfl⟩ := Heq
    cases Hsl
    by_cases he : e = 0
    · icases Hu with (⟨-, Hm⟩ | ⟨%He, -⟩)
      · iexists _; iframe
        ipureintro; refine ⟨rfl, rfl, ?_⟩; simp only [hm]; exact GMap.delete_singleton _ _
      · exact absurd he He
    · exact absurd herr (errnoErr_ne_nil' e he)

theorem DB.Close.wp_proof (wp_close : DB.close.spec (GF := GF) (hG := hG)) :
    DB.Close.spec (GF := GF) (hG := hG) := by
  intro γ db t n
  wp_start as ⟨Hdb, Hown, -⟩
  iunfold isDB at Hdb
  icases Hdb with ⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hrw, #Hmeta, #Hguard⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, -⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"rwlock"] (rwR (GF := GF) γ db f fd p) $$ [$Hrw $Hsync]
    as ⟨Hl1, HW⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hl2, HM⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hl3, HR⟩
  (try wp_auto)
  iunfold metaR at HM
  icases HM with ⟨%b, %mp, %mx, %hwm, %mxc, %T, Hfl, Hcur, Hmb, %Hmx, Hauth, Hout, Hrest⟩
  iunfold dbOwner at Hown
  iunfold rwR at HW
  icases HW with (⟨%mp1, %fl, %hwm1, %st, %m, Hcur1, Hmap1, Hout1, Hflds1, Hw, Hcls1, %Hok0, Hst⟩ |
    ⟨⟨%x, Hown2⟩, Hcls1, %st, Hmap1, Hflds1⟩)
  rotate_left
  · -- closed: three halves of `own`
    iexfalso
    cases b with
    | true =>
      icases Hrest with ⟨-, %x3, Hown3⟩
      iapply ghostVar_halves3 γ.own (t, n) x x3; iframe
    | false =>
      icases Hrest with ⟨-, -, -, Hown3, -⟩
      iapply ghostVar_halves3 γ.own (t, n) x _; iframe
  icases Hmb with (⟨Hmb, Hcls2⟩ | Hcls2)
  rotate_left
  · icombine Hcls1 Hcls2 gives % ⟨_, Hbad⟩; cases Hbad
  unfold mapR mapBody
  icases HR with ⟨%st0, Hmap0, Hflds0, Hrest0⟩
  icombine Hmap1 Hmap0 gives % ⟨_, Heq⟩
  subst Heq
  icombine Hcur Hcur1 gives % ⟨_, Heq⟩
  cases Heq
  iunfold writerFile at Hw
  icases Hw with ⟨%mxw, %tail, %fsz, Hfsz, Hdsz, Hf1, Hfd1, Hm, Hmxw, Htail, %Hw⟩
  imod ghostVar_update_halves true γ.cls false false $$ Hcls1 Hcls2 with ⟨Hcls1, Hcls2⟩
  rcases st with _ | ⟨base, len, γm⟩
  · -- no mapping: the handle failed
    icases Hst with ⟨Hfailed, Hx⟩
    iunfold writerExtra at Hx
    icases Hx with ⟨Hcurx, Hf2, Hfd2⟩
    icases (mapFields_join db none).1 $$ [Hflds1 Hflds0] with ⟨Hd, H0, H1⟩
    · iframe
    ihave Hf := ownFile_join f fd p $$ [Hf1 Hf2]
    · iframe
    ihave Hfd := osFd_join fd _ $$ [Hfd1 Hfd2]
    · iframe
    dsimp only [mapSlice, mapPtr0, mapPtr1, mapLen]
    wp_apply wp_close db (DFrac.own 1) slice.nil (W64 0) null null f DFrac.discard fd p
        ⟨p, true, true⟩ p m (fun _ => rfl) $$ [Hd Hdsz H0 H1 Hf Hfd]
      as %errc ⟨Hd, Hdsz, H0, H1, -, -, -⟩
    · iframe; iframe #; unfold mappingRes; ileft; ipureintro; rfl
    (try simp only [↓reduceIte])
    icases (mapFields_join db none).2 $$ [Hd H0 H1] with ⟨Hflds1, Hflds0⟩
    · iframe
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hl3 Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hcls2 Hauth Hout Hrest]
    · iunfold metaR
      iexists b, mp, mx, hwm, mxc, T
      iframe Hfl Hcur Hauth Hout Hrest
      isplitl [Hcls2]
      · iright; iexact Hcls2
      · ipureintro; exact Hmx
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwR (GF := GF) γ db f fd p)
      $$ [$Hrw $Hsync $Hl1 Hown Hcls1 Hmap1 Hflds1]
    · iunfold rwR
      iright
      iframe
    (try wp_auto)
    iapply HΦ
    iexists p
    iframe #
    iright; iright; iexact Hfailed
  · -- a mapping: close its invariant and gather its cells
    icases Hst with ⟨%Hst, Htok1, -, Hwc⟩
    obtain ⟨Hmaps, Hlen, Hbase, Hlen41⟩ := Hst
    dsimp only [mapRest] at *
    icases Hrest0 with ⟨-, Htok0, #Hinv, Hf2, Hfd2⟩
    ihave Htok := (ghostVar_split_half γm 1 ()).2 $$ [Htok1 Htok0]
    · iframe
    imod mapInv_close γ p base len γm $$ [Htok] with Hc
    · iframe; iframe #
    icases Hc with >Hc
    iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.bboltfs.mapCells at Hc
    icases Hc with ⟨%mp2, %fl2, %hwm2, Hcur2, %Hl, Hpages, Hmo⟩
    icombine Hcur1 Hcur2 gives % ⟨_, Heq⟩
    cases Heq
    icases Hmo with (Hout2 | ⟨Hout2, %mc, Hc0, Hc1, %Hmc⟩)
    · icombine Hout1 Hout2 gives % ⟨_, Hbad⟩; cases Hbad
    icases pagesCells_split p base (hwm - 2) 2 $$ Hpages with ⟨Hps, Hpc⟩
    rw [show 4096 * 2 = 8192 by rfl]
    ihave Hcells := mapCells_gather base hwm len Hw.1 Hl mc Hmc.1 $$ [Hwc Hc0 Hc1 Hpc]
    · iframe
    iunfold cellsAny at Hcells
    icases Hcells with ⟨%vf, Hcells⟩
    icases (mapFields_join db (some (base, len, γm))).1 $$ [Hflds1 Hflds0] with ⟨Hd, H0, H1⟩
    · iframe
    ihave Hf := ownFile_join f fd p $$ [Hf1 Hf2]
    · iframe
    ihave Hfd := osFd_join fd _ $$ [Hfd1 Hfd2]
    · iframe
    dsimp only [mapSlice, mapPtr0, mapPtr1, mapLen]
    have h8 : 8192 ≤ len := by omega
    have hlen : (W64 (len : Int)).toNat = len := by
      have : len < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofInt]; omega
    have hne : (⟨base, W64 len, W64 len⟩ : GoSlice) ≠ slice.nil := by
      intro h; have := congrArg GoSlice.ptr h; simp [slice.nil] at this; subst this
      simp [null] at Hbase
    wp_apply wp_close db (DFrac.own 1) ⟨base, W64 len, W64 len⟩ (W64 len) (base +ₗ 16)
        (base +ₗ 4112) f DFrac.discard fd p ⟨p, true, true⟩ p m (fun _ => rfl)
        $$ [Hd Hdsz H0 H1 Hf Hfd Hm Hcells]
      as %errc ⟨Hd, Hdsz, H0, H1, ⟨%err, Hun, %Herr⟩, -, -⟩
    · iframe; iframe #
      unfold mappingRes; iright; iexists base, W64 len, vf
      rw [hlen]; iframe; iframe #
      ipureintro
      refine ⟨rfl, Hbase, ?_, ?_⟩
      · rw [BitVec.toInt_eq_toNat_cond, hlen]; split <;> omega
      · rw [Hmaps]; simp
    rw [if_neg hne, if_neg hne, if_neg hne]
    imod ghostVar_update_halves none γ.map _ _ $$ Hmap1 Hmap0 with ⟨Hmap1, Hmap0⟩
    icases (mapFields_join db none).2 $$ [Hd H0 H1] with ⟨Hflds1, Hflds0⟩
    · iframe
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hl3 Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe
    (try wp_auto)
    cases b with
    | true =>
      icases Hrest with ⟨Hfa, Hrest⟩
      ihave #Hfailed := monoNatLbOwn_get γ.fail 1 1 $$ Hfa
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hcls2 Hauth Hout Hfa Hrest]
      · iunfold metaR
        iexists true, mp, mx, hwm, mxc, T
        iframe Hfl Hcur Hauth Hout
        isplitl [Hcls2]
        · iright; iexact Hcls2
        isplitr
        · ipureintro; exact Hmx
        dsimp only
        iframe
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwR (GF := GF) γ db f fd p)
        $$ [$Hrw $Hsync $Hl1 Hown Hcls1 Hmap1 Hflds1]
      · iunfold rwR
        iright
        iframe
      (try wp_auto)
      iapply HΦ
      iexists p
      iframe #
      iright; iright
      unfold dbFailed
      iexact Hfailed
    | false =>
      icases Hrest with ⟨Hfa, %Hok, Hlast, Hown3, %B, #HB, #Htx, %HT⟩
      obtain ⟨rfl, Hok, rfl, HTn⟩ := Hok
      icombine Hown Hown3 gives % ⟨_, Heq⟩
      cases Heq
      ihave Hmx := osBytes_join p mxw mxc 0 (by rw [Hw.2.2.1, Hmx.1]) $$ [Hmxw Hmb]
      · iframe
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hcls2 Hauth Hout Hfa Hlast Hown3]
      · iunfold metaR
        iexists false, mx, mx, curPgid mx, mxc, T
        iframe Hfl Hcur Hauth Hout
        isplitl [Hcls2]
        · iright; iexact Hcls2
        isplitr
        · ipureintro; exact Hmx
        dsimp only
        iframe Hfa
        isplitr
        · ipureintro; exact ⟨rfl, Hok, rfl, HTn⟩
        iframe Hlast Hown3
        iexists B; iframe #; ipureintro; exact HT
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwR (GF := GF) γ db f fd p)
        $$ [$Hrw $Hsync $Hl1 Hown Hcls1 Hmap1 Hflds1]
      · iunfold rwR
        iright
        iframe
      (try wp_auto)
      iapply HΦ
      iexists p
      iframe #
      by_cases herrc : errc = interface.nil
      · ileft
        isplitr
        · ipureintro; exact herrc
        ihave Hm := close_unmapped p m base len err Hmaps Hbase (Herr herrc) $$ Hun
        icases Hm with ⟨%m', Hm, %Hm'⟩
        unfold dbClosed
        iexists m', mx, mxw, tail, B
        iframe; iframe #
        ipureintro
        refine ⟨(Hw.2.2.2.2 rfl).1, (Hw.2.2.2.2 rfl).2.1, Hok, rfl, by omega, by omega, ?_, Hm'.2.2,
          by have := (Hw.2.2.2.2 rfl).2.2.2.2.1; omega, by have := (Hw.2.2.2.2 rfl).2.2.2.2.2.1; omega⟩
        rw [Hm'.2.1]; exact Hok0 rfl
      · iright; ileft; ipureintro; exact herrc

end proof

end bboltfs
end EtcdGrove
end Perennial
