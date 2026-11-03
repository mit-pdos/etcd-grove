/- Lean-first (no Rocq counterpart). The proof of `db.Close()`'s crash-aware spec: as
`DB__Close.lean`'s, over `isDBC` (`rwRC`, `metaRC`), with `DB.close.specCrash`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__CloseCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__closeCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Close

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

/-- What is left after unmapping a mapping: some state of the file. -/
theorem unmappedC_own (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat)
    (sl : GoSlice) (err : GoInterface) (hne : sl ≠ slice.nil) :
    unmappedResC (GF := GF) p γc m bs fa fb sl err ⊢ ∃ s : CState, csOwn (GF := GF) p γc s := by
  unfold unmappedResC
  iintro (%Hnil | ⟨%b, %l, %vf, %e, -, Hu⟩)
  · exact absurd Hnil.1 hne
  · icases Hu with (⟨-, Hm⟩ | ⟨-, (Hm | ⟨Hm, -⟩)⟩) <;> (iexists _; iexact Hm)

theorem DB.Close.wp_proof_crash (wp_close : DB.close.specCrash (GF := GF) (hG := hG)) :
    DB.Close.specCrash (GF := GF) (hG := hG) := by
  intro γ γc db t n
  wp_start as ⟨Hdb, Hown⟩
  iunfold isDBC at Hdb
  icases Hdb with ⟨⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hci, #Hrw, #Hmeta, #Hguard⟩, -, -⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, -⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p) $$ [$Hrw $Hsync]
    as ⟨Hl1, HW⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hl2, HM⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hl3, HR⟩
  (try wp_auto)
  iunfold metaRC at HM
  icases HM with ⟨%b, %mx, %hwm, %c, %T, Hfl, Hcur, Hcls2, Hauth, Hout, Hrest⟩
  iunfold dbOwner at Hown
  iunfold rwRC at HW
  icases HW with (⟨%mp1, %fl, %hwm1, %st, %m, %bs, Hcur1, Hmap1, Hout1, Hflds1, Hw, Hcls1, %Hok0, Hst⟩ |
    ⟨⟨%x, Hown2⟩, Hcls1, %st, Hmap1, Hflds1⟩)
  rotate_left
  · -- closed: three halves of `own`
    iexfalso
    cases b with
    | true =>
      icases Hrest with ⟨-, %x3, Hown3⟩
      iapply ghostVar_halves3 γ.own (t, n) x _; iframe
    | false =>
      icases Hrest with ⟨-, -, -, Hown3, -⟩
      iapply ghostVar_halves3 γ.own (t, n) x _; iframe
  icombine Hcls1 Hcls2 gives % ⟨_, Hc⟩
  cases Hc
  unfold mapR mapBody
  icases HR with ⟨%st0, Hmap0, Hflds0, Hrest0⟩
  icombine Hmap1 Hmap0 gives % ⟨_, Heq⟩
  subst Heq
  icombine Hcur Hcur1 gives % ⟨_, Heq⟩
  cases Heq
  iunfold writerFileC at Hw
  icases Hw with ⟨%fsz, Hfsz, Hdsz, Hf1, Hfd1, Hm, %Hw⟩
  imod ghostVar_update_halves true γ.cls false false $$ Hcls1 Hcls2 with ⟨Hcls1, Hcls2⟩
  rcases st with _ | ⟨base, len, γm⟩
  · -- no mapping: the handle failed
    icases Hst with ⟨#Hfailed, Hx⟩
    cases b with
    | false =>
      iexfalso
      icases Hrest with ⟨Hfa, -⟩
      iunfold dbFailed at Hfailed
      icases monoNatLbOwn_valid γ.fail 1 0 1 $$ Hfa Hfailed with %Hbad
      omega
    | true =>
    icases Hrest with ⟨Hfa, %t3, Hown3⟩
    icombine Hown Hown3 gives % ⟨_, Heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
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
        ⟨p, true, true⟩ p γc m bs 8192 (4096 * hwm) (fun _ => rfl) $$ [Hd Hdsz H0 H1 Hf Hfd]
      as %errc ⟨Hd, Hdsz, H0, H1, -, -, -⟩
    · iframe; iframe #; unfold mappingResC; ileft; ipureintro; rfl
    (try simp only [↓reduceIte])
    icases (mapFields_join db none).2 $$ [Hd H0 H1] with ⟨Hflds1, Hflds0⟩
    · iframe
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hl3 Hmap0 Hflds0]
    · iframe #; inext; iexists none; iframe; unfold mapRest; iempintro
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hcls2 Hauth Hout Hfa Hown3]
    · iunfold metaRC
      iexists true, mx, hwm, true, T
      iframe Hfl Hcur Hauth Hout Hcls2
      dsimp only; iframe Hfa; iexists t; iexact Hown3
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p)
      $$ [$Hrw $Hsync $Hl1 Hown Hcls1 Hmap1 Hflds1]
    · iunfold rwRC
      iright
      iframe
    (try wp_auto)
    iapply HΦ
    iexists p
    iframe #
    iexists _; iexact Hm
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
        (base +ₗ 4112) f DFrac.discard fd p ⟨p, true, true⟩ p γc m bs 8192 (4096 * hwm) (fun _ => rfl)
        $$ [Hd Hdsz H0 H1 Hf Hfd Hm Hcells]
      as %errc ⟨Hd, Hdsz, H0, H1, ⟨%err, Hun, %Herr⟩, -, -⟩
    · iframe; iframe #
      unfold mappingResC; iright; iexists base, W64 len, vf
      rw [hlen]; iframe; iframe #
      ipureintro
      refine ⟨rfl, Hbase, ?_, ?_, Hw.2.2.1⟩
      · rw [BitVec.toInt_eq_toNat_cond, hlen]; split <;> omega
      · rw [Hmaps]; simp
    ihave Hm := unmappedC_own p γc m bs 8192 (4096 * hwm) _ err hne $$ Hun
    icases Hm with ⟨%s, Hm⟩
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
      icases Hrest with ⟨Hfa, %t3, Hrest⟩
      icombine Hown Hrest gives % ⟨_, Heq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
      ihave #Hfailed := monoNatLbOwn_get γ.fail 1 1 $$ Hfa
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hcls2 Hauth Hout Hfa Hrest]
      · iunfold metaRC
        iexists true, mx, hwm, true, T
        iframe Hfl Hcur Hauth Hout Hcls2
        dsimp only
        iframe Hfa; iexists t; iexact Hrest
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p)
        $$ [$Hrw $Hsync $Hl1 Hown Hcls1 Hmap1 Hflds1]
      · iunfold rwRC
        iright
        iframe
      (try wp_auto)
      iapply HΦ
      iexists p
      iframe #
      iexists s; iexact Hm
    | false =>
      icases Hrest with ⟨Hfa, %Hok, Hlast, Hown3, %B, #HB, #Htx, %HT⟩
      obtain ⟨Hok, rfl, HTn⟩ := Hok
      icombine Hown Hown3 gives % ⟨_, Heq⟩
      cases Heq
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hcls2 Hauth Hout Hfa Hlast Hown3]
      · iunfold metaRC
        iexists false, mx, curPgid mx, true, T
        iframe Hfl Hcur Hauth Hout Hcls2
        dsimp only
        iframe Hfa
        isplitr
        · ipureintro; exact ⟨Hok, rfl, HTn⟩
        iframe Hlast Hown3
        iexists B; iframe #; ipureintro; exact HT
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p)
        $$ [$Hrw $Hsync $Hl1 Hown Hcls1 Hmap1 Hflds1]
      · iunfold rwRC
        iright
        iframe
      (try wp_auto)
      iapply HΦ
      iexists p
      iframe #
      iexists s; iexact Hm

end proof

end bboltfs
end EtcdGrove
end Perennial
