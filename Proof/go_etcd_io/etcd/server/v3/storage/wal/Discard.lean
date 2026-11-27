/-
`wal.Discard` over `fsExt`: the proof (P6b, mit-pdos/etcd-grove#50; spec
`Spec/go_etcd_io/etcd/server/v3/storage/wal/Discard.lean`; `notes/wal-p6-handoff.md`, sessions 15-23).

`Discard(lg, dir)` (`unsaved.go:93-116`): `dir := filepath.Clean(dirpath)`, `RemoveAll(dir.tmp)`,
`Rename(dir, dir.tmp)`, `syncDir(filepath.Dir(dir))`, a log line. The ghost steps, in program order:
* the area opened (`walAreaRes_open`), `dir.tmp` dropped off the area claim by a fresh WAL name `b`
  (`walInv_drop`) with the claims under it (`area_takeTmp`): a `tmpAny` for `RemoveAll`;
* `RemoveAll`'s error: nothing done, `dir.tmp` merged back (`discard_abortTmp`, as `Create`'s
  `create_abortTmp` with the merge's witness `b`: `nm` is registered, not in the area claim);
* **U'** (`walInv_discardU`), the cleanup's pin (`walInv_pinClean`), **R** (`discAU`, `os.Rename.specDirSnc`:
  `AU₁` at the rename's commit; the rename cannot fail under `FsNoErrOn`);
* the parent's fsync (`syncDir`): its error leaves `AU₂` with the caller; its `nil` gives `osCommitLb` past
  the rename, **S** (`walInv_discardS`: `AU₂`) and the area back (`walInv_discardBack`).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Discard
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.syncDir
public import Spec.os.RenameS
public import Spec.path.filepath.Clean
public import Spec.path.filepath.Dir
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Info
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateTmp
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateAbort
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CleanupAu
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardR
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DiscardBack

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section pure
variable [GooseExts]

open Classical in
/-- **The entry just logged is the claim's last writer of a name it writes.** -/
theorem lastWrite_log (h : NamesH) (j : Ino) (b : GoString) (x : Nat) (e : LogEntry) (c : Ents)
    (hw : e.op.Writes j b) : LastWrite (h.log x e c) j b x e c := by
  have h2 : decide (e.op.Writes j b) = true := decide_eq_true hw
  unfold LastWrite NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil, h2, ite_true]
  simp

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- **`Discard`'s abort when `RemoveAll(dir.tmp)` fails** (`create_abortTmp` with the merge's witness `w`, a
WAL name of the area claim: the discarded `nm` is registered, not in it): `dir.tmp`'s claim (whatever it holds
now) merged back into the area claim and `walAreaRes` rebuilt. -/
theorem discard_abortTmp (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (nm w : GoString) (hT : NamesH)
    (Wn : List GoString) (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) (hw : walNameOk w) (hNw : N.Mem w)
    (hself : h.restrict jr N = h) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗ osSharedInv (L := hG.goose_localGS) R -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ WalFs.walUnlockedTok (W := W) -∗
      osNames (L := hG.goose_localGS) jr (N.diff [tmpName nm]) (DFrac.own (1 : Qp).half)
        (h.restrict jr (N.diff [tmpName nm])) -∗
      tmpAny jr (tmpName nm) hT -∗
      areaCls (L := hG.goose_localGS) (cl.filter (fun c => decide (c.1 ≠ tmpName nm))) -∗
      walSplitFrag (W := W) Wn ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ WalFs.walUnlockedTok (W := W) ∗
        walAreaRes (L := hG.goose_localGS) jr := by
  iintro #Hinv #Hsi Hnc Hu HN Ht Hcl Hsf
  unfold tmpAny
  icases Ht with ⟨HT, Hs⟩
  have hwt : w ≠ tmpName nm := fun e => tmpName_not_walName nm (e ▸ hw)
  have hNw' : (N.diff [tmpName nm]).Mem w :=
    (NameSet.mem_diff _ _ _).2 ⟨hNw, by simpa using hwt⟩
  imod walInv_mergeIn C Mr R jr r (N.diff [tmpName nm]) (.only [tmpName nm]) N
    (h.restrict jr (N.diff [tmpName nm])) hT w (tmpName nm) (WalFs.walUnlockedTok (W := W))
    walUnlockedTok_exclX ⊤ CoPset.subseteq_top walN_osShN_top hw hNw' (by simp [NameSet.Mem])
    (fun b hb => by simp only [NameSet.Mem, List.mem_singleton] at hb; subst hb; exact tmpName_not_walName nm)
    (fun b => by
      rw [NameSet.mem_diff]
      by_cases hb : b = tmpName nm
      · subst hb
        constructor
        · intro _; right; simp [NameSet.Mem]
        · intro _; exact areaOk_tmp hok hnm
      · simp [NameSet.Mem, hb])
    $$ Hinv Hsi Hnc Hu HN HT with ⟨Hnc, Hu, %h', HN, %hm⟩
  imod osNames_self R jr N _ h' CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself'⟩
  have htc : h'.cur !! tmpName nm = hT.cur !! tmpName nm := by
    have e := cur_of_part hm.2.1 (by simp [NameSet.Mem] : (NameSet.only [tmpName nm]).Mem (tmpName nm))
    exact e
  imodintro
  iframe Hnc Hu
  iapply area_give N N h h' cl jr (tmpName nm) Wn hok (fun _ => Iff.rfl) (tmpName_not_walName nm)
    (fun b hb _ _ => abort_cur N h h' jr (tmpName nm) hself hself' hm.1 b hb)
  iframe HN Hcl Hsf
  rw [htc]
  iexact Hs

-- (the proof term's instantiation at the end of the declaration exceeds the default budget)
set_option maxHeartbeats 1000000 in
theorem wal.Discard.wp_proof (Mr : WalMarshal)
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_RmSub : os.RemoveAll.specSubS (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.specDirSnc (GF := GF) (hG := hG))
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_syncDir : go_etcd_io.etcd.server.v3.storage.wal.syncDir.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    wal.Discard.spec (GF := GF) Mr := by
  classical
  intro lg R jr r dir nm qp ic Q₁ Q₂ hin hnmO hdl _hr hnoerr
  wp_start as ⟨#Hzap, #Hok, #Hdd, Hp, Hres, Hperm, Hu, Hau1, Hau2⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨#Hbin, #Herrs, #Hfmt, -, -, #Hsync, #Hproto, #Hfu, -, -, -, -, #Hos, #Htime, -, #Hfp, #Hzp, -, -, -, -, -, -, -⟩
  ihave %hrc := osPathS_cleanAbs' R r _ jr $$ Hp
  have hdc := dir_child hin
  subst hdc
  have hnm := hin.1
  have htn : ¬ walNameOk (tmpName nm) := tmpName_not_walName nm
  have hne : nm ≠ tmpName nm := (tmpName_ne nm).symm
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  wp_apply wp_Clean (child r nm) as %cr %hcr
  rw [clean_child hrc hnmO] at hcr
  subst hcr
  try wp_auto
  rw [tmp_path]
  -- the area opened; `nm.tmp` off the area claim, by a fresh WAL name `b` of it
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb, -, #Hab⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N0, %h0, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  obtain ⟨b, hb, hbW⟩ := exists_walName_notin Wn
  have hbN : N0.Mem b := (hok.1 b hb).resolve_right hbW
  have hNt : N0.Mem (tmpName nm) := areaOk_tmp hok hnm
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod osNames_self R jr N0 _ h0 CoPset.subseteq_top $$ Hsi HN with ⟨HN, %hself⟩
  imod walInv_drop walCodec Mr R jr r N0 h0 b (tmpName nm) ⊤ CoPset.subseteq_top walN_osShN_top hb hbN hNt
    (tmpName_walNameP nm) htn (tmpName_areaSlot hnm) $$ Hinv Hsi Hnc Hu HN
    with ⟨Hnc, Hu, HN, HT⟩
  iframe Hnc
  imodintro
  icases area_takeTmp N0 h0 cl nm Wn hok hnm $$ Hcl with ⟨Hts, Hcl⟩
  have hTt : (h0.restrict jr (N0.inter [tmpName nm])).cur !! tmpName nm = h0.cur !! tmpName nm := by
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ ((NameSet.mem_inter _ _ _).2 ⟨hNt, List.mem_singleton_self _⟩)]
  have hFt : FsNoErrAt (child r (tmpName nm)) :=
    ⟨hnoerr.1.mono (fun p hp => .inr (.inl (by rw [hp, tmp_path]))), by rw [← tmp_path]; exact hnoerr.2.1⟩
  have hFr : FsNoErrAt r :=
    ⟨hnoerr.1.mono (fun p hp => .inr (.inr hp)), pathFits_area hnoerr.2.2⟩
  ihave Ht : tmpAny jr (tmpName nm) (h0.restrict jr (N0.inter [tmpName nm])) $$ [HT Hts]
  · unfold tmpAny; rw [hTt]; iframe
  -- `RemoveAll(dir.tmp)`
  wp_apply wp_removeAllTmp wp_RmSub r (tmpName nm) R jr qp _ (tmpName_nameOk hnmO)
    $$ [Hp Ht Hperm] as %err ⟨Hp, Hperm, Ht, -⟩
  · iframe; iframe #
  cases err
  case ok ei =>
    -- `RemoveAll` failed: nothing done, `nm.tmp` merged back
    icases Ht with ⟨%hT1, Ht, -⟩
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod discard_abortTmp walCodec Mr R jr r N0 h0 cl nm b hT1 Wn hok hnm hb hbN hself
      $$ Hinv Hsi Hnc Hu HN Ht Hcl Hsf
      with ⟨Hnc, Hu, Hres⟩
    iframe Hnc
    imodintro
    try wp_auto
    iapply HΦ
    iframe Hp Hperm
    ileft
    iframe
    ipureintro; intro hc; cases hc
  all_goals (
    try wp_auto
    icases Ht with ⟨%hT1, Ht, %hT1n⟩
    have hT1a : hT1.cur !! tmpName nm = none := by
      exact hT1n rfl hFt hFr
    iunfold tmpAny at Ht
    icases Ht with ⟨Ht, -⟩
    -- U': the WAL's claim and `nm.tmp`'s merged into the discard claim, `nm` unregistered
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_discardU walCodec Mr R jr r (child r nm) nm (tmpName nm) Wn hT1 ic Q₁ hin htn
      $$ Hinv Hsi Hnc Hau1 Hu Hsf Ht
      with ⟨Hnc, Hau1, %hC, %J, Hu, Hnf, Hsf, HC, %hU⟩
    obtain ⟨hnmW, hCt, hJ⟩ := hU
    have hN1 : (NameSet.only [nm, tmpName nm]).Mem nm := by simp [NameSet.Mem]
    have hN2 : (NameSet.only [nm, tmpName nm]).Mem (tmpName nm) := by simp [NameSet.Mem]
    have ht0 : hC.cur !! tmpName nm = none := by
      rw [cur_of_part hCt (by simp [NameSet.Mem] : (NameSet.only [tmpName nm]).Mem (tmpName nm))]
      exact hT1a
    imod walInv_pinClean walCodec Mr R jr r (.only [nm, tmpName nm]) hC nm hnm hN1
      $$ Hinv Hsi Hnc Hu HC with ⟨Hnc, Hpin, HC⟩
    imod osNames_next R jr _ _ _ CoPset.subseteq_top $$ Hsi HC with ⟨HC, #HlbC⟩
    ihave HA := discAU walCodec Mr R jr r (child r nm) nm (tmpName nm) (.only [nm, tmpName nm]) hC J
      hC.next ic Q₁ hin hne hN1 hN2 hJ ht0 (Nat.le_refl _) htn (tmpName_areaSlot hnm) $$ Hinv [Hpin Hau1]
    · unfold discP; iframe
    iframe Hnc
    imodintro
    -- `Rename(dir, dir.tmp)`: R, `AU₁` committed
    try wp_auto
    wp_apply wp_Rename r nm (tmpName nm) jr J (.only [nm, tmpName nm]) R qp hC (1 : Qp).half
      (1 : Qp).half hC.next _ hnmO (tmpName_nameOk hnmO) hN1 hN2 hne hJ ht0 (Qp.half_add_half 1)
      $$ [Hp Hperm HC HA] as %err ⟨Hp, Hperm, %o, %ho, HQ, Hout⟩
    · iframe; iframe #
    cases err
    case ok ei =>
      -- the rename failed: impossible, the file system does not fail on `dir.tmp`
      exact absurd ⟨hnoerr.1.mono (fun p hp => .inr (.inl (by rw [hp, tmp_path]))), hnoerr.2.2,
        by rw [← tmp_path]; exact hnoerr.2.1⟩ (ho.2.2 (by intro hc; cases hc))
    obtain ⟨⟨x, s⟩, rfl⟩ := Option.isSome_iff_exists.1 (ho.1 rfl)
    unfold discQ
    icases HQ with ⟨Hu, HQ1, #Hkey⟩
    unfold renDirOut claimOut logOut osLogged
    icases Hout with ⟨⟨-, -, -, #Hlg⟩, HC⟩
    try wp_auto
    -- `syncDir(filepath.Dir(dir))`: the area's fsync
    wp_apply wp_Dir (child r nm) as %pd %hpd
    rw [dir_child_model hrc hnmO] at hpd
    subst pd
    wp_apply wp_syncDir r R jr (DFrac.own qp) 1 (x + 1) $$ [Hp Hperm] as %serr ⟨Hp, Hperm, Hs⟩
    · iframe; iframe #
    icases Hs with (%hserr | ⟨%hserr, #Hc⟩)
    · -- the fsync failed: `AU₁` committed, `AU₂` back
      cases serr
      case nil => exact absurd rfl hserr
      try wp_auto
      iapply HΦ
      iframe Hp Hperm
      iright
      iframe HQ1
      iright
      iframe Hau2
      ipureintro; exact hserr
    subst hserr
    -- S: `AU₂` committed, the WAL's directory claim to the program; the area back
    have hEs : (restrictN (NameSet.only [nm, tmpName nm])
        (<[tmpName nm := Node.dir J]> (GMap.delete nm hC.cur))) !! nm = none := by
      rw [restrictN_lookup _ _ _ hN1, GMap.lookup_insert_ne _ _ hne.symm]
      simp
    have hEt : (restrictN (NameSet.only [nm, tmpName nm])
        (<[tmpName nm := Node.dir J]> (GMap.delete nm hC.cur))) !! tmpName nm = some (.dir J) := by
      rw [restrictN_lookup _ _ _ hN2]; simp
    have hw : (renDirEnt jr nm (tmpName nm) J s).op.Writes jr nm := by
      left; simp [renDirEnt, MetaOp.slots]
    ihave %hR := osPathS_rootsOk R r _ jr $$ Hp
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod walInv_discardS walCodec Mr R jr r (child r nm) nm (.only [nm, tmpName nm]) _ ic J Q₂ x
      (renDirEnt jr nm (tmpName nm) J s) _ (x + 1) hin hN1
      (by intro e; have := congrArg (fun M => NameSet.Mem M (tmpName nm)) e; simp [NameSet.Mem, hne.symm] at this)
      hR hEs (lastWrite_log _ _ _ _ _ _ hw) (Nat.lt_succ_self x) hEs
      $$ Hinv Hsi Hnc Hau2 Hu Hnf HC Hc Hkey
      with ⟨Hnc, HQ2, Hu, HC, %hj, Hj, Hr, Hh, %hf, -⟩
    imod walInv_discardBack walCodec Mr R jr r N0 h0 cl Wn nm b _ hj J hok hnm hnmW hb hbW hbN hEt hf
      $$ Hinv Hsi Hnc Hu Hsf HN HC Hj Hr Hh Hcl
      with ⟨Hnc, Hu, Hres⟩
    iframe Hnc
    imodintro
    -- `lg.Info(...)`, `nil`
    try wp_auto
    wp_apply wp_String as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Info lg _ _ $$ []
    · iframe #
    try wp_auto
    iapply HΦ
    iframe Hp Hperm
    iright
    iframe HQ1
    ileft
    iframe
    ipureintro; rfl)

end proof

end EtcdGrove
end Perennial

end
