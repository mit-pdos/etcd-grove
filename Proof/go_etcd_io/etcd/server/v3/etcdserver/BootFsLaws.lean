/-
**`bootstrap`'s file-system laws over the WAL's sealed slot** (claim #34, 2026-11-23;
`BootParts.lean`'s header). `wal.bootRes` is sealed (`WalApi.lean`); the laws open it through its
API law `wal.bootRes_iff` (no `import all` of the slot's module): `bootFs.touchData.law` from
`TouchDirAll.specExisting` (at every file-extension instance: the slot's data area names its own);
`bootFs.walExist.law` from `wal.Exist.spec` at the WAL area's instances (2026-11-23).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllExisting
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.Exist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`bootFs.touchData.law`** from `TouchDirAll.specExisting` at every file-extension instance: the
data area's directory is a root, its spine, its root's call permission and its whole claim held, so
`TouchDirAll` runs on it with the claim on `.touch` (absent) split off; on success `.touch` is absent
again and the claim, merged back, names no entry: the start again. -/
theorem bootFs.touchData_law_holds
    (hT : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt],
      fileutil.TouchDirAll.specExisting (GF := GF) (hG := hG)) :
    bootFs.touchData.law (GF := GF) := by
  intro cfg lg
  iintro %Φ ⟨#Hpkg, #Hlg, Hb⟩ HΦ
  icases (wal.bootRes_iff cfg).1 $$ Hb with ⟨Hdd, %hw, Hma⟩
  iunfold memberAreasFresh at Hma
  icases Hma with ⟨Hw, Hda⟩
  iunfold dataAreaFresh at Hda
  icases Hda with ⟨%S, %ok, %has, %R, %j, %h, %hp, #Hos, #Hsh, #Hab, Hp, Hperm, Hn⟩
  obtain ⟨hcl, hlen, hemp⟩ := hp
  imod Fs.osNames_split R j (.except []) [go!".touch"] h CoPset.subseteq_top $$ Hsh Hn with ⟨Ht, Hrest⟩
  rw [show (Fs.NameSet.except []).inter [go!".touch"] = .only [go!".touch"] by simp [Fs.NameSet.inter],
    show (Fs.NameSet.except []).diff [go!".touch"] = .except [go!".touch"] by simp [Fs.NameSet.diff]]
  have hTn : (h.restrict j (.only [go!".touch"])).cur !! go!".touch" = none := by
    simp only [Fs.NamesH.restrict]
    rw [Fs.restrictN_lookup _ _ _ (by simp [Fs.NameSet.Mem]), hemp]
  iapply wp_fupd
  wp_apply hT lg R j cfg.DataDir' (DFrac.own 1) 1 _ (by omega) hTn $$ [Hp Hperm Ht]
  · iframe; iframe #
  iintro %err ⟨#Hfe, Hp, Hperm, %hT', HT, Hd, %hTn'⟩
  cases err with
  | ok e =>
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; intro hc; cases hc
    iapply fmtErrorOkOrNil_ne _ (by intro hc; cases hc) $$ Hfe
  | nil =>
    have hTn' := hTn' rfl
    iclear Hd
    imod Fs.osNames_merge R j (.only [go!".touch"]) (.except [go!".touch"]) (.except []) hT' _
      (by intro b; simp only [Fs.NameSet.Mem]; by_cases hb : b = go!".touch" <;> simp [hb])
      CoPset.subseteq_top $$ Hsh HT Hrest with ⟨%hM, HM, %hMf⟩
    have hMc := fun c => merged_cur hM hT' _ j go!".touch" c hMf.1 hMf.2.1
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iapply (wal.bootRes_iff cfg).2
    iframe Hdd
    isplitr
    · ipureintro; exact hw
    iunfold memberAreasFresh
    iframe Hw
    iunfold dataAreaFresh
    iexists S, ok, has, R, j, hM
    iframe Hos Hsh Hab Hp Hperm HM
    ipureintro
    refine ⟨hcl, hlen, fun c => ?_⟩
    rw [hMc c]
    split
    · subst_vars; exact hTn'
    · simp only [Fs.NamesH.restrict]
      next hc =>
      rw [Fs.restrictN_lookup _ _ _ (by simp [Fs.NameSet.Mem, hc]), hemp]

/-- **An update over the WAL directory `dir`, from `dir`'s own claim of no WAL** (`walAbsent`),
committed with the state unchanged: `wal.Exist`'s update on the fresh area. -/
theorem bootFs.walAbsent_au [W : WalFs.WalGS GF] (dir : GoString) :
    WalFs.walAbsent (W := W) dir ⊢
      AU <{ ∃∃ o : Option WalDur, WalFs.walDirIs (W := W) dir o }> @ WalFs.walAuMask, ∅
        <{ WalFs.walDirIs (W := W) dir o, COMM ⌜o = none⌝ ∗ WalFs.walAbsent (W := W) dir }> := by
  iintro Ha
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask from Std.LawfulSet.empty_subset)
  iintro Hclose
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists none
  iunfold WalFs.walAbsent at Ha
  iframe Ha
  isplit
  · iintro Hd
    imod Hclose with -
    imodintro
    iunfold WalFs.walAbsent
    iexact Hd
  · iintro Hd
    imod Hclose with -
    imodintro
    isplitr
    · ipureintro; rfl
    iunfold WalFs.walAbsent
    iexact Hd

/-- **`bootFs.walExist.law`** from `wal.Exist.spec` at the WAL area's file-extension instances: the
area holds no WAL (`walAbsent`, committed unchanged by `bootFs.walAbsent_au`), and the file system does
not fail on the WAL directory (`FsNoErrAt`: the area's I/O set covers every inode, `a.cov`, and the
directory by path, with its no-I/O-error and no-lock-error premises, `a.sat`/`a.satL`; the directory
fits, `a.fits`), so `Exist` answers `false` (`wal.Exist.spec`'s `o = none` arm), the area as it was. -/
theorem bootFs.walExist_law_holds
    (hE : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [WalFs.WalGS GF],
      wal.Exist.spec (GF := GF) walCodec walSrvMr) :
    bootFs.walExist.law (GF := GF) := by
  intro cfg
  iintro %Φ ⟨#Hpkg, Hw⟩ HΦ
  iunfold bootFs.walPart at Hw
  icases Hw with ⟨%hdd, Ha⟩
  iunfold walAreaFresh at Ha
  icases Ha with ⟨%a, %ha, #Hok, Hdur, Hp, Hres, Hperm, Hu, Habs⟩
  obtain ⟨hdir, hin, hcl, hpath⟩ := ha
  have hne : @Fs.FsNoErrAt a.ext a.dir :=
    ⟨⟨a.Sio, a.cov, a.sat, a.satL, fun p hp => hp ▸ hpath⟩,
      ⟨by have := a.fits.1; omega, a.fits.2⟩⟩
  have hnm : NameOk go!"wal" := by unfold NameOk; decide
  rw [hdd, ← hdir]
  ihave Hau := bootFs.walAbsent_au (W := a.W) a.dir $$ Habs
  wp_apply (@hE a.ext a.semOk a.has a.W a.R a.jr a.r a.dir go!"wal" 1
      (fun o => iprop(⌜o = none⌝ ∗ WalFs.walAbsent (W := a.W) a.dir)) hin hnm)
    $$ [Hp Hres Hperm Hu Hau] as %b ⟨Hp, Hres, Hperm, Hu, %o, ⟨%ho, Habs⟩, -, %hf⟩
  · iframe; iframe #
  subst ho
  have hb : b = false := hf rfl hne
  subst hb
  iapply HΦ
  iunfold bootFs.walPart
  isplitr
  · ipureintro; exact hdd
  iunfold walAreaFresh
  iexists a
  isplitr
  · ipureintro; exact ⟨hdir, hin, hcl, hpath⟩
  iframe Hok Hdur Hp Hres Hperm Hu Habs

end laws

end EtcdGrove
end Perennial
