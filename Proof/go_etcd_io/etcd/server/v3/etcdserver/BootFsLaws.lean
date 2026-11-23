/-
**`bootstrap`'s file-system laws over the WAL's sealed slot** (claim #34, 2026-11-23;
`BootParts.lean`'s header). `wal.bootRes` is sealed (`WalApi.lean`), so the laws that open it are
proved here, in the package, with `import all` of the slot's module: `bootFs.touchData.law` from
`TouchDirAll.specExisting` (at every file-extension instance: the slot's data area names its own).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllExisting
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllLemmas
import all Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi

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
  iunfold wal.bootRes at Hb
  icases Hb with ⟨Hdd, %hw, Hma⟩
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
    iunfold wal.bootRes
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

end laws

end EtcdGrove
end Perennial
