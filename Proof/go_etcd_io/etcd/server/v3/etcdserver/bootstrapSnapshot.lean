/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapSnapshot.lean` (claim #34, stage 4,
2026-11-23), over `TouchDirAll`, `RemoveMatchFile` (of the new, empty directory), `cfg.SnapDir()`,
`snap.New` and zap's logging, at the program's file-extension instances (`backend.theFs`, which
`bootFs.dirFresh`'s `backend.onFs` names). The snapshot directory's names are carved by
`bootSnap.snapDir_carve` (`BootSnapCarve.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapSnapshot
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__SnapDir
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.New
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootSnapCarve

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`err != nil` on any error** (`RemoveMatchFile`'s `err`): `i == nil` on an interface steps to
`decide (i = nil)` for every `i`. Derived from Perennial's `go_eq_interface`, whose rule matches on
both sides, so it does not step on a variable `i` (`CoreComparisonSemantics` has this rule for
functions, not for interfaces: `notes/perennial-changes.md`). -/
instance (priority := high) go_eq_interface_nil_r (elems : List go.InterfaceElem) (i : GoInterface) :
    ⟦GoOp GoEquals (go.InterfaceType elems), (#i, #interface.nil)⟧ ⤳[under]
      #(decide (i = interface.nil)) := by
  have h := go.go_eq_interface (elems := elems) i interface.nil
  cases i <;> simpa using h

theorem bootstrapSnapshot.wp_proof
    (hSnapDir : config.ServerConfig.SnapDir.spec (GF := GF) (hG := hG))
    (hTouch : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt],
      fileutil.TouchDirAll.spec (GF := GF) (hG := hG))
    (hRemove : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt],
      go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile.spec (GF := GF) (hG := hG))
    (hNew : snap.New.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hError : zap.Logger.Error.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG)) :
    bootstrapSnapshot.spec (GF := GF) (hG := hG) := by
  intro cfg Hfits
  rcases hfs : backend.theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [bootFs.dirFresh, backend.onFs_none hfs]
    wp_start as ⟨-, H⟩
    iexfalso; iexact H
  simp only [bootFs.dirFresh, snapFreeAll, snapFree, backend.fileFree, backend.onFs_some hfs]
  wp_start as ⟨#Hzlg, Hdf⟩
  icases Hdf with ⟨%R, %j, %h, ⟨%hclean, -, %hcur⟩, #Hinv, #Hsh, #Hab, Hp, Hc, Hn⟩
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  ihave #Hfpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
  · iPkgInit
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap $$ []
  · iPkgInit
  have Hlen : cfg.DataDir'.length < 2 ^ 60 := by have := Hfits.1; omega
  have hsd := bootSnap.snapDirOf_child hclean
  have Hslen : (config.snapDirOf cfg.DataDir').length < 2 ^ 60 := by
    have := (config.snapDirOf_fits Hfits).2; have := Hfits.1; omega
  -- `TouchDirAll(cfg.Logger, cfg.SnapDir())`
  wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDD
  · iframe DataDirF
  imod Fs.osNames_split R j (.except []) [go!"snap"] h CoPset.subseteq_top $$ Hsh Hn with ⟨Hs, -⟩
  have hb : (Fs.NameSet.except []).inter [go!"snap"] = .only [go!"snap"] := by
    simp [Fs.NameSet.inter]
  rw [hb]
  wp_apply (hTouch cfg.Logger' R j (config.snapDirOf cfg.DataDir')
      (path.joinModel [cfg.DataDir', go!"member"]) go!"snap" 1 (h.restrict j (.only [go!"snap"]))
      hsd bootSnap.nameOk_snap Hslen (bootSnap.restrictN_none _ _ hcur _)) $$ [Hp Hc Hs]
    as %terr ⟨Hp, Hc, Hr⟩
  · iframe Hp Hc Hs; iframe #
  icases Hr with (⟨%Hne, -⟩ | ⟨%Heq, %h', %hJ, %J, %n, ⟨%hJ1, -, %hJ3⟩, Hs, HJ, -⟩)
  · obtain ⟨ti, rfl⟩ : ∃ ti, terr = GoInterface.ok ti := by
      cases terr with
      | nil => exact absurd rfl Hne
      | ok ti => exact ⟨ti, rfl⟩
    wp_auto
    wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDD2
    · iframe DataDirF
    wp_apply hStr as %f0 -
    wp_apply hErr as %f1 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hFatal as %r Hf
    · iframe #
    iexfalso; iexact Hf
  subst Heq
  wp_auto
  icases Fs.osCallPerm_child R _ go!"snap" _ j 1 $$ Hp Hc with ⟨Hp, Hc⟩
  ihave HpJ := Fs.osPathS_child R _ go!"snap" (DFrac.own 1) j J h' bootSnap.nameOk_snap hJ1 $$ Hp Hs
  rw [← hsd]
  have hJn : ∀ b, hJ.cur !! b = none := fun b => by rw [hJ3]; rfl
  -- `RemoveMatchFile(cfg.Logger, cfg.SnapDir(), tmp)`
  wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDr
  · iframe DataDirF
  wp_apply (hRemove cfg.Logger' (config.snapDirOf cfg.DataDir') _ R J (DFrac.own 1) 1 (DFrac.own 1) hJ
      hJn) $$ [HpJ Hc HJ] as %rerr ⟨HpJ, Hc, HJ⟩
  · iframe HpJ Hc HJ; iframe #
  (try wp_auto)
  -- the branches: `err == nil` first (the split is on `decide (err = nil)`), then `err != nil`, which
  -- reads `err` again (`zap.Error(err)`)
  wp_join (iprop(True) : IProp GF) with [err] as -
  all_goals try (ipureintro; trivial)
  · wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDe
    · iframe DataDirF
    wp_apply hStr as %f0 -
    wp_apply hErr as %f1 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hError
    · iframe #
    wp_join_done
    try (ipureintro; trivial)
  -- `RemoveMatchFile(cfg.Logger, cfg.SnapDir(), db.tmp)`
  wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDr
  · iframe DataDirF
  wp_apply (hRemove cfg.Logger' (config.snapDirOf cfg.DataDir') _ R J (DFrac.own 1) 1 (DFrac.own 1) hJ
      hJn) $$ [HpJ Hc HJ] as %rerr ⟨HpJ, Hc, HJ⟩
  · iframe HpJ Hc HJ; iframe #
  (try wp_auto)
  -- the branches: `err == nil` first (the split is on `decide (err = nil)`), then `err != nil`, which
  -- reads `err` again (`zap.Error(err)`)
  wp_join (iprop(True) : IProp GF) with [err] as -
  all_goals try (ipureintro; trivial)
  · wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDe
    · iframe DataDirF
    wp_apply hStr as %f0 -
    wp_apply hErr as %f1 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hError
    · iframe #
    wp_join_done
    try (ipureintro; trivial)
  -- `RemoveMatchFile(cfg.Logger, cfg.SnapDir(), .snap)`
  wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDr
  · iframe DataDirF
  wp_apply (hRemove cfg.Logger' (config.snapDirOf cfg.DataDir') _ R J (DFrac.own 1) 1 (DFrac.own 1) hJ
      hJn) $$ [HpJ Hc HJ] as %rerr ⟨HpJ, Hc, HJ⟩
  · iframe HpJ Hc HJ; iframe #
  (try wp_auto)
  -- the branches: `err == nil` first (the split is on `decide (err = nil)`), then `err != nil`, which
  -- reads `err` again (`zap.Error(err)`)
  wp_join (iprop(True) : IProp GF) with [err] as -
  · wp_apply hInfo
    · iframe #
    wp_join_done
    try (ipureintro; trivial)
  · wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDe
    · iframe DataDirF
    wp_apply hStr as %f0 -
    wp_apply hErr as %f1 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl -
    wp_auto
    wp_apply hError
    · iframe #
    wp_join_done
    try (ipureintro; trivial)
  -- the snapshot directory's claims
  imod bootSnap.snapDir_carve R cfg.DataDir' J 1 1 hJ Hfits hJn $$ Hinv Hsh HpJ Hc HJ
    with ⟨Hdb, %F, %hF, HF⟩
  -- `snap.New(cfg.Logger, cfg.SnapDir())`
  wp_apply (hSnapDir cfg_ptr DFrac.discard cfg.DataDir' Hlen) as #HDDn
  · iframe DataDirF
  wp_apply (hNew cfg.Logger' (config.snapDirOf cfg.DataDir') ⟨cfg.DataDir', rfl⟩) as %ss #Hss
  · iframe #
    iapply zapLoggerOk_orNil; iexact Hzlg
  (try wp_auto)
  iapply HΦ
  iframe Hss Hdb
  iexists F
  iframe HF
  ipureintro
  exact fun i _ => hF i

end proof

end EtcdGrove
end Perennial
