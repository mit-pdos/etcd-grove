/-
`(*WAL).renameWAL` over `fsExt`: the proof (W4 of `notes/wal-fsext-plan.md`, sixteenth session; spec
`LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/WAL__renameWAL.lean`). No `sorry`. The callees'
specs are its hypotheses: `os.RemoveAll.specAbsentN` (`CreateCallees.lean`), `os.Rename.specDirSnc`,
`newFilePipeline.spec`, `fileutil.OpenDir.spec`, `errors.AsLinkError.spec` (`LinuxFs/Spec/errors/
AsLinkError.lean`: `os.Rename`'s error is a `*LinkError`, `os.renameErrOk`, so `errors.As` matches it)
and `renameWALUnlock.spec` (a hypothesis: W4 log, sixteenth session, on why it is not provable as
stated). `RemoveAll`'s error exit commits the update with no effect (`osAUnc_none`) for the post's
`U none`; the spine law runs at the step after a committed rename. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWAL
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__renameWALUnlock
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir
public import LinuxFs.Spec.errors.AsLinkError
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem walTmpsRes_split' (j : Ino) :
    walTmpsRes (hG := hG) j ⊢ tmpClaim (hG := hG) j (pipeTmp 0) ∗ tmpClaim (hG := hG) j (pipeTmp 1) := by
  unfold walTmpsRes walTmps
  iintro ⟨H0, H1, -⟩
  iframe

/-- **An `osAUnc` committed with no effect**: when the update's input gives its output for the outcome
`none`, the update gives its result `Q none` (at a program step, with the generation's `notCrashed`). -/
theorem osAUnc_none {A : Type} (α : IProp GF) (β Q : Option A → IProp GF) (hb : α ⊢ β none) :
    ⊢ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ osAUnc α β Q ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ Q none := by
  iintro Hnc Hau
  ihave Hacc := osAUnc_unfold α β Q $$ Hau
  unfold osAUncPre
  imod (fupd_mask_subseteq (show osAuMask ⊆ (⊤ : CoPset) from fun _ _ => CoPset.mem_full)) with Hmc
  imod Hacc $$ Hnc with ⟨Hα, Hnc, Hcl⟩
  icases Hcl with ⟨-, Hco⟩
  ihave Hβ := hb $$ Hα
  imod Hco $$ %none Hβ with HQ
  imod Hmc
  imodintro
  iframe

theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.wp_proof (P : WalPbIn GF)
    (Mr : WalMarshal)
    (wp_RmAbsN : os.RemoveAll.specAbsentN (GF := GF) (hG := hG))
    (wp_Rename : os.Rename.specDirSnc (GF := GF) (hG := hG))
    (wp_nfp : go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec (GF := GF) (hG := hG))
    (wp_OpenDir : go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir.spec (GF := GF) (hG := hG))
    (wp_As : errors.AsLinkError.spec (GF := GF) (hG := hG))
    (wp_unlock : go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWALUnlock.spec (W := W) P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.renameWAL.spec (W := W) P Mr := by
  intro R jr J r dir nm tmp N h lb qp dq w lg mds md e lt f snapi enti U Sp SpR hok
  have hok' := hok
  obtain ⟨hin, hdl, hnm, htmp, hne, hNnm, hNt, htJ, hnmA, hSp, hU⟩ := hok
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, #Hlb, HN, Hau, HSp, Htmps, Hpre, Hfp, Hdf⟩
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, #Herrs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩
  have hdc := dir_child hin
  subst hdc
  iunfold walPreIn at Hpre
  icases Hpre with ⟨%locks, Hlg, #Hzap, Hdir, Hpre⟩
  try wp_auto
  wp_apply wp_RmAbsN r nm jr R qp N (DFrac.own (1 : Qp).half) h 1 hnm hNnm hnmA $$ [Hp HN Hperm]
    as %err ⟨Hp, HN, Hperm, -⟩
  · iframe; iframe #
  cases err
  case ok ei =>
    -- `RemoveAll(w.dir)` failed: the update committed with no effect
    iapply wp_notCrashed_acc _ _ rfl
    iintro Hnc
    imod osAUnc_none (osNames jr N (DFrac.own (1 : Qp).half) h)
      (renDirOut jr J N tmp nm h (DFrac.own (1 : Qp).half) lb) U
      (by unfold renDirOut logOut claimOut; exact emp_sep.2) $$ Hnc Hau
      with ⟨Hnc, HU⟩
    iframe Hnc
    imodintro
    try wp_auto
    iapply HΦ
    unfold renameWALPost
    iframe Hp
    iright; iright; ileft
    iframe
    isplitr
    · ipureintro; intro hc; cases hc
    ileft
    iunfold walPreIn
    iexists locks
    iframe; iframe #
  try wp_auto
  wp_apply wp_Rename r tmp nm jr J N R qp h (1 : Qp).half (1 : Qp).half lb U htmp hnm hNt hNnm hne htJ
    hnmA (Qp.half_add_half 1) $$ [Hp Hperm HN Hau] as %err ⟨Hp, Hperm, %o, %ho, HU, Hout⟩
  · iframe; iframe #
  cases err
  case ok ei =>
    -- the rename failed: `errors.As` matches its `*LinkError`, `renameWALUnlock`
    obtain ⟨le, hle⟩ := ho.2.resolve_left (by intro hc; cases hc)
    cases hle
    try wp_auto
    wp_apply wp_As le _ null $$ [$linkErr] as Hl
    try wp_auto
    wp_apply wp_unlock R jr J r (child r nm) nm tmp N h lb qp dq w lg mds md e lt f snapi enti U Sp SpR o
      hok' $$ [Hp Hperm HU Hout HSp Htmps Hlg Hdir Hpre Hfp Hdf] as %w' %err' Hpost
    · iframe; iframe #
      iunfold walPreIn
      iexists locks
      iframe; iframe #
    try wp_auto
    iapply HΦ $$ Hpost
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.1 (ho.1 rfl)
  -- committed: the spine law at a step after the rename
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  ihave Hlaw := hSp
  imod Hlaw $$ %x HSp Hnc HU Hout with ⟨Hnc, HU, Hs1, Hs2, HSpR⟩
  iframe Hnc
  imodintro
  ihave #Hwi : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold wal.walInit at Hwi
  icases Hwi with ⟨-, -, #Hseg, -⟩
  icases walTmpsRes_split' J $$ Htmps with ⟨Ht0, Ht1⟩
  ihave Hperm : osCallPerm ((1 : Qp).half + (1 : Qp).half) $$ [Hperm]
  · rw [Qp.half_add_half]; iexact Hperm
  icases (osCallPerm_split _ _).1 $$ Hperm with ⟨Hperm1, Hperm2⟩
  try wp_auto
  have hdl' : (child r nm).length < 2 ^ 61 := by omega
  wp_apply wp_nfp lg (child r nm) (W64 64000000) R dq J (by decide) (by decide) hdl' (by decide)
    $$ [Hperm1 Hs1 Ht0] as %fp ⟨%hfp, %γ, Hpipe, Hmain⟩
  · iframe; iframe #; unfold pipeRes; iframe
  try wp_auto
  wp_apply wp_OpenDir (child r nm) R J dq (1 : Qp).half $$ [Hs2 Hperm2] as %df %err ⟨Hs2, Hperm2, Hod⟩
  · iframe; iframe #
  try wp_auto
  icases Hod with (⟨%fd, %herr, Hf, Hdfd⟩ | ⟨%herr, %hdf⟩)
  · subst herr
    iapply HΦ
    unfold renameWALPost
    iframe Hp
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists x, fp, γ, (W64 64000000), df, fd
    iframe
    iunfold walPreIn
    iexists locks
    iframe; iframe #
  · iapply HΦ
    unfold renameWALPost
    iframe Hp
    iright; iright; iright
    isplitr
    · ipureintro; exact herr
    iexists x
    iframe

end proof

end EtcdGrove
end Perennial
