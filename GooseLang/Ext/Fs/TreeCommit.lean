/-
The durability of the tree: a successful `fsync(2)` of a directory commits every entry of the tree's
log (`DirSync`, `Impl.lean`: ext4 commits the whole journal), and a crash keeps every committed
entry (`MachineCrash`). The ghost state records it as a persistent lower bound on the committed
prefix of the log (`osCommitLb n`: the first `n` entries are committed), held against the
authoritative bound of the state interpretation (`commitRes`, `Ghost.lean`); `wp_osDirSync_lb`
gives it for the whole history its caller holds a fraction of, and `TreeCrashLb.lean` turns it into
what a crash keeps (`TreeCrashedLb`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSpecsDirFd

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The first `n` entries of the tree's log are committed: a crash keeps them (persistent). -/
def osCommitLb (n : Nat) : IProp GF := gCommitLb (gooseOsGS (L := L)) n

instance osCommitLb_persistent (n : Nat) : Persistent (osCommitLb (L := L) n) := by
  unfold osCommitLb; infer_instance

instance osCommitLb_timeless (n : Nat) : Timeless (osCommitLb (L := L) n) := by
  unfold osCommitLb; infer_instance

/-- A lower bound weakened. -/
theorem osCommitLb_le {n : Nat} (n' : Nat) (h : n' ≤ n) :
    ⊢ osCommitLb (L := L) n -∗ osCommitLb (L := L) n' := by
  unfold osCommitLb; exact gCommitLb_le _ n' h

/-- Nothing is a lower bound for free. -/
theorem osCommitLb_zero : ⊢ |==> osCommitLb (L := L) 0 := by
  unfold osCommitLb gCommitLb
  letI := (gooseOsGS (L := L)).osAllG
  exact monoNatLbOwn_0 _

/-- `wp_fs_stepT`, with the committed prefix's authoritative bound too (`commitRes`). -/
theorem wp_fs_stepTC (o : String) (v : val) (Φ : val → IProp GF) (hv : v.isPanic = false)
    (hE : ↑osN ⊆ E) :
    ⊢ osInv (L := L) -∗
      (∀ st Γb Γm Γf Γt V Γdf Γc h, osWorld st Γb Γm Γf Γt h -∗ treeWorld st V Γdf Γc -∗
          commitRes (gooseOsGS (L := L)) st ==∗
        ⌜∃ e' h' st', FsStep o v h st () e' h' st' ()⌝ ∗
        ▷ ∀ e' h' st', ⌜FsStep o v h st () e' h' st' ()⌝ ==∗
          ∃ Γb' Γm' Γf' Γt' V' Γdf' Γc', osWorld st' Γb' Γm' Γf' Γt' h' ∗
            treeWorld st' V' Γdf' Γc' ∗ commitRes (gooseOsGS (L := L)) st' ∗
            WP e' @ s; E {{ Φ }}) -∗
      WP (ExternalOp fsExt.name o (Val v)) @ s; E {{ Φ }} := by
  iintro #Hinv HF
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl -
  icases (os_local_ctx_eq σ).mp $$ Hl with Hl
  unfold osCtx osCtxF treeCtx
  icases Hl with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, HAb, HAm, HAf, HAt, Htok, Hv⟩,
    ⟨%V, %Γdf, %Γc, %Hns, HAd, HAdf, HAc, Hrd, Hcr, Hcm⟩⟩
  unfold osInv
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with >Hi
  icases Hi with ⟨%cv, %n, Hv', Hcells⟩
  icases gVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨rfl, rfl⟩ := Heq
  imod HF $$ %σ %Γb %Γm %Γf %Γt %V %Γdf %Γc %h [HAb HAm HAf HAt Htok Hcells Hheap]
    [HAd HAdf HAc Hrd Hcr] Hcm with ⟨%Hex, Hcont⟩
  · unfold osWorld; iframe; ipureintro; exact Hwc
  · unfold treeWorld; iframe; ipureintro; exact Hns
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ E \ ↑osN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isplitr
  · ipureintro
    obtain ⟨e', h', st', Hst⟩ := Hex
    exact FsSemOk.step_ex _ _ _ _ g _ _ _ ()
      (fun _ _ _ _ _ h1 h2 => mapsTo_unique Hwc.1 h1 h2) Hst
  inext
  iintro %e' %h' %σ' %g' %Hst -
  have Hst := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ Hst
  imod Hclose2
  imod Hcont $$ %e' %h' %σ' %Hst with
    ⟨%Γb', %Γm', %Γf', %Γt', %V', %Γdf', %Γc', Hw, Hn, Hcm, Hwp⟩
  unfold osWorld
  icases Hw with ⟨%Hwc', HAb, HAm, HAf, HAt, Htok, Hcells, Hheap⟩
  imod gVar_update _ _ _ (cellView σ', GMap.size σ'.proc.inflight) $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hcells] with -
  · inext; iexists (cellView σ'), (GMap.size σ'.proc.inflight); iframe
  imodintro
  iframe Hheap Hwp
  isplitl [HAb HAm HAf HAt Htok Hv Hn Hcm]
  · iapply (os_local_ctx_eq σ').mpr
    unfold osCtx osCtxF treeCtx
    isplitl [HAb HAm HAf HAt Htok Hv]
    · iexists Γb', Γm', Γf', Γt'
      iframe
      ipureintro; exact Hwc'
    · unfold treeWorld
      icases Hn with ⟨%Hns', HAd, HAdf, HAc, Hrd, Hcr⟩
      iexists V', Γdf', Γc'
      iframe HAd HAdf HAc Hrd Hcr Hcm
      ipureintro; exact Hns'
  · have : (ExtInterp.globalCtx (E := fsExt) (extGlobalGS fsExt) g' : IProp GF) =
        iprop(True) := rfl
    rw [this]; itrivial

/-- `commitRes` after a commit of the whole log: the bound raised to the log's length, and a lower
bound of it. -/
theorem commitRes_commitAll (st : OsState) :
    ⊢ commitRes (gooseOsGS (L := L)) st ==∗
      commitRes (gooseOsGS (L := L)) st.commitAll ∗ osCommitLb (L := L) st.fs.metaLog.length := by
  unfold commitRes osCommitLb
  iintro ⟨%c, %hc, Ha⟩
  imod gCommit_update _ c (max c st.fs.metaLog.length) (Nat.le_max_left _ _) $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  isplitl [Ha]
  · iexists (max c st.fs.metaLog.length)
    iframe Ha
    ipureintro
    intro y hy
    show st.fs.committed y ∨ y < st.fs.metaLog.length
    by_cases h : y < c
    · exact Or.inl (hc y h)
    · exact Or.inr (by omega)
  · iapply gCommitLb_le _ _ (Nat.le_max_right _ _) $$ Hlb

/-- **`fsync(2)` of a directory fd, with durability**: any errno; on success (`0`), every entry of
the history `W` the caller holds a fraction of is committed (`osCommitLb W.2.length`). The ghost
state as it was. -/
theorem wp_osDirSync_lb (fd : w64) (dq : DFrac) (x : Ino × DirPh) (dqt : DFrac) (R : Roots)
    (W : Hist) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFd (L := L) fd dq x -∗ osTree (L := L) dqt R W -∗
      (∀ e : w64, osDirFd (L := L) fd dq x -∗ osTree (L := L) dqt R W -∗
        (⌜e ≠ 0⌝ ∨ osCommitLb (L := L) W.2.length) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirSync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  iapply wp_fs_stepTC "DirSync" _ Φ (by simp [val.isPanic]) hE $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %V %Γdf %Γc %h Hw Hn Hcm
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Ht with %HV
  obtain ⟨rfl, rfl⟩ := HV
  unfold osDirFd
  icases gAuth_lookup _ _ _ _ _ _ $$ HAdf Hfd with %Hfl
  obtain ⟨df, hdf⟩ : ∃ df, st.proc.dfds !! fd = some df := by
    have := hc.fds fd; rw [Hfl] at this
    cases h0 : st.proc.dfds !! fd with
    | none => rw [h0] at this; cases this
    | some df => exact ⟨df, rfl⟩
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_refl st) Hag
    exact ⟨_, h, st, ⟨fd, df, rfl, hdf, .inr ⟨1, by decide, rfl, rfl⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', df', hv, -, hres⟩ := Hst
  cases go.intoVal_inj hv
  have hlen : W.2.length = st.fs.metaLog.length := by rw [hc.hist]
  rcases hres with ⟨rfl, rfl⟩ | ⟨e, he, rfl, hst⟩
  · -- success: the whole log committed
    have hw' : FsTreeWf st.commitAll := ⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩
    have hc' : TreeCoh st.commitAll W Γdf Γc := hc.congr rfl rfl rfl rfl
    imod worlds_close (st := st) (st' := st.commitAll) ⟨rfl, rfl, rfl, rfl, rfl⟩ Hr Hfr rfl hw' hc' $$ [HAb HAm HAf HAt Htok Hcells Hσ]
      HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imod commitRes_commitAll st $$ Hcm with ⟨Hcm, #Hlb⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, W, Γdf, Γc
    try unfold osWorld
    try unfold treeWorld
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    isplitl [Hcm]
    · iexact Hcm
    iapply wp_value'
    iapply HΦ $$ %0 [Hfd] Ht
    · (try unfold osDirFd); iexact Hfd
    · iright; rw [hlen]; iexact Hlb
  · -- failure: nothing changed
    rw [hst] at Hr Hfr ⊢
    imod worlds_close (filesSame_refl st) Hr Hfr rfl hw hc $$ [HAb HAm HAf HAt Htok Hcells Hσ]
      HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
    · unfold osWorld; iframe; ipureintro; exact Hwc
    imodintro
    iexists Γb, Γm, Γf, Γt, W, Γdf, Γc
    try unfold osWorld
    try unfold treeWorld
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    isplitl [Hcm]
    · iexact Hcm
    iapply wp_value'
    iapply HΦ $$ %e [Hfd] Ht
    · (try unfold osDirFd); iexact Hfd
    · ileft; ipureintro; exact he

end specs

end Fs
end Perennial

end
