/-
What the program logic may use of the premise **no I/O error on chosen files** (`NoIoErr S`,
`Premises.lean`) over a semantics whose steps satisfy it (`FsStepSat (NoIoErr S)`, which
`fsSemWithS (NoIoErr S) Q` has, `fsSemWithS_sat`): the errno of a covered call is 0 whenever the call
could succeed (`noIoErr_step`), and the error-free specs of the operations derived from their specs
by `wp_ext_post` (`WpPost.lean`), with no error arm. Untrusted.

The specs of the calls on an fd or a token here take `hS : ∀ st i, S.ino st i` (every inode covered):
the inode a step is on is the state's, which `wp_ext_post` does not see. A narrower inode set (the
WAL's directory) needs the step's state, and for a set given by paths the tree at the step (a
lifting with the tree, not made; `notes/wal-units/noioerr.md`). The calls on a path need only
`S.path` of their argument.
-/
module

public import GooseLang.Ext.Fs.NoIoErr
public import GooseLang.Ext.Fs.WpPost
public import GooseLang.Ext.Fs.Specs
public import GooseLang.Ext.Fs.Write
public import GooseLang.Ext.Fs.TreeShared
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [S : ExtSemantics fsExt] [FsSemOk]
variable {tf : GoTypeFns}
open Classical in

/-- **A covered call that could succeed does** (`NoIoErr`, from the semantics' step). -/
theorem noIoErr_step {Sio : IoSet} [hsat : FsStepSat (NoIoErr Sio)] {o : String} {v : val}
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step tf o v h st g e' h' st' g') (hc : IoCovers Sio o v st)
    (hex : ∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e'') : ErrnoZero o e' :=
  (hsat.sat o v h st g e' h' st' g' hs hc).1 hex

/-- **A covered `unlink`/`rmdir` that cannot succeed fails with Linux's errno** (`NoIoErr`'s
`PathErrno`, from the semantics' step). -/
theorem noIoErr_pathErrno {Sio : IoSet} [hsat : FsStepSat (NoIoErr Sio)] {o : String} {v : val}
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step tf o v h st g e' h' st' g') (hc : IoCovers Sio o v st)
    (hno : ¬ ∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e'') : PathErrno o v st e' :=
  (hsat.sat o v h st g e' h' st' g' hs hc).2 hno

open Classical in
/-- Every step of `fsync(fd)` returns 0 when every inode is covered. -/
theorem fsync_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i) (fd : w64) :
    ∀ h st g e' h' st' g', S.step tf "Fsync" (#fd) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', d, f, hv, hfd, hfl, -⟩ := hst
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨fd', d, hv, hfd, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.setFile d.ino (f.synced (InflightAt st d.ino ·)),
      by simp only [IsFsStep]; exact ⟨fd', d, f, hv, hfd, hfl, .inl ⟨by trivial, by trivial⟩⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- Every step of a directory fd's `close(fd)` returns 0 when every inode is covered. -/
theorem dirClose_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) :
    ∀ h st g e' h' st' g', S.step tf "DirClose" (#fd) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', e, df, hv, hdf, hst', -⟩ := hst
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨fd', df, hv, hdf, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.setProc { st.proc with dfds := GMap.delete fd' st.proc.dfds },
      by simp only [IsFsStep]; exact ⟨fd', 0, df, hv, hdf, by trivial, by trivial⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- Every step of a directory fd's `fsync(fd)` returns 0 when every inode is covered. -/
theorem dirSync_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) :
    ∀ h st g e' h' st' g', S.step tf "DirSync" (#fd) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', df, hv, hdf, -⟩ := hst
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨fd', df, hv, hdf, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.commitAll,
      by simp only [IsFsStep]; exact ⟨fd', df, hv, hdf, .inl ⟨by trivial, by trivial⟩⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- Every step of `pwrite`'s end on the token `t` of the change `c0` (a write at `off`, below
`maxBytes`) returns errno 0 when every inode is covered: a write of at least one byte can land
there (`maxBytes` page-aligned), so the premise rules the errno out. -/
theorem pwFinish_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (t : Nat) (c0 : OsChange) (off : Nat) (data : List w8) (hoff : off < maxBytes) :
    ∀ h st g e' h' st' g', (st.proc.inflight !! t = some c0 ∧ c0.kind = .write off data) →
      S.step tf "PWriteFinish" (osTokV t) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ ∃ r0, r = PairV r0 (#(0 : w64)) := by
  intro h st g e' h' st' g' ⟨hc0, hk0⟩ hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨t', c, off', data', f, k, e, hv, hc, hk, hfl, -, -, -, -, -, -⟩ := hst
  have htt : t = t' := by injection hv with hv; exact extVal_inj hv
  subst htt
  rw [hc0] at hc; cases hc
  rw [hk0] at hk; cases hk
  let k0 := if off + data.length ≤ maxBytes then data.length else maxBytes - off
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨t, c0, rfl, hc0, hS _ _⟩)
    ⟨_, _, by
      simp only [IsFsStep]
      refine ⟨t, c0, off, data, f, k0, 0, rfl, hc0, hk0, hfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
      · simp only [k0]; split <;> omega
      · left; refine ⟨?_, rfl⟩; simp only [k0]; split
        · exact .inl rfl
        · right; omega
      · simp only [k0]; split
        · exact .inr (.inl rfl)
        · right; right; rw [show off + (maxBytes - off) = maxBytes by omega]; rfl
      · simp only [k0]; split
        · right; assumption
        · right; omega, (⟨_, rfl⟩ : ∃ r : val, osRes _ 0 = osRes r 0)⟩
  obtain ⟨r0, hr0⟩ := (hz : ∃ r : val, e' = osRes r 0)
  exact ⟨_, hr0, r0, rfl⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`fsync(fd)` with no error** (`wp_osFsync` under `NoIoErr`, every inode covered): the file
durable. -/
theorem wp_osFsyncNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (lo : Nat) (xs : List ByteG)
    (hcov : m.Covers lo xs.length) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      osBytes (L := L) d.ino lo (DFrac.own 1) xs -∗
      (osMeta (L := L) d.ino (DFrac.own 1) m.synced -∗
        osBytes (L := L) d.ino lo (DFrac.own 1) (xs.map (fun x => durB x.1)) -∗
        osFd (L := L) fd dq d -∗ Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hb HΦ
  iapply wp_ext_post "Fsync" (#fd) (by simp) (· = #(0 : w64)) (fsync_noErr hS fd) Φ
  iapply wp_osFsync fd dq d m lo xs hcov hE _ $$ Hinv Hfd Hm Hb
  iintro %e Hr Hfd %he
  have he0 : e = 0 := go.intoVal_inj he
  subst he0
  icases Hr with (⟨-, Hm, Hb⟩ | ⟨%h0, -, -⟩)
  · iapply HΦ $$ Hm Hb Hfd
  · exact absurd rfl h0.1

/-- **A shared directory fd's `close(fd)` with no error** (`wp_osDirCloseS` under `NoIoErr`, every
inode covered). -/
theorem wp_osDirCloseSNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) (j : Ino) (ph : DirPhS) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osDirFdS (L := L) fd j ph -∗ Φ (#(0 : w64)) -∗
      WP (ExternalOp fsExt.name "DirClose" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_ext_post "DirClose" (#fd) (by simp) (· = #(0 : w64)) (dirClose_noErr hS fd) Φ
  iapply wp_osDirCloseS fd j ph hE _ $$ Hinv Hfd
  iintro %e %he
  rw [he]; iexact HΦ

/-- A change's token says what is in flight under it. -/
theorem pwTok_inflight (t : Nat) (p : Ino) (off : Nat) (data : List w8) (m : OsMeta)
    (xs : List ByteG) (n : Nat) (st : OsState) :
    iprop(pwTok (L := L) t p off data m xs n ∗ ExtInterp.localCtx (E := fsExt) (extLocalGS fsExt) st)
      ⊢ ⌜∃ c, st.proc.inflight !! t = some c ∧ c.kind = .write off data⌝ := by
  iintro ⟨Ht, Hc⟩
  icases (os_local_ctx_eq st).mp $$ Hc with Hc
  unfold pwTok osTok osCtx osCtxF
  icases Ht with ⟨Ht, -⟩
  icases Hc with ⟨⟨%Γb, %Γm, %Γf, %Γt, %Hwc, -, -, -, HAt, -⟩, -⟩
  icases gAuth_lookup _ _ _ _ _ _ $$ HAt Ht with %Hti
  ipureintro
  obtain ⟨c, hct⟩ : ∃ c, st.proc.inflight !! t = some c := by
    have := Hwc.2.toks t; rw [Hti] at this; exact Option.isSome_iff_exists.1 this.symm
  obtain ⟨-, hckind, -⟩ := Hwc.2.tok_is t _ c Hti hct
  exact ⟨c, hct, hckind⟩

/-- **`pwrite`'s end with no errno** (`wp_osPWriteFinishK` under `NoIoErr`, every inode covered,
the write's offset below `maxBytes`): `k` bytes written, errno 0. -/
theorem wp_osPWriteFinishKNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (keep : Bool) (t : Nat) (p : Ino) (off : Nat) (data : List w8)
    (m : OsMeta) (xs : List ByteG) (n : Nat) (hoff : off < maxBytes) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ pwTok (L := L) t p off data m xs n -∗
      (∀ k : Nat, ∀ zs : List Cands,
        ⌜k ≤ data.length ∧ (k = data.length ∨ 0 < k) ∧
          zs.length = pwSize m.size off k - m.size ∧
          ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ -∗
        ⌜∀ j c, m.pc (m.size + j) = some c → j < zs.length → zs[j]? = some c⌝ -∗
        ⌜PwCut off data.length k⌝ -∗
        osMeta (L := L) p (DFrac.own 1) (pwPostK keep m off data k n) -∗
        osBytes (L := L) p off (DFrac.own 1) (pwBytes m.size off data k n xs zs) -∗
        mcells m.maps off (off + data.length) (pwCell m.size off data k xs) -∗
        Φ (PairV (#(W64 k)) (#(0 : w64)))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_ext_postS "PWriteFinish" (osTokV t) (by simp [val.isPanic])
    (pwTok (L := L) t p off data m xs n)
    (fun (st : OsState) => ∃ c, st.proc.inflight !! t = some c ∧ c.kind = .write off data)
    (pwTok_inflight t p off data m xs n) (fun r => ∃ r0, r = PairV r0 (#(0 : w64)))
    (fun h st g e' h' st' g' ⟨c, hc, hk⟩ hs => pwFinish_noErr hS t c off data hoff h st g e' h' st' g'
      ⟨hc, hk⟩ hs) Φ $$ Ht
  iintro Ht
  iapply wp_osPWriteFinishK keep t p off data m xs n hE _ $$ Hinv Ht
  iintro %k %e %zs %h %hpc %hcut Hm Hbs Hc %he
  obtain ⟨r0, hr0⟩ := he
  injection hr0 with _ he0
  have he0 : e = 0 := go.intoVal_inj he0
  subst he0
  obtain ⟨hk, hke, hz⟩ := h
  have hke' : k = data.length ∨ 0 < k := by
    rcases hke with ⟨h1, -⟩ | h1
    · exact h1
    · exact absurd rfl h1
  have hall : k ≤ data.length ∧ (k = data.length ∨ 0 < k) ∧ _ := ⟨hk, hke', hz⟩
  iapply HΦ $$ %k %zs %hall %hpc %hcut Hm Hbs Hc

/-- **`pwrite`'s end, its error witnessed** (`wp_osPWriteFinish`, wal-fsfix2): an errno only when the
file system can fail on an inode or the write starts at or past `maxBytes`. -/
theorem wp_osPWriteFinishW (t : Nat) (p : Ino) (off : Nat) (data : List w8) (m : OsMeta)
    (xs : List ByteG) (n : Nat) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ pwTok (L := L) t p off data m xs n -∗
      (∀ k : Nat, ∀ e : w64, ∀ zs : List Cands,
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          zs.length = pwSize m.size off k - m.size ∧
          ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ -∗
        ⌜PwCut off data.length k⌝ -∗
        osMeta (L := L) p (DFrac.own 1) (pwPost m off data.length k) -∗
        osBytes (L := L) p off (DFrac.own 1) (pwBytes m.size off data k n xs zs) -∗
        mcells m.maps off (off + data.length) (pwCell m.size off data k xs) -∗
        ⌜e ≠ 0 → ¬ FsNoErrIno ∨ maxBytes ≤ off⌝ -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  by_cases hno : FsNoErrIno ∧ off < maxBytes
  · obtain ⟨⟨Sio, hi, h1, -, -⟩, hoff⟩ := hno
    iapply wp_ext_postS "PWriteFinish" (osTokV t) (by simp [val.isPanic])
      (pwTok (L := L) t p off data m xs n)
      (fun (st : OsState) => ∃ c, st.proc.inflight !! t = some c ∧ c.kind = .write off data)
      (pwTok_inflight t p off data m xs n) (fun r => ∃ r0, r = PairV r0 (#(0 : w64)))
      (fun h st g e' h' st' g' ⟨c, hc, hk⟩ hs => pwFinish_noErr (Sio := Sio) hi t c off data hoff
        h st g e' h' st' g' ⟨hc, hk⟩ hs) Φ $$ Ht
    iintro Ht
    iapply wp_osPWriteFinish t p off data m xs n hE _ $$ Hinv Ht
    iintro %k %e %zs %h %hpc Hm Hbs Hc %he
    obtain ⟨r0, hr0⟩ := he
    injection hr0 with _ he0
    have he0 : e = 0 := go.intoVal_inj he0
    subst he0
    iapply HΦ $$ %k %(0 : w64) %zs %h %hpc Hm Hbs Hc
    ipureintro; intro h0; exact absurd rfl h0
  · iapply wp_osPWriteFinish t p off data m xs n hE _ $$ Hinv Ht
    iintro %k %e %zs %h %hpc Hm Hbs Hc
    iapply HΦ $$ %k %e %zs %h %hpc Hm Hbs Hc
    ipureintro; intro _
    by_cases hf : FsNoErrIno
    · exact .inr (Nat.le_of_not_lt fun h' => hno ⟨hf, h'⟩)
    · exact .inl hf

/-- **A shared directory fd's `fsync(fd)`, its error witnessed** (`wp_osDirSyncS`, wal-fsfix2): an
errno only when the file system can fail on an inode (`¬ FsNoErrIno`). -/
theorem wp_osDirSyncSW (R : Roots) (fd : w64) (j : Ino) (ph : DirPhS) (n : Nat) (hE : ↑osN ⊆ E)
    (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osDirFdS (L := L) fd j ph -∗
      osLogLb (L := L) n -∗
      (∀ e : w64, osDirFdS (L := L) fd j ph -∗ (⌜e ≠ 0⌝ ∨ osCommitLb (L := L) n) -∗
        ⌜e ≠ 0 → ¬ FsNoErrIno⌝ -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "DirSync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hfd #Hlb HΦ
  by_cases hno : FsNoErrIno
  · obtain ⟨Sio, hi, h1, -, -⟩ := hno
    iapply wp_ext_post "DirSync" (#fd) (by simp) (· = #(0 : w64)) (dirSync_noErr (Sio := Sio) hi fd) Φ
    iapply wp_osDirSyncS R fd j ph n hE hE' _ $$ Hinv Hsi Hfd Hlb
    iintro %e Hfd Hr %he
    have he0 : e = 0 := go.intoVal_inj he
    subst he0
    iapply HΦ $$ Hfd Hr
    ipureintro; intro h; exact absurd rfl h
  · iapply wp_osDirSyncS R fd j ph n hE hE' _ $$ Hinv Hsi Hfd Hlb
    iintro %e Hfd Hr
    iapply HΦ $$ Hfd Hr
    ipureintro; intro _; exact hno

end specs

end Fs
end Perennial

end
