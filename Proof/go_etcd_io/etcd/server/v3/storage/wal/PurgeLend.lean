/- Lean-first (no Rocq counterpart).

# The handle's side of a purge (unit `locks`, session 9; `notes/wal-units/locks.md`)

A purge round runs while the WAL's handle is lent to it (`walOpenWF`, the tester's `purgeRound` between
the apply thread's `ReleaseLockTo` and its next operation). The round needs, of the handle: its half of the
WAL directory's claim (half of which goes into each removal's update, `walPurge_osAUnc`, a quarter to the
call), the directory's path, the call permission's quarter, the tail's key and record (its cuts), the lock
token's pending-cut flag, the record of what is out (the directory's claim), and the locked range
(`walDirLks`). It gives them back with the claim's names after its removals (`hj'`): only `.wal` names
removed, never the tail's (`WalSub`), which keeps `walDirH`'s facts (the tail at its name, the largest `.wal`
name) and, the removed names being no locked segment's, `LkRel` (`LkRel_subAt`).

- `WalSubAt hj hj' nm`, `WalSub hj hj' nm0`: the `.wal` names after a removal of `nm`, after removals none of
  `nm0`; `walSub_refl`, `walSub_trans_at`.
- `LkRel_subAt`, `walDirLks_purgeStep`: the locked range after a removal (the purger's lock on the inode
  excludes a locked segment's name: `walDirLks_purge`).
- `walDirH_lend`, `walOpenWF_lend`: the lending laws.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeSafe
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLaws
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The `.wal` names after the removal of `nm`** (or none). -/
def WalSubAt (hj hj' : NamesH) (nm : GoString) : Prop :=
  ∀ b, walNameP b = true → hj'.cur !! b = hj.cur !! b ∨ (b = nm ∧ hj'.cur !! b = none)

/-- **The `.wal` names after removals, none of `nm0`.** -/
def WalSub (hj hj' : NamesH) (nm0 : GoString) : Prop :=
  ∀ b, walNameP b = true → hj'.cur !! b = hj.cur !! b ∨ (b ≠ nm0 ∧ hj'.cur !! b = none)

theorem walSub_refl (hj : NamesH) (nm0 : GoString) : WalSub hj hj nm0 := fun _ _ => Or.inl rfl

theorem walSub_trans_at {hj hj' hj'' : NamesH} {nm0 nm : GoString} (h : WalSub hj hj' nm0)
    (h' : WalSubAt hj' hj'' nm) (hne : nm ≠ nm0) : WalSub hj hj'' nm0 := by
  intro b hb
  rcases h' b hb with e | ⟨rfl, e⟩
  · rw [e]; exact h b hb
  · exact Or.inr ⟨hne, e⟩

/-- **The locked range after a removal** of a `.wal` name neither the tail's nor a locked segment's. -/
theorem LkRel_subAt {hj hj' : NamesH} {cuts : List Nat} {nm0 nm : GoString} {ls : List (GoString × Ino)}
    {b : Nat} (hr : LkRel hj cuts nm0 ls b) (hs : WalSubAt hj hj' nm) (h0 : nm ≠ nm0)
    (hl : nm ∉ ls.map (·.1)) : LkRel hj' cuts nm0 ls b := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  refine ⟨h1, h2, h3, fun k l hk => ?_, fun nm' n hn hw hne hnl => ?_, h6⟩
  · obtain ⟨hc, hix⟩ := h4 k l hk
    have hw : walNameP l.1 = true := by
      obtain ⟨ix, e⟩ := hix
      rw [e]; unfold walNameP walFileName
      simp only [decide_eq_true_eq]
      exact List.suffix_append _ _
    rcases hs l.1 hw with e | ⟨e, -⟩
    · rw [e]; exact ⟨hc, hix⟩
    · exact absurd (e ▸ List.mem_map_of_mem (List.mem_of_getElem? hk)) hl
  · rcases hs nm' hw with e | ⟨-, e⟩
    · rw [e] at hn; exact h5 nm' n hn hw hne hnl
    · rw [e] at hn; cases hn

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **A removal's step on the locked range** (the purger holding a lock `osLock k i fd'` on the inode `nm`
names, `nm` not the tail's): the range `b` and the locks' names (`nm` none of them), and the range back for
the names after the removal. -/
theorem walDirLks_purgeStep (dir : GoString) (hj : NamesH) (nm0 : GoString) (lfs : List Loc)
    (cuts : List Nat) (i : Ino) (k : LockKind) (fd' : w64) (nm : GoString)
    (hn : hj.cur !! nm = some (.file i)) (h0 : nm ≠ nm0) :
    walDirLks (W := W) dir hj nm0 lfs cuts ∗ osLock (GF := GF) k i fd' ∗
        fileutil.lockKind (GF := GF) k ⊢
      ∃ (γt : GName) (b : Nat) (ls : List (GoString × Ino)),
        walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName))
            (<[dir := b]> (∅ : GMap GoString Nat)) ∗
          osLock (GF := GF) k i fd' ∗ ⌜LkRel hj cuts nm0 ls b ∧ nm ∉ ls.map (·.1)⌝ ∗
          ∀ hj' : NamesH, ⌜WalSubAt hj hj' nm⌝ -∗
            walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName))
              (<[dir := b]> (∅ : GMap GoString Nat)) -∗
            walDirLks (W := W) dir hj' nm0 lfs cuts := by
  unfold walDirLks
  iintro ⟨⟨%γt, %b, %ls, Htf, Hls, %hr⟩, Hl, #Hk⟩
  ihave ⟨Hls, Hl, %hx⟩ := walLocksHI_excl lfs ls i k fd' $$ [Hls Hl]
  · iframe; iexact Hk
  have hnl : nm ∉ ls.map (·.1) := by
    intro hm
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
    obtain ⟨k', hk'⟩ := List.getElem?_of_mem hl
    have := (hr.2.2.2.1 k' l hk').1
    rw [hn] at this
    cases this
    exact hx l hl rfl
  iexists γt, b, ls
  iframe Htf Hl
  isplitr
  · ipureintro; exact ⟨hr, hnl⟩
  iintro %hj' %hs Htf
  iexists γt, b, ls
  iframe Htf Hls
  ipureintro
  exact LkRel_subAt hr hs h0 hnl

/-- **The tail's description and its lock** (the handle's `walTailW` conjunct; unit `locks`, session 10): lent
with the handle to a purge round, so that a purger's lock refutes being on the tail's inode
(`walTailLk_excl`). -/
def walTailLk (fd : w64) (i : Ino) : IProp GF :=
  iprop(∃ (rd : Bool) (lo lk : Option Bool), osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗
    fdLocksW fd ⟨i, rd, true, lo, lk⟩)

/-- **A purger's lock is not on the tail's inode** (the tail's description holds an exclusive lock:
`fdLocksW_excl`, `fdLocks_excl`). -/
theorem walTailLk_excl (fd : w64) (i i' : Ino) (k : LockKind) (fd' : w64) :
    walTailLk (GF := GF) fd i ∗ osLock (GF := GF) k i' fd' ∗ fileutil.lockKind (GF := GF) k ⊢
      walTailLk (GF := GF) fd i ∗ osLock (GF := GF) k i' fd' ∗ ⌜i' ≠ i⌝ := by
  iintro ⟨H, Hl, #Hk⟩
  by_cases he : i' = i
  · subst he
    unfold walTailLk
    icases H with ⟨%rd, %lo, %lk, -, Hw⟩
    ihave ⟨Hlk, %hk⟩ := fdLocksW_excl fd _ rfl $$ Hw
    obtain ⟨kk, hkk⟩ := hk
    iexfalso
    iapply fdLocks_excl fd fd' ⟨i', rd, true, lo, lk⟩ kk k hkk
    iframe; iexact Hk
  · iframe; ipureintro; exact he

/-- **The handle's share of its directory, lent** (see the file header): back with the claim's names after
removals of `.wal` names but the tail's. -/
theorem walDirH_lend (dir : GoString) (j : Ino) (dfd : w64) (ino : Ino) (name : GoString) (k : Nat)
    (lfs : List Loc) (cuts : List Nat) (qp : Qp) (nmd : Roots → Qp → IProp GF) (nf : Option GoString) :
    walDirH (W := W) dir j dfd ino name k lfs cuts qp nmd nf ⊢
      ∃ (R : Roots) (q : Qp) (X : List GoString) (hj : NamesH) (nm0 : GoString),
        walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        osPathS R dir (DFrac.own q) j ∗ osSharedInv R ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
        walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗ walDirLks (W := W) dir hj nm0 lfs cuts ∗
        ⌜walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file ino) ∧ (∀ b ∈ X, walNameP b = false) ∧
          ∀ b n, hj.cur !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0⌝ ∗
        ∀ hj' : NamesH, ⌜WalSub hj hj' nm0⌝ -∗
          osNames j (.except X) (DFrac.own (1 : Qp).half) hj' -∗ osPathS R dir (DFrac.own q) j -∗
          osSharedInv R -∗ osCallPerm (callKey R dir) (1 : Qp).half.half -∗
          walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ -∗ walDirLks (W := W) dir hj' nm0 lfs cuts -∗
          walDirH (W := W) dir j dfd ino name k lfs cuts qp nmd nf := by
  unfold walDirH
  iintro ⟨%R, %q, %X, %hj, %nm0, %ph, #Hkey, Hn, Hp, #Hsh, %hRW, Hc, Hfd, Hnmd, Ho, Hlk, Hnf, %hf⟩
  obtain ⟨hw0, hc0, hpd, htmp, hX, hsq, hmax⟩ := hf
  iexists R, q, X, hj, nm0
  iframe Hkey Hn Hp Hsh Hc Ho Hlk
  isplitr
  · ipureintro; exact ⟨hw0, hc0, hX, hmax⟩
  iintro %hj' %hs Hn Hp - Hc Ho Hlk
  iexists R, q, X, hj', nm0, ph
  iframe Hkey Hn Hp Hsh Hc Hfd Hnmd Ho Hlk Hnf
  isplitr
  · ipureintro; exact hRW
  ipureintro
  refine ⟨hw0, ?_, hpd, htmp, hX, hsq, fun b n hb hw => ?_⟩
  · rcases hs nm0 hw0 with e | ⟨hne, -⟩
    · rw [e]; exact hc0
    · exact absurd rfl hne
  · rcases hs b hw with e | ⟨-, e⟩
    · rw [e] at hb; exact hmax b n hb hw
    · rw [e] at hb; cases hb

/-- **The client handle, lent to a purge round** (see the file header): its share of the directory
(`walDirH_lend`), its tail's key and record (`tg`: the history, metadata, cuts, write position, inode), the
lock token's pending-cut flag, the tail's locked description (`walTailLk`, session 10); back with the claim's
names after removals of `.wal` names but the tail's. -/
theorem walOpenWF_lend (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    walOpenWF (W := W) P Mr w dir ⊢
      ∃ (j : Ino) (X : List GoString) (hj : NamesH) (R : Roots) (q : Qp) (nm0 : GoString) (ino : Ino)
        (lfs : List Loc) (γ : GName) (tg : TailG) (tfd : w64),
        walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        osPathS R dir (DFrac.own q) j ∗ osSharedInv R ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
        walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗ walDirLks (W := W) dir hj nm0 lfs tg.2.2.1 ∗
        walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗ walCutFrag (W := W) none ∗
        walTailLk (GF := GF) tfd ino ∗
        ⌜walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file ino) ∧ (∀ b ∈ X, walNameP b = false) ∧
          ∀ b n, hj.cur !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0⌝ ∗
        ∀ hj' : NamesH, ⌜WalSub hj hj' nm0⌝ -∗
          osNames j (.except X) (DFrac.own (1 : Qp).half) hj' -∗ osPathS R dir (DFrac.own q) j -∗
          osSharedInv R -∗ osCallPerm (callKey R dir) (1 : Qp).half.half -∗
          walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ -∗
          walDirLks (W := W) dir hj' nm0 lfs tg.2.2.1 -∗ walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
          walCutFrag (W := W) none -∗ walTailLk (GF := GF) tfd ino -∗ walOpenWF (W := W) P Mr w dir := by
  refine (walOpenWF_iff (W := W) P Mr w dir).1.trans ?_
  iintro ⟨%h, Hh, %hd, %hmd, Hpc⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hdh,
    Hl1, Hl2, Hl3, %hl4, Hl5, Hl6, Hl7, Hl8, Hl9, Hl10, Hl11, Hopen, %hpure⟩
  unfold walTailW
  icases Ht with ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  icases walDirH_lend dir j dfd h.ino name h.pc lfs.dropLast h.cuts _ _ _ $$ Hdh with
    ⟨%R, %q, %X, %hj, %nm0, #Hkey, Hn, Hp, #Hsh, Hc, Ho, Hlk, %hf, Hback⟩
  icases (walOpenWI_cut (W := W) w dir h.inc).1 $$ Hopen with ⟨Hwc, Hpf, Hcf⟩
  iexists j, X, hj, R, q, nm0, h.ino, lfs.dropLast, h.γ,
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG), fd
  unfold tailVar
  iframe Hkey Hn Hp Hsh Hc Ho Hlk Hk Hv Hcf
  isplitl [Hfd]
  · unfold walTailLk; iexact Hfd
  isplitr
  · ipureintro; exact hf
  iintro %hj' %hs Hn Hp Hsh' Hc Ho Hlk Hk Hv Hcf Hfd
  ihave Hdh := Hback $$ %hj' %hs Hn Hp Hsh' Hc Ho Hlk
  ihave Hopen := (walOpenWI_cut (W := W) w dir h.inc).2 $$ [Hwc Hpf Hcf]
  · iframe Hwc Hpf Hcf
  iapply (walOpenWF_iff (W := W) P Mr w dir).2
  iexists h
  iframe Hpc
  isplitl [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hdh Hl1 Hl2 Hl3 Hl5 Hl6 Hl7 Hl8 Hl9 Hl10 Hl11 Hopen Hf Hfd Hoff Hk Hm Hb Hv]
  · unfold walHandleIn
    iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hdh Hl1 Hl2 Hl3 Hl5 Hl6 Hl7
      Hl8 Hl9 Hl10 Hl11 Hopen
    unfold walTailW
    iunfold walTailLk at Hfd
    iframe Hf Hfd Hoff Hk
    isplitl [Hm Hb Hv]
    · iexists m, bs
      iframe Hm Hb Hv
      ipureintro; exact hp
    ipureintro; exact ⟨hl4, hpure⟩
  · ipureintro; exact ⟨hd, hmd⟩

/-- `walOpenWF_lend` at the incarnation `i`. -/
theorem walOpenWFI_lend (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (i : Nat) :
    walOpenWFI (W := W) P Mr w dir i ⊢
      ∃ (j : Ino) (X : List GoString) (hj : NamesH) (R : Roots) (q : Qp) (nm0 : GoString) (ino : Ino)
        (lfs : List Loc) (γ : GName) (tg : TailG) (tfd : w64),
        walDirKey (W := W) dir j X ∗ osNames j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        osPathS R dir (DFrac.own q) j ∗ osSharedInv R ∗ osCallPerm (callKey R dir) (1 : Qp).half.half ∗
        walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ ∗ walDirLks (W := W) dir hj nm0 lfs tg.2.2.1 ∗
        walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗ walCutFrag (W := W) none ∗
        walTailLk (GF := GF) tfd ino ∗
        ⌜walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file ino) ∧ (∀ b ∈ X, walNameP b = false) ∧
          ∀ b n, hj.cur !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0⌝ ∗
        ∀ hj' : NamesH, ⌜WalSub hj hj' nm0⌝ -∗
          osNames j (.except X) (DFrac.own (1 : Qp).half) hj' -∗ osPathS R dir (DFrac.own q) j -∗
          osSharedInv R -∗ osCallPerm (callKey R dir) (1 : Qp).half.half -∗
          walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ -∗
          walDirLks (W := W) dir hj' nm0 lfs tg.2.2.1 -∗ walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
          walCutFrag (W := W) none -∗ walTailLk (GF := GF) tfd ino -∗ walOpenWFI (W := W) P Mr w dir i := by
  refine (walOpenWFI_iff (W := W) P Mr w dir i).1.trans ?_
  iintro ⟨%h, Hh, %hd, %hmd, %hi, Hpc⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hdh,
    Hl1, Hl2, Hl3, %hl4, Hl5, Hl6, Hl7, Hl8, Hl9, Hl10, Hl11, Hopen, %hpure⟩
  unfold walTailW
  icases Ht with ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  icases walDirH_lend dir j dfd h.ino name h.pc lfs.dropLast h.cuts _ _ _ $$ Hdh with
    ⟨%R, %q, %X, %hj, %nm0, #Hkey, Hn, Hp, #Hsh, Hc, Ho, Hlk, %hf, Hback⟩
  icases (walOpenWI_cut (W := W) w dir h.inc).1 $$ Hopen with ⟨Hwc, Hpf, Hcf⟩
  iexists j, X, hj, R, q, nm0, h.ino, lfs.dropLast, h.γ,
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG), fd
  unfold tailVar
  iframe Hkey Hn Hp Hsh Hc Ho Hlk Hk Hv Hcf
  isplitl [Hfd]
  · unfold walTailLk; iexact Hfd
  isplitr
  · ipureintro; exact hf
  iintro %hj' %hs Hn Hp Hsh' Hc Ho Hlk Hk Hv Hcf Hfd
  ihave Hdh := Hback $$ %hj' %hs Hn Hp Hsh' Hc Ho Hlk
  ihave Hopen := (walOpenWI_cut (W := W) w dir h.inc).2 $$ [Hwc Hpf Hcf]
  · iframe Hwc Hpf Hcf
  iapply (walOpenWFI_iff (W := W) P Mr w dir i).2
  iexists h
  iframe Hpc
  isplitl [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hdh Hl1 Hl2 Hl3 Hl5 Hl6 Hl7 Hl8 Hl9 Hl10 Hl11 Hopen Hf Hfd Hoff Hk Hm Hb Hv]
  · unfold walHandleIn
    iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hdh Hl1 Hl2 Hl3 Hl5 Hl6 Hl7
      Hl8 Hl9 Hl10 Hl11 Hopen
    unfold walTailW
    iunfold walTailLk at Hfd
    iframe Hf Hfd Hoff Hk
    isplitl [Hm Hb Hv]
    · iexists m, bs
      iframe Hm Hb Hv
      ipureintro; exact hp
    ipureintro; exact ⟨hl4, hpure⟩
  · ipureintro; exact ⟨hd, hmd, hi⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
