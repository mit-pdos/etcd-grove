/- Lean-first (no Rocq counterpart).

# Why a purger's lock makes a segment safe to remove (unit `locks`, session 6; `notes/wal-units/locks.md`)

The handle's half of the purge law. A purger (`purgeRound`, `fileutil.purgeFile`) removes a segment
only after `TryLockFile` on it succeeded: it holds `osLock k i fd'` (of `fileutil`'s kind) on the
segment's inode `i`. Against the handle's locks (`walDirLks`, `Handle.lean`):

* `walLocksHI_excl`: no non-tail lock of the handle is on `i` (`fdLocks_excl` against each);
* `LkRel_purge` (pure): a `.wal` name of the directory that is neither the tail's nor a locked one's
  has a sequence below the first locked segment's (`LkRel`), so it ends at or before the registered
  range's start `b` (the cuts increasing);
* `walDirLks_purge`: the two together: the segment named `nm`, on `i`, sequence `sq`, ends at or
  before `b` (`segStart cuts (sq + 1) ≤ b`), with `b` the range the invariant bounds by `unl`
  (`walLks_agree`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.LockRange
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The purge's bound from the handle's relation**: a `.wal` name `nm` of the directory, neither
the tail's (`nm0`) nor a locked segment's, with sequence `sq` (below `2 ^ 64`), ends at or before the
registered range's start `b`. -/
theorem LkRel_purge {hj : NamesH} {cuts : List Nat} {nm0 : GoString} {ls : List (GoString × Ino)}
    {b : Nat} {nm : GoString} {n : Node} {sq ix : Nat} (hr : LkRel hj cuts nm0 ls b)
    (hc : cuts.Pairwise (· < ·)) (hn : hj.cur !! nm = some n) (hw : walNameP nm = true)
    (h0 : nm ≠ nm0) (hl : nm ∉ ls.map (·.1)) (hnm : nm = walFileName sq ix) (hsq : sq < 2 ^ 64) :
    sq + 1 ≤ cuts.length - ls.length ∧ segStart cuts (sq + 1) ≤ b := by
  obtain ⟨-, hcl, -, -, hrest, hb⟩ := hr
  obtain ⟨sq', ix', e, hlt⟩ := hrest nm n hn hw h0 hl
  have hm := walFileName_seq_mod (hnm.symm.trans e)
  rw [Nat.mod_eq_of_lt hsq, Nat.mod_eq_of_lt (by omega : sq' < 2 ^ 64)] at hm
  subst hm
  exact ⟨by omega, Nat.le_trans (segStart_mono hc (by omega) (by omega)) hb⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- A locked segment of the handle is not on an inode another description holds the lock of. -/
theorem walLockHI_excl (lf : Loc) (bn : GoString) (i i' : Ino) (k : LockKind) (fd' : w64) :
    walLockHI (GF := GF) lf bn i ∗ osLock (GF := GF) k i' fd' ∗ fileutil.lockKind (GF := GF) k ⊢
      walLockHI (GF := GF) lf bn i ∗ osLock (GF := GF) k i' fd' ∗ ⌜i ≠ i'⌝ := by
  iintro ⟨H, Hl, #Hk⟩
  by_cases he : i = i'
  · subst he
    unfold walLockHI
    icases H with ⟨%f, %fd, %pd, %d, -, -, -, Hlk, %h⟩
    obtain ⟨-, hi, kk, hkk⟩ := h
    subst hi
    iexfalso
    iapply fdLocks_excl fd fd' d kk k hkk
    iframe; iexact Hk
  · iframe
    ipureintro; exact he

/-- **No non-tail lock of the handle is on `i`**, the inode a purger holds the lock of. -/
theorem walLocksHI_excl (lfs : List Loc) (ls : List (GoString × Ino)) (i : Ino) (k : LockKind)
    (fd' : w64) :
    ([∗list] lf; l ∈ lfs; ls, walLockHI (GF := GF) lf l.1 l.2) ∗ osLock (GF := GF) k i fd' ∗
        fileutil.lockKind (GF := GF) k ⊢
      ([∗list] lf; l ∈ lfs; ls, walLockHI (GF := GF) lf l.1 l.2) ∗ osLock (GF := GF) k i fd' ∗
        ⌜∀ l ∈ ls, l.2 ≠ i⌝ := by
  induction lfs generalizing ls with
  | nil =>
    iintro ⟨H, Hl, -⟩
    ihave %h := BigSepL2.bigSepL2_length $$ H
    cases ls with
    | nil => iframe; ipureintro; simp
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ls with
    | nil => iintro ⟨H, -⟩; ihave %h := BigSepL2.bigSepL2_length $$ H; simp at h
    | cons l ls =>
      iintro ⟨⟨Hx, Hxs⟩, Hl, #Hk⟩
      ihave ⟨Hx, Hl, %h1⟩ := walLockHI_excl x l.1 l.2 i k fd' $$ [Hx Hl]
      · iframe; iexact Hk
      ihave ⟨Hxs, Hl, %h2⟩ := ih ls $$ [Hxs Hl]
      · iframe; iexact Hk
      iframe Hl
      isplitl [Hx Hxs]
      · iapply (BigSepL2.bigSepL2_cons (PROP := IProp GF)).2
        iframe
      ipureintro
      intro l' hl'
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact h1
      · exact h2 l' hl'

/-- **The purge's bound on the handle's side**: with a purger's lock on `i`, a `.wal` name `nm` of the
directory at `i` (not the tail's), its sequence `sq`, ends at or before the registered range's start
`b` (`walTailsFrag`'s, which the invariant bounds by `unl`: `walLks_agree`). Stated on `walDirLks`
unfolded, `b` exposed. -/
theorem walDirLks_purge (dir : GoString) (hj : NamesH) (nm0 : GoString) (lfs : List Loc)
    (cuts : List Nat) (i : Ino) (k : LockKind) (fd' : w64) (nm : GoString) (sq ix : Nat)
    (hc : cuts.Pairwise (· < ·)) (hn : hj.cur !! nm = some (.file i)) (hw : walNameP nm = true)
    (h0 : nm ≠ nm0) (hnm : nm = walFileName sq ix) (hsq : sq < 2 ^ 64) :
    walDirLks (W := W) dir hj nm0 lfs cuts ∗ osLock (GF := GF) k i fd' ∗
        fileutil.lockKind (GF := GF) k ⊢
      ∃ (γt : GName) (b : Nat) (ls : List (GoString × Ino)),
        walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName))
            (<[dir := b]> (∅ : GMap GoString Nat)) ∗
          ([∗list] lf; l ∈ lfs; ls, walLockHI (GF := GF) lf l.1 l.2) ∗ ⌜LkRel hj cuts nm0 ls b⌝ ∗
          osLock (GF := GF) k i fd' ∗ ⌜sq + 1 ≤ cuts.length - ls.length ∧ segStart cuts (sq + 1) ≤ b⌝ := by
  unfold walDirLks
  iintro ⟨⟨%γt, %b, %ls, Htf, Hls, %hr⟩, Hl, #Hk⟩
  ihave ⟨Hls, Hl, %hx⟩ := walLocksHI_excl lfs ls i k fd' $$ [Hls Hl]
  · iframe; iexact Hk
  iexists γt, b, ls
  iframe
  ipureintro
  refine ⟨hr, LkRel_purge hr hc hn hw h0 ?_ hnm hsq⟩
  intro hm
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem hl
  have := (hr.2.2.2.1 k' l hk').1
  rw [hn] at this
  cases this
  exact hx l hl rfl

end iris

end WalFs
end EtcdGrove
end Perennial

end
