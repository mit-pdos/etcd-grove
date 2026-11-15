/- Lean-first (no Rocq counterpart).

# The handle's locked range (unit `locks`, session 5; `notes/wal-units/locks.md`)

The handle's half of the tie between its locks and the invariant's `unl` (`LkRel`, `walDirLks`,
`Handle.lean`): how `cut`, `ReleaseLockTo` and `Close` move it.

* `LkRel_cut`, `walDirLks_cut`: `cut` makes the old tail a non-tail lock and the renamed segment the
  tail (one more cut; the old names keep their starts, `segStart_snoc`).
* `walLockHI_ofTail`: the old tail, a writable locked description (`fdLocksW`), as a `walLockHI`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutLay
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- Two segment names whose sequence numbers differ (both below `2 ^ 64`) differ. -/
theorem walFileName_ne_of_seq {a b ix ix' : Nat} (hab : a ≠ b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    walFileName a ix ≠ walFileName b ix' := by
  intro h
  have := walFileName_seq_mod h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact hab this

/-- **`cut`'s step on the locked range**: the old tail `nm0` (inode `ino`) becomes the last non-tail lock,
the renamed segment `bt` (sequence one more) the tail, one more cut. -/
theorem LkRel_cut {hj hj' : NamesH} {cuts : List Nat} {nm0 bt : GoString} {ls : List (GoString × Ino)}
    {b c : Nat} {ino i' : Ino} {ix' : Nat}
    (h : LkRel hj cuts nm0 ls b) (hnm0 : hj.cur !! nm0 = some (.file ino))
    (hbt : bt = walFileName (cuts.length + 1) ix') (hlt : cuts.length + 1 < 2 ^ 64)
    (hj'c : hj'.cur = <[bt := .file i']> hj.cur) :
    LkRel hj' (cuts ++ [c]) bt (ls ++ [(nm0, ino)]) b := by
  obtain ⟨h1, h2, ⟨ix0, h3⟩, h4, h5, h6⟩ := h
  have hne0 : bt ≠ nm0 := by
    rw [hbt, h3]; exact walFileName_ne_of_seq (by omega) hlt (by omega)
  have hnel : ∀ (k : Nat) (l : GoString × Ino), ls[k]? = some l → bt ≠ l.1 := by
    intro k l hk
    obtain ⟨-, ix, hix⟩ := h4 k l hk
    have hk' : k < ls.length := (List.getElem?_eq_some_iff.1 hk).1
    rw [hbt, hix]; exact walFileName_ne_of_seq (by omega) hlt (by omega)
  unfold LkRel
  simp only [List.length_append, List.length_singleton]
  refine ⟨by omega, by omega, ⟨ix', hbt⟩, fun k l hk => ?_, fun nm n hn hw hnb hnl => ?_, ?_⟩
  · rcases Nat.lt_or_ge k ls.length with hk' | hk'
    · rw [List.getElem?_append_left hk'] at hk
      obtain ⟨hl1, ix, hix⟩ := h4 k l hk
      refine ⟨by rw [hj'c, GMap.lookup_insert_ne _ _ (hnel k l hk)]; exact hl1, ix, ?_⟩
      rw [hix]; congr 1; omega
    · rw [List.getElem?_append_right hk'] at hk
      have hk0 : k - ls.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hk).1
        simp only [List.length_singleton] at this; omega
      rw [hk0] at hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨by rw [hj'c, GMap.lookup_insert_ne _ _ hne0]; exact hnm0, ix0, ?_⟩
      rw [h3]; show walFileName _ ix0 = _; congr 1; omega
  · have hnb' : bt ≠ nm := fun e => hnb e.symm
    rw [hj'c, GMap.lookup_insert_ne _ _ hnb'] at hn
    have hn0 : nm ≠ nm0 := by
      rintro rfl; exact hnl (by simp)
    have hnl' : nm ∉ ls.map (·.1) := by
      intro hm; exact hnl (by simp only [List.map_append, List.mem_append]; exact Or.inl hm)
    obtain ⟨sq, ix, e, hsq⟩ := h5 nm n hn hw hn0 hnl'
    exact ⟨sq, ix, e, by omega⟩
  · rw [show cuts.length + 1 - (ls.length + 1) = cuts.length - ls.length by omega,
      segStart_snoc (by omega)]
    exact h6

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- A writable description's `fdLocksW`: its `fdLocks`, and an exclusive lock held. -/
theorem fdLocksW_excl (fd : w64) (d : OsFd) (hw : d.writable = true) :
    fdLocksW (GF := GF) fd d ⊢ fdLocks fd d ∗ ⌜∃ k, d.lk k = some true⌝ := by
  unfold fdLocksW
  iintro ⟨H, %hh⟩
  iframe H
  ipureintro
  rcases hh hw with h | h
  · exact ⟨.ofd, h⟩
  · exact ⟨.flock, h⟩

/-- **The old tail as a non-tail lock** (`cut`): its lock, its file at `child pd bn` (`bn` a segment's
name), its writable locked description on `i`. -/
theorem walLockHI_ofTail (lf f : Loc) (fd : w64) (pd bn : GoString) (i : Ino) (rd : Bool)
    (lo lk : Option Bool) (sq ix : Nat) (hbn : bn = walFileName sq ix) :
    fileutil.lockedFile lf f ∗ os.ownFile f fd (child pd bn) (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨i, rd, true, lo, lk⟩ ∗ fdLocksW fd ⟨i, rd, true, lo, lk⟩ ⊢
    walLockHI (GF := GF) lf bn i := by
  iintro ⟨#Hl, Hf, Hfd, Hk⟩
  ihave ⟨Hk, %hk⟩ := fdLocksW_excl fd _ rfl $$ Hk
  unfold walLockHI
  iexists f, fd, pd, ⟨i, rd, true, lo, lk⟩
  iframe Hl Hf Hfd Hk
  ipureintro
  exact ⟨⟨pd, sq, ix, by rw [hbn]⟩, rfl, hk⟩

/-- **`cut`'s step on the handle's locks**: the old tail's lock appended to the non-tail locks, the
renamed segment the tail, one more cut. -/
theorem walDirLks_cut (dir : GoString) (hj hj' : NamesH) (nm0 bt : GoString) (ls : List Loc) (lt : Loc)
    (cuts : List Nat) (c : Nat) (ino i' : Ino) (sq ix ix' : Nat)
    (hnm0 : hj.cur !! nm0 = some (.file ino)) (hnm0s : nm0 = walFileName sq ix) (hsq : sq + 1 < 2 ^ 64)
    (hbt : bt = walFileName (sq + 1) ix')
    (hj'c : hj'.cur = <[bt := .file i']> hj.cur) :
    walDirLks (W := W) dir hj nm0 ls cuts ∗ walLockHI (GF := GF) lt nm0 ino ⊢
      walDirLks (W := W) dir hj' bt (ls ++ [lt]) (cuts ++ [c]) := by
  unfold walDirLks
  iintro ⟨⟨%γt, %b, %lsI, Htf, Hls, %hr⟩, Hlt⟩
  iexists γt, b, lsI ++ [(nm0, ino)]
  iframe Htf
  isplitl [Hls Hlt]
  · iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).2
    iframe Hls Hlt
  ipureintro
  obtain ⟨-, hcl, ⟨ix0, h3⟩, -⟩ := id hr
  have hm := walFileName_seq_mod (hnm0s.symm.trans h3)
  rw [Nat.mod_eq_of_lt (by omega : sq < 2 ^ 64), Nat.mod_eq_of_lt hcl] at hm
  subst hm
  exact LkRel_cut hr hnm0 hbt (by omega) hj'c

end iris

end WalFs
end EtcdGrove
end Perennial

end
