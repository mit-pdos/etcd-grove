/- Lean-first (no Rocq counterpart).

# The handle's locked range (unit `locks`, session 5; `notes/wal-units/locks.md`)

The handle's half of the tie between its locks and the invariant's `unl` (`LkRel`, `walDirLks`,
`Handle.lean`): how `cut`, `ReleaseLockTo` and `Close` move it.

* `LkRel_cut`, `walDirLks_cut`: `cut` makes the old tail a non-tail lock and the renamed segment the
  tail (one more cut; the old names keep their starts, `segStart_snoc`).
* `walLockHI_ofTail`: the old tail, a writable locked description (`fdLocksW`), as a `walLockHI`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutLay
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReleasePos
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtTail

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

/-- `%016x` is injective modulo `2 ^ 64`. -/
theorem hex16_inj {a b : Nat} (h : hex16 a = hex16 b) : a % 2 ^ 64 = b % 2 ^ 64 := by
  rw [hex16_mod a, hex16_mod b, hex16_hexPad, hex16_hexPad] at h
  have h16 : ∀ n, n % 2 ^ 64 < 16 ^ 16 := fun n => lt_of_lt_of_eq (Nat.mod_lt _ (by decide)) (by decide)
  rcases Nat.lt_trichotomy (a % 2 ^ 64) (b % 2 ^ 64) with hl | he | hl
  · have := hexPad_lt 16 _ _ hl (h16 b); rw [h] at this; exact absurd this (go.goStringLt_irrefl _)
  · exact he
  · have := hexPad_lt 16 _ _ hl (h16 a); rw [h] at this; exact absurd this (go.goStringLt_irrefl _)

/-- **Equal segment names**: equal sequence numbers and indices, modulo `2 ^ 64`. -/
theorem walFileName_inj {a b ix ix' : Nat} (h : walFileName a ix = walFileName b ix') :
    a % 2 ^ 64 = b % 2 ^ 64 ∧ ix % 2 ^ 64 = ix' % 2 ^ 64 := by
  refine ⟨walFileName_seq_mod h, ?_⟩
  unfold walFileName at h
  have hl : ∀ n, (hex16 n).length = 16 := fun n => by simp [hex16]
  simp only [List.append_assoc] at h
  have h1 := List.append_inj h (by rw [hl, hl])
  have h2 := List.append_inj h1.2 (by rfl)
  have h3 := List.append_inj h2.2 (by rw [hl, hl])
  exact hex16_inj h3.1

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

/-- A segment start past the first segment is a cut of the layout, a cut position of the history, at
most its length. -/
theorem absD_segStart_cut {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) {k : Nat} (hk0 : 0 < k) (hk : k ≤ lay.cuts.length) :
    walCutPos (histM d) (segStart lay.cuts k) ∧ segStart lay.cuts k ≤ d.H.length := by
  have hmem : segStart lay.cuts k ∈ lay.cuts := by
    unfold segStart
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  have hc := h.cuts.1 _ hmem
  refine ⟨hc, ?_⟩
  rcases hc with h0 | ⟨hh, es, hb, -⟩ | ⟨m, al, hb⟩
  · omega
  · have := (List.getElem?_eq_some_iff.1 hb).1
    simp only [histM, histN_length, List.length_map] at this; omega
  · have := (List.getElem?_eq_some_iff.1 hb).1
    simp only [histM, histN_length, List.length_map] at this; omega

/-- **The first read segment starts at or before `walOpenPos`** (`ReadAll`'s registration): the segments
from `kk` on, the first named at most `a`. -/
theorem absD_segStart_le_openPos {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (h : WalAbsD C Mr d lay ents) {kk : Nat} {gs : List SegG} (hgs : lay.segs.drop kk = gs)
    (hne : gs ≠ []) {a : w64}
    (hhd : ∀ g, gs.head? = some g → ∀ sq ix : Nat, g.name = walFileName sq ix → ix < 2 ^ 64 →
      ix ≤ uint.nat a) :
    segStart lay.cuts (lay.first + kk) ≤ walOpenPos (histM d) a := by
  obtain ⟨g, hg⟩ : ∃ g, lay.segs[kk]? = some g := by
    cases e : lay.segs[kk]? with
    | none => rw [List.getElem?_eq_none_iff] at e; rw [List.drop_eq_nil_of_le e] at hgs; exact absurd hgs.symm hne
    | some g => exact ⟨g, rfl⟩
  have hkk : kk < lay.segs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hhead : gs.head? = some g := by rw [← hgs, List.head?_drop]; exact hg
  obtain ⟨sq, ix, hn, hix, hb⟩ := h.nameBound kk g hg
  have hia := hhd g hhead sq ix hn hix
  have hcl := h.cuts.2.2
  apply cutStart_le_openPos (ix := ix)
  rcases Nat.eq_zero_or_pos (lay.first + kk) with h0 | h0
  · left; rw [h0]; rfl
  · right
    obtain ⟨hcp, hle⟩ := absD_segStart_cut h h0 (by omega)
    exact ⟨hcp, by simpa [histM] using hle, hb h0, hia⟩

/-- **`ReadAll`'s locked range**: the segments from `kk` on locked (the last the tail), the range registered at
the first one's start. -/
theorem LkRel_read {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {hj : NamesH} {kk : Nat}
    {gs0 : List SegG} {gl : SegG} (h : WalAbsD C Mr d lay hj.cur) (hsn : SegsNamed lay.segs hj.cur)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hgs : lay.segs.drop kk = gs0 ++ [gl])
    (hcl : lay.cuts.length < 2 ^ 64) :
    LkRel hj lay.cuts gl.name (gs0.map (fun g => (g.name, g.ino))) (segStart lay.cuts (lay.first + kk)) := by
  have hlen : lay.segs.length = kk + gs0.length + 1 := by
    have := congrArg List.length hgs
    simp only [List.length_drop, List.length_append, List.length_singleton] at this
    have hkk : kk < lay.segs.length := by
      rcases Nat.lt_or_ge kk lay.segs.length with h1 | h1
      · exact h1
      · rw [List.drop_eq_nil_of_le h1] at hgs; simp at hgs
    omega
  have hc := h.cuts.2.2
  have hfk : lay.first + kk = lay.cuts.length - gs0.length := by omega
  have hseg : ∀ k, lay.segs[kk + k]? = (gs0 ++ [gl])[k]? := by
    intro k; rw [← hgs, List.getElem?_drop]
  have hlg : lay.segs.getLast? = some gl := by
    rw [List.getLast?_eq_getElem?, show lay.segs.length - 1 = kk + gs0.length by omega, hseg]
    simp
  simp only [LkRel, List.length_map]
  refine ⟨by omega, hcl, (h.tailSeq gl hlg).1, fun k l hk => ?_, fun nm n hn hw hne hnl => ?_, ?_⟩
  · rw [List.getElem?_map] at hk
    cases hgk : gs0[k]? with
    | none => rw [hgk] at hk; cases hk
    | some g =>
      rw [hgk] at hk; simp only [Option.map_some, Option.some.injEq] at hk; subst hk
      have hk' : k < gs0.length := (List.getElem?_eq_some_iff.1 hgk).1
      have hsg : lay.segs[kk + k]? = some g := by
        rw [hseg, List.getElem?_append_left hk']; exact hgk
      refine ⟨(hsn.1 g (List.mem_of_getElem? hsg)).2, ?_⟩
      obtain ⟨ix, hix⟩ := h.seqName (kk + k) g hsg
      exact ⟨ix, by rw [hix, ← Nat.add_assoc, hfk]⟩
  · obtain ⟨g', hg', rfl⟩ := walName_seg hsn h.names.1 hnd hw hn
    obtain ⟨k', hk'⟩ := List.getElem?_of_mem hg'
    rcases Nat.lt_or_ge k' kk with hlt | hge
    · obtain ⟨ix, hix⟩ := h.seqName k' g' hk'
      exact ⟨lay.first + k', ix, hix, by omega⟩
    · exfalso
      have e : lay.segs[kk + (k' - kk)]? = some g' := by rw [show kk + (k' - kk) = k' by omega]; exact hk'
      rw [hseg] at e
      rcases Nat.lt_or_ge (k' - kk) gs0.length with h1 | h1
      · rw [List.getElem?_append_left h1] at e
        exact hnl (List.mem_map.2 ⟨(g'.name, g'.ino), List.mem_map.2 ⟨g', List.mem_of_getElem? e, rfl⟩, rfl⟩)
      · rw [List.getElem?_append_right h1] at e
        have : k' - kk - gs0.length = 0 := by
          have := (List.getElem?_eq_some_iff.1 e).1; simp at this; omega
        rw [this] at e; simp at e; subst e; exact hne rfl
  · exact Nat.le_of_eq (by rw [hfk])

/-- **The handle's lock names** (the non-tail locks' then the tail's): each a segment's name at its
sequence, present in the directory. -/
theorem LkRel_names {hj : NamesH} {cuts : List Nat} {nm0 : GoString} {ls : List (GoString × Ino)} {b : Nat}
    {ino : Ino} (h : LkRel hj cuts nm0 ls b) (hnm0 : hj.cur !! nm0 = some (.file ino)) :
    ∀ k bn, (ls.map (·.1) ++ [nm0])[k]? = some bn →
      ∃ ix n, bn = walFileName (cuts.length - ls.length + k) ix ∧ hj.cur !! bn = some n := by
  intro k bn hk
  obtain ⟨h1, -, ⟨ix0, h3⟩, h4, -⟩ := h
  rcases Nat.lt_or_ge k ls.length with hlt | hge
  · rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_map] at hk
    cases hl : ls[k]? with
    | none => rw [hl] at hk; cases hk
    | some l =>
      rw [hl] at hk; simp only [Option.map_some, Option.some.injEq] at hk; subst hk
      obtain ⟨hl1, ix, hix⟩ := h4 k l hl
      exact ⟨ix, _, hix, hl1⟩
  · rw [List.getElem?_append_right (by simpa using hge)] at hk
    have hk0 : k - ls.length = 0 := by
      have := (List.getElem?_eq_some_iff.1 hk).1
      simp only [List.length_map, List.length_singleton] at this; omega
    simp only [List.length_map, hk0, List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    exact ⟨ix0, _, by rw [h3]; congr 1; omega, hnm0⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **A lock's file, named `child pd bn`** (a segment's name; persistent): what `ReleaseLockTo`'s name loop
reads (`l.Name()`, `filepath.Base`). -/
def walLockBase (lf : Loc) (bn : GoString) : IProp GF :=
  iprop(∃ (f : Loc) (pd : GoString), fileutil.lockedFile lf f ∗ os.fileNamed f (child pd bn) ∗
    ⌜walSegName (child pd bn)⌝)

instance walLockBase_persistent (lf : Loc) (bn : GoString) : Persistent (walLockBase (GF := GF) lf bn) := by
  unfold walLockBase; infer_instance

theorem walLockHI_base (lf : Loc) (bn : GoString) (i : Ino) :
    walLockHI (GF := GF) lf bn i ⊢ walLockHI lf bn i ∗ walLockBase lf bn := by
  unfold walLockHI walLockBase
  iintro ⟨%f, %fd, %pd, %d, #Hl, Hf, Hfd, Hk, %h⟩
  ihave #Hn := os.ownFile_named f fd (child pd bn) (DFrac.own 1) $$ Hf
  isplitl [Hf Hfd Hk]
  · iexists f, fd, pd, d; iframe Hl Hf Hfd Hk; ipureintro; exact h
  · iexists f, pd; iframe Hl Hn; ipureintro; exact h.1

theorem walLocksHI_base (lfs : List Loc) (ls : List (GoString × Ino)) :
    ([∗list] lf; l ∈ lfs; ls, walLockHI (GF := GF) lf l.1 l.2) ⊢
      ([∗list] lf; l ∈ lfs; ls, walLockHI (GF := GF) lf l.1 l.2) ∗
        □ [∗list] lf; bn ∈ lfs; ls.map (·.1), walLockBase (GF := GF) lf bn := by
  induction lfs generalizing ls with
  | nil =>
    cases ls with
    | nil =>
      iintro H; iframe H; imodintro
      simp only [List.map_nil]
      iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
    | cons l ls => iintro H; ihave %h := BigSepL2.bigSepL2_length $$ H; simp at h
  | cons x xs ih =>
    cases ls with
    | nil => iintro H; ihave %h := BigSepL2.bigSepL2_length $$ H; simp at h
    | cons l ls =>
      iintro ⟨Hx, Hxs⟩
      ihave ⟨Hx, #Hbx⟩ := walLockHI_base x l.1 l.2 $$ Hx
      ihave ⟨Hxs, #Hbxs⟩ := ih ls $$ Hxs
      iframe Hx Hxs
      imodintro
      simp only [List.map_cons]
      iapply (BigSepL2.bigSepL2_cons (PROP := IProp GF)).2
      iframe Hbx Hbxs

/-- **The first `m` locks as `walLockH`s, the rest kept.** -/
theorem walLocksHI_split (m : Nat) (lfs : List Loc) (ls : List (GoString × Ino)) :
    ([∗list] lf; l ∈ lfs; ls, walLockHI (GF := GF) lf l.1 l.2) ⊢
      ([∗list] lf ∈ lfs.take m, walLockH (GF := GF) lf) ∗
        [∗list] lf; l ∈ lfs.drop m; ls.drop m, walLockHI (GF := GF) lf l.1 l.2 := by
  induction m generalizing lfs ls with
  | zero =>
    iintro H
    simp only [List.take_zero, List.drop_zero]
    iframe H
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | succ m ih =>
    cases lfs with
    | nil =>
      iintro H
      simp only [List.take_nil, List.drop_nil]
      cases ls with
      | nil =>
        isplitr
        · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
        · simp only [List.drop_nil]; iexact H
      | cons l ls => ihave %h := BigSepL2.bigSepL2_length $$ H; simp at h
    | cons x xs =>
      cases ls with
      | nil => iintro H; ihave %h := BigSepL2.bigSepL2_length $$ H; simp at h
      | cons l ls =>
        iintro ⟨Hx, Hxs⟩
        ihave ⟨Ht, Hd⟩ := ih xs ls $$ Hxs
        simp only [List.take_succ_cons, List.drop_succ_cons]
        iframe Hd
        iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
        iframe Ht
        iapply walLockHI_H $$ Hx

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
