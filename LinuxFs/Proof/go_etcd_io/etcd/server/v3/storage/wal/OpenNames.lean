/- Lean-first (no Rocq counterpart).

# The names `Open` reads (W3/W5 of `notes/wal-fsext-plan.md`; pure)

`openAtIndex` calls `selectWALFiles` over the program's half of the WAL directory's claim
`(lay.j, .except X, hj)`; its premise `WalDirNamesOk` (every `.wal` name of the claim, and those
present named `fmt.walNameStr s i`) follows from the invariant's facts on the layout:

* `walFileName_walNameStr`: a segment's name (`walFileName sq ix`, `Abs.lean`) is the `fmt` model's
  `fmt.walNameStr` of the 64-bit truncations (`hex16 = fmt.hexPad 16`, which keeps the last 16 digits).
* `walName_unique`: two `.wal` names of a directory holding the same file are the same name, when the
  directory's `.wal` files are distinct (`walInos` without duplicates).
* `walName_seg`: a `.wal` name present is a segment's; `walNamesOut_segs`: the names `readWALNames`
  returns (`WalNamesOut`) are the segments' names, in order; `walOpenNames_ok`: `openWALFiles`' premise
  on the names from the selected position.
* `walDirNamesOk_of`: from `SegsNamed` (`WalsNamed`), `WalAbsD.names` and `nameBound`, and the
  segments' inodes distinct (`WalsOk`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

theorem hexDigit_eq (x : Nat) (h : x < 16) : hexDigit x = _root_.Perennial.fmt.hexDigitByte x := by
  have : ∀ y, y < 16 → hexDigit y = _root_.Perennial.fmt.hexDigitByte y := by decide
  exact this x h

/-- `fmt.hexPad w n` keeps `n`'s last `w` digits. -/
theorem hexPad_mod (w n : Nat) : fmt.hexPad w n = fmt.hexPad w (n % 16 ^ w) := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    simp only [fmt.hexPad]
    rw [ih (n / 16), ih (n % 16 ^ (w + 1) / 16)]
    have e1 : n % 16 ^ (w + 1) / 16 = n / 16 % 16 ^ w := by
      rw [Nat.pow_succ', Nat.mod_mul_right_div_self]
    have e2 : n % 16 ^ (w + 1) % 16 = n % 16 :=
      Nat.mod_mod_of_dvd n ⟨16 ^ w, by rw [Nat.pow_succ']⟩
    rw [e1, e2, Nat.mod_mod]

/-- The digits of `hex16` as `fmt.hexPad`'s (any width). -/
theorem hexDigits_hexPad (w n : Nat) :
    ((List.range w).reverse).map (fun i => hexDigit (n / 16 ^ i % 16)) = fmt.hexPad w n := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    rw [List.range_succ_eq_map, List.reverse_cons, List.map_append, ← List.map_reverse, List.map_map]
    simp only [fmt.hexPad, List.map_cons, List.map_nil]
    rw [← ih (n / 16)]
    congr 1
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    · simp only [Nat.pow_zero, Nat.div_one]
      rw [hexDigit_eq _ (Nat.mod_lt _ (by decide))]

theorem hex16_hexPad (n : Nat) : hex16 n = fmt.hexPad 16 n := hexDigits_hexPad 16 n

/-- **A segment's name is `fmt.walNameStr`'s** (the truncations to 64 bits). -/
theorem walFileName_walNameStr (sq ix : Nat) :
    walFileName sq ix = fmt.walNameStr (BitVec.ofNat 64 sq) (BitVec.ofNat 64 ix) := by
  unfold walFileName fmt.walNameStr
  have h64 : (2 : Nat) ^ 64 = 16 ^ 16 := by decide
  have hs : uint.nat (BitVec.ofNat 64 sq) = sq % 16 ^ 16 := by
    rw [← h64]; exact BitVec.toNat_ofNat sq 64
  have hi : uint.nat (BitVec.ofNat 64 ix) = ix % 16 ^ 16 := by
    rw [← h64]; exact BitVec.toNat_ofNat ix 64
  rw [hs, hi, hex16_hexPad, hex16_hexPad, ← hexPad_mod, ← hexPad_mod]
  generalize fmt.hexPad 16 sq = A
  generalize fmt.hexPad 16 ix = B
  simp only [List.append_assoc]
  rfl

private theorem walNames_nodup (E : Ents) : (walNames E).Nodup := by
  unfold walNames
  refine (List.mergeSort_perm _ _).nodup_iff.2 (List.Nodup.sublist (List.filter_sublist) ?_)
  exact GMap.toList_keys_nodup E

private theorem mem_walNames {E : Ents} {b : GoString} {e : Node} (hb : walNameP b = true)
    (he : E !! b = some e) : b ∈ walNames E := by
  unfold walNames
  refine (List.mergeSort_perm _ _).mem_iff.2 (List.mem_filter.2 ⟨?_, hb⟩)
  exact List.mem_map.2 ⟨(b, e), (GMap.mem_toList _ _ _).2 he, rfl⟩

/-- **Two `.wal` names holding the same file are one**, the directory's `.wal` files distinct. -/
theorem walName_unique {E : Ents} {b b' : GoString} {i : Ino} (hb : walNameP b = true)
    (hb' : walNameP b' = true) (he : E !! b = some (.file i)) (he' : E !! b' = some (.file i))
    (hnd : (walInos E).Nodup) : b = b' := by
  refine Classical.byContradiction fun hne => ?_
  have hm : b ∈ walNames E := mem_walNames hb he
  have hm' : b' ∈ (walNames E).erase b := (List.mem_erase_of_ne (Ne.symm hne)).2 (mem_walNames hb' he')
  have hp : List.Perm (walNames E) (b :: b' :: ((walNames E).erase b).erase b') :=
    (List.perm_cons_erase hm).trans (List.Perm.cons _ (List.perm_cons_erase hm'))
  have hp' := hp.filterMap (fun b => match E !! b with
    | some (.file i) => some i
    | _ => none)
  have hnd' := hp'.nodup_iff.1 hnd
  simp only [List.filterMap_cons, he, he'] at hnd'
  exact (List.nodup_cons.1 hnd').1 (List.mem_cons_self ..)

/-- **A `.wal` name present in the directory is a segment's.** -/
theorem walName_seg {hj : NamesH} {segs : List SegG} {b : GoString} {e : Node}
    (hsn : SegsNamed segs hj.cur)
    (hnames : walInos hj.cur = segs.map (·.ino)) (hnd : (segs.map (·.ino)).Nodup)
    (hbw : walNameP b = true) (he : hj.cur !! b = some e) : ∃ g ∈ segs, b = g.name := by
  obtain ⟨i, rfl⟩ := hsn.2 b e hbw he
  have hi : i ∈ walInos hj.cur := by
    unfold walInos
    refine List.mem_filterMap.2 ⟨b, mem_walNames hbw he, by rw [he]⟩
  rw [hnames] at hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hgw, hge⟩ := hsn.1 g hg
  exact ⟨g, hg, walName_unique hbw hgw he hge (by rw [hnames]; exact hnd)⟩

/-- **The names `readWALNames` returns are the segments'**, in order. -/
theorem walNamesOut_segs {X : List GoString} {hj : NamesH} {segs : List SegG} {ws : List GoString}
    (hX : ∀ b ∈ X, walNameP b = false) (hsn : SegsNamed segs hj.cur)
    (hnames : walInos hj.cur = segs.map (·.ino)) (hnd : (segs.map (·.ino)).Nodup)
    (hsort : (segs.map (·.name)).Pairwise (fun a b => go.GoStringLt a b))
    (hnm : ∀ g ∈ segs, ∃ sq ix : Nat, g.name = walFileName sq ix)
    (hout : WalNamesOut (.except X) hj ws) : ws = segs.map (·.name) := by
  obtain ⟨-, hle, hok, hsome, hall, hcnt⟩ := hout
  have hmem : ∀ b, walNameP b = true → (NameSet.except X).Mem b := fun b hb hbX => by
    rw [hX b hbX] at hb; cases hb
  have hwsw : ∀ b ∈ ws, walNameP b = true := fun b hb => by
    unfold walNameP; exact decide_eq_true (hok b hb).2.1
  have hndw : ws.Nodup := by
    refine List.nodup_iff_count.2 fun b => ?_
    by_cases hb : b ∈ ws
    · exact hcnt b (hmem b (hwsw b hb))
    · rw [List.count_eq_zero_of_not_mem hb]; omega
  have hnds : (segs.map (·.name)).Nodup :=
    hsort.imp (fun {a b} h hab => by subst hab; exact go.goStringLt_irrefl _ h)
  refine List.Perm.eq_of_pairwise (le := go.GoStringLe) ?_ hle (hsort.imp Or.inr) ?_
  · intro a b _ _ h1 h2
    rcases h1 with h1 | h1
    · exact h1
    rcases h2 with h2 | h2
    · exact h2.symm
    exact absurd h2 (go.goStringLt_asymm h1)
  refine (List.perm_ext_iff_of_nodup hndw hnds).2 fun b => ⟨fun hb => ?_, fun hb => ?_⟩
  · have hbw := hwsw b hb
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (hsome b (hmem b hbw) hb)
    obtain ⟨g, hg, rfl⟩ := walName_seg hsn hnames hnd hbw he
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hb
    obtain ⟨hgw, hge⟩ := hsn.1 g hg
    refine hall _ (hmem _ hgw) (by rw [hge]; rfl) ?_
    obtain ⟨sq, ix, hn⟩ := hnm g hg
    refine ⟨of_decide_eq_true hgw, BitVec.ofNat 64 sq, BitVec.ofNat 64 ix, ?_⟩
    rw [hn, walFileName_walNameStr]
    exact fmt.scanWalName_walNameStr _ _

theorem walFileName_length (sq ix : Nat) : (walFileName sq ix).length = 37 := by
  simp [walFileName, hex16]

/-- **`openWALFiles`' premise on the names from the selected position**: each is a name of the
claim, a valid name, short, holding the segment's file. -/
theorem walOpenNames_ok {X : List GoString} {hj : NamesH} {segs : List SegG} {ws : List GoString}
    (k : Nat) (hX : ∀ b ∈ X, walNameP b = false) (hsn : SegsNamed segs hj.cur)
    (hnm : ∀ g ∈ segs, ∃ sq ix : Nat, g.name = walFileName sq ix)
    (hout : WalNamesOut (.except X) hj ws) (hws : ws = segs.map (·.name)) :
    ∀ (m : Nat) (b : GoString) (i : Ino), (ws.drop k)[m]? = some b →
      ((segs.map (·.ino)).drop k)[m]? = some i →
      (NameSet.except X).Mem b ∧ NameOk b ∧ b.length < 2 ^ 60 ∧ hj.cur !! b = some (.file i) := by
  intro m b i hb hi
  have hbm : b ∈ ws := List.mem_of_mem_drop (List.mem_of_getElem? hb)
  rw [hws, List.getElem?_drop, List.getElem?_map] at hb
  rw [List.getElem?_drop, List.getElem?_map] at hi
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hi
  rw [hg] at hg'; cases hg'
  have hgm : g ∈ segs := List.mem_of_getElem? hg
  obtain ⟨hgw, hge⟩ := hsn.1 g hgm
  obtain ⟨sq, ix, hn⟩ := hnm g hgm
  refine ⟨fun hbX => ?_, (hout.2.2.1 _ hbm).1, ?_, hge⟩
  · rw [hX _ hbX] at hgw; cases hgw
  · rw [hn, walFileName_length]; decide

/-- **`selectWALFiles`' premise from the layout's facts** (see the file header). -/
theorem walDirNamesOk_of {X : List GoString} {hj : NamesH} {segs : List SegG}
    (hX : ∀ b ∈ X, walNameP b = false) (hsn : SegsNamed segs hj.cur)
    (hnames : walInos hj.cur = segs.map (·.ino)) (hnd : (segs.map (·.ino)).Nodup)
    (hnm : ∀ g ∈ segs, ∃ sq ix : Nat, g.name = walFileName sq ix) :
    WalDirNamesOk (.except X) hj := by
  intro b hsuf
  have hbw : walNameP b = true := by unfold walNameP; exact decide_eq_true hsuf
  refine ⟨fun hbX => (by rw [hX b hbX] at hbw; cases hbw), fun hs => ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨i, rfl⟩ := hsn.2 b e hbw he
  have hi : i ∈ walInos hj.cur := by
    unfold walInos
    refine List.mem_filterMap.2 ⟨b, mem_walNames hbw he, by rw [he]⟩
  rw [hnames] at hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
  obtain ⟨hgw, hge⟩ := hsn.1 g hg
  have := walName_unique hbw hgw he hge (by rw [hnames]; exact hnd)
  subst this
  obtain ⟨sq, ix, hn⟩ := hnm g hg
  exact ⟨_, _, by rw [hn, walFileName_walNameStr]⟩

end pure

end WalFs
end EtcdGrove
end Perennial
