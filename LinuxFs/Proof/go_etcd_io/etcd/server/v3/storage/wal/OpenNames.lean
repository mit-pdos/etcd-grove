/- Lean-first (no Rocq counterpart).

# The names `Open` reads (W3/W5 of `notes/wal-fsext-plan.md`; pure)

`openAtIndex` calls `selectWALFiles` over the program's half of the WAL directory's claim
`(lay.j, .except X, hj)`; its premise `WalDirNamesOk` (every `.wal` name of the claim, and those
present named `fmt.walNameStr s i`) follows from the invariant's facts on the layout:

* `walFileName_walNameStr`: a segment's name (`walFileName sq ix`, `Abs.lean`) is the `fmt` model's
  `fmt.walNameStr` of the 64-bit truncations (`hex16 = fmt.hexPad 16`, which keeps the last 16 digits).
* `walName_unique`: two `.wal` names of a directory holding the same file are the same name, when the
  directory's `.wal` files are distinct (`walInos` without duplicates).
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

theorem walNames_nodup (E : Ents) : (walNames E).Nodup := by
  unfold walNames
  refine (List.mergeSort_perm _ _).nodup_iff.2 (List.Nodup.sublist (List.filter_sublist) ?_)
  exact GMap.toList_keys_nodup E

theorem mem_walNames {E : Ents} {b : GoString} {e : Node} (hb : walNameP b = true)
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
