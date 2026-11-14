/- Lean-first (no Rocq counterpart).

# A growth of the tail (I3b, `wal-tc11`; pure)

`ReadAll`'s `ZeroToEnd` truncates the tail to its write position `wr` (`os.File.Truncate.specWalTail`'s
pieces: `rzSeg … true wr`, `rzLand`), then grows it back to the size it had (`fallocate`, or the
fallback's truncate past the size). Here the growth's pieces, as the truncate's (`WinCrashW.lean`,
`RzLand.lean`, `RzWals.lean`):

* its first step, `rzSeg g0 tr tg n` with `size ≤ tg ≤ hi` (the bytes unchanged, `rzSeg_bs_of_le`;
  the bytes past the size as the `OsMeta` knew them, with the growth's zero stamped `n` appended):
  `segBytesX_rzGrow` (the growth form of `segBytesX_rzSeg`), `fileCrashedR_rzMeta_grow`,
  `crashOkA_rzGrow`, `tailCrashStep_rzGrow`. `tg ≤ hi`: a growth back to a size the file had since its
  last exact state (`ZeroToEnd`'s: the truncate to `wr` kept `hi`) allows no longer crash.
* its landing with the size `w` (`size ≤ w ≤ tg`), the bytes grown over those of `zs` with the zero
  stamped `n` appended (`rsDoneK`'s), the `OsMeta` `rsPostK true tr … w n []`: `rzLandG`; its crash
  condition from the in-flight layout (`crashOkA_rzLandG`, over `segBytesX_rzLandG`: the in-flight
  tail's `segBytesX` is a prefix of the landed one's), given that `zs` are the candidates the `OsMeta`
  knew of those bytes (`hzs`; the extension's model has it, `resize_done_worldK`'s `zs` from
  `RsFacts.hcandP`, but `rsDoneK` does not export it: an obligation, I3b `wal-tc11` entry).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzWals

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section grow
variable [GooseExts]

/-- `rzMeta_pc` for either kind of resize: past the size, what the `OsMeta` knew, with the zero
stamped `n` appended inside the announced range. -/
theorem rzMeta_pcG {tr : Bool} {m : OsMeta} {tg n j : Nat} (_hzf : ∀ z, m.zf = some z → m.size ≤ z)
    (hj : m.size ≤ j) :
    (rzMeta tr m tg n).pc j = (m.pc j).map (fun c =>
      if min m.size tg ≤ j ∧ j < rsHi tr m.size tg then c ++ [((0 : w8), n)] else c) := by
  have hz' : (rzMeta tr m tg n).zf = m.zf.map
      (fun z => if min m.size tg < rsHi tr m.size tg then max z (rsHi tr m.size tg) else z) := rfl
  by_cases hin : min m.size tg ≤ j ∧ j < rsHi tr m.size tg
  · have htc : (rzMeta tr m tg n).tc !! j = (m.pc j).map (· ++ [((0 : w8), n)]) := by
      show rsTail tr m tg m.size n [] !! j = _
      rw [rsTail_lookup, if_pos ⟨hin.1, hin.2, hj⟩, if_neg (by omega)]
    cases hp : m.pc j with
    | some c =>
      unfold OsMeta.pc; rw [htc, hp]; simp [hin]
    | none =>
      rw [hp] at htc
      unfold OsMeta.pc at hp ⊢
      rw [htc, hz']
      simp only [Option.map_none]
      cases ht : m.tc !! j with
      | some c => rw [ht] at hp; cases hp
      | none =>
        rw [ht] at hp
        cases hz : m.zf with
        | none => rfl
        | some z =>
          rw [hz] at hp
          simp only at hp
          split at hp
          · cases hp
          · simp only [Option.map_some, if_pos (show min m.size tg < rsHi tr m.size tg by omega)]
            rw [if_neg (by omega)]
  · have htc : (rzMeta tr m tg n).tc !! j = m.tc !! j := by
      show rsTail tr m tg m.size n [] !! j = _
      rw [rsTail_lookup, if_neg (fun h => hin ⟨h.1, h.2.1⟩), announce_tc,
        if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)]
    unfold OsMeta.pc
    rw [htc, hz']
    cases ht : m.tc !! j with
    | some c => simp [hin]
    | none =>
      cases hz : m.zf with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        by_cases hzj : z ≤ j
        · rw [if_pos hzj]; simp only [Option.map_some, hin, if_false]
          rw [if_pos (by split <;> omega)]
        · rw [if_neg hzj]; simp only [Option.map_none]
          rw [if_neg (by split <;> omega)]

/-- **`segBytesX` across a growth's first step** (`rzSeg` to a target `size ≤ tg ≤ hi`): as long,
each byte's candidates the old ones or with the growth's zero (stamped `n > 0`, a stamp `rzMeta`
knows) appended. -/
theorem segBytesX_rzGrow {g0 : SegG} {tr : Bool} {tg n : Nat} (hn : 0 < n) (hgrow : g0.om.size ≤ tg)
    (htg : tg ≤ g0.om.hi) (hlen : g0.bs.length = g0.om.size)
    (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z) :
    (segBytesX (rzSeg g0 tr tg n)).length = (segBytesX g0).length ∧
    ∀ b, b < (segBytesX g0).length → RzCands (rzSeg g0 tr tg n).om.rz
      ((segBytesX g0).getD b (0, [])).2 ((segBytesX (rzSeg g0 tr tg n)).getD b (0, [])).2 := by
  have hbs := rzSeg_bs_of_le (tr := tr) (n := n) hlen hgrow
  have hhi' : (rzSeg g0 tr tg n).om.hi = g0.om.hi := by
    show max g0.om.hi tg = _; omega
  have hpc := pcRunN_map (m := g0.om) (m' := (rzSeg g0 tr tg n).om)
    (F := fun j c => if min g0.om.size tg ≤ j ∧ j < rsHi tr g0.om.size tg then c ++ [((0 : w8), n)]
      else c) (b := g0.bs.length) (k := g0.om.hi - g0.bs.length)
    (fun j h1 _ => rzMeta_pcG hzf (by omega))
  have hrun : ∀ i, (pcRun (rzSeg g0 tr tg n).om (rzSeg g0 tr tg n).bs.length)[i]? =
      ((pcRun g0.om g0.bs.length)[i]?).map (fun y => (y.1,
        if min g0.om.size tg ≤ g0.bs.length + i ∧ g0.bs.length + i < rsHi tr g0.om.size tg then
          y.2 ++ [((0 : w8), n)] else y.2)) := by
    intro i; unfold pcRun; rw [hbs, hhi']; exact hpc i
  generalize hR : pcRun (rzSeg g0 tr tg n).om (rzSeg g0 tr tg n).bs.length = R at hrun
  generalize hR0 : pcRun g0.om g0.bs.length = R0 at hrun
  have hRl : R.length = R0.length := by
    apply Nat.le_antisymm
    · have h := hrun R0.length
      rw [List.getElem?_eq_none (Nat.le_refl _), Option.map_none] at h
      exact List.getElem?_eq_none_iff.1 h
    · have h := hrun R.length
      rw [List.getElem?_eq_none (Nat.le_refl _)] at h
      exact List.getElem?_eq_none_iff.1 (Option.map_eq_none_iff.1 h.symm)
  have hX : segBytesX (rzSeg g0 tr tg n) = g0.bs ++ R := by rw [← hR, ← hbs]; rfl
  have hX0 : segBytesX g0 = g0.bs ++ R0 := by rw [← hR0]; rfl
  refine ⟨by rw [hX, hX0, List.length_append, List.length_append, hRl], fun b hb => ?_⟩
  have hrz : n ∈ (rzSeg g0 tr tg n).om.rz := by simp [rzSeg, rzMeta]
  rw [hX, hX0]
  by_cases hbs' : b < g0.bs.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hbs',
      List.getElem?_append_left hbs']
  · have hi := hrun (b - g0.bs.length)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    cases hy : R0[b - g0.bs.length]? with
    | none =>
      exfalso
      have := List.getElem?_eq_none_iff.1 hy
      rw [hX0, List.length_append] at hb; omega
    | some y =>
      rw [hy] at hi
      rw [hi]
      simp only [Option.map_some, Option.getD_some]
      split
      · exact .inr ⟨n, hn, hrz, rfl⟩
      · exact .inl rfl

/-- **A crash after a growth's first step is one the old tail allows** (the target at most `hi`: no
longer crash): a byte past the size keeps one of its known candidates or is zero (allowed there: past
`lo`); past the zeros known, zero (`OsMeta.TcZ`). -/
theorem fileCrashedR_rzMeta_grow {tr : Bool} {m : OsMeta} {tg n : Nat} {bs : List ByteG} {q : DFrac}
    {fo : Option OsFile} (hgrow : m.size ≤ tg) (htg : tg ≤ m.hi) (hlo : m.lo ≤ m.size)
    (htcz : m.TcZ) (h : FileCrashedR (rzMeta tr m tg n) [(0, q, bs)] fo) :
    FileCrashedR m [(0, q, bs)] fo := by
  have hzf := htcz.1
  intro f' hf'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h f' hf'
  simp only [rzMeta_lo, rzMeta_hi] at h2 h3
  have hrs := le_rsHi tr m.size tg
  refine ⟨h1, by omega, by omega, ?_, ?_, ?_⟩
  · intro r hr k hk hks
    rcases h4 r hr k hk hks with h | ⟨hl, h0⟩
    · exact .inl h
    · right; simp only [rzMeta_lo] at hl; exact ⟨by omega, h0⟩
  · intro z hz b hzb hb
    have hz' : (rzMeta tr m tg n).zf =
        some (if min m.size tg < rsHi tr m.size tg then max z (rsHi tr m.size tg) else z) := by
      show (m.zf.map _) = _; rw [hz]; rfl
    by_cases hb' : (if min m.size tg < rsHi tr m.size tg then max z (rsHi tr m.size tg) else z) ≤ b
    · exact h5 _ hz' b hb' hb
    · have hzs : m.size ≤ z := hzf z hz
      have hin : min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ m.size ≤ b := by
        split at hb' <;> omega
      have htc : (rzMeta tr m tg n).tc !! b = some [((0 : w8), 0), ((0 : w8), n)] := by
        show rsTail tr m tg m.size n [] !! b = _
        rw [rsTail_lookup, if_pos hin, if_neg (by omega), tcz_pc htcz hz hzb hin.2.2]; rfl
      rcases h6 b _ (by simp only [rzMeta_size]; omega) htc hb with ⟨s, hs⟩ | ⟨-, h0⟩
      · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
        rcases hs with ⟨h0, -⟩ | ⟨h0, -⟩ <;> exact h0
      · exact h0
  · intro b c hb hc hbs
    by_cases hin : min m.size tg ≤ b ∧ b < rsHi tr m.size tg
    · have htc : (rzMeta tr m tg n).tc !! b = some (c ++ [((0 : w8), n)]) := by
        show rsTail tr m tg m.size n [] !! b = _
        have hpc : m.pc b = some c := by unfold OsMeta.pc; rw [hc]
        rw [rsTail_lookup, if_pos ⟨hin.1, hin.2, hb⟩, if_neg (by omega), hpc]; rfl
      rcases h6 b _ (by simp only [rzMeta_size]; omega) htc hbs with ⟨s, hs⟩ | ⟨-, h0⟩
      · rcases List.mem_append.1 hs with hs | hs
        · exact .inl ⟨s, hs⟩
        · simp only [List.mem_singleton, Prod.mk.injEq] at hs
          exact .inr ⟨by omega, hs.1⟩
      · exact .inr ⟨by omega, h0⟩
    · have htc : (rzMeta tr m tg n).tc !! b = some c := by
        show rsTail tr m tg m.size n [] !! b = _
        rw [rsTail_lookup, if_neg (fun h => hin ⟨h.1, h.2.1⟩), announce_tc,
          if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega), hc]
      rcases h6 b _ (by simp only [rzMeta_size]; omega) htc hbs with h | ⟨-, h0⟩
      · exact .inl h
      · exact .inr ⟨by omega, h0⟩

/-- **The crash condition across a growth's first step** (`crashOkA_rz`): from any tail `g0` (exact
or in a window) whose `OsMeta` is a state's (`OsMeta.TcZ`), to a target `size ≤ tg ≤ hi`. -/
theorem crashOkA_rzGrow {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay0 : WalLay} {alt : Option WalLay} {cl : List Claim} {k : Nat}
    {pre : List SegG} {g0 : SegG} {tr : Bool} {tg n : Nat}
    (hnd : (lay0.segs.map (·.ino)).Nodup) (hs0 : lay0.segs = pre ++ [g0])
    (hlen : g0.bs.length = g0.om.size) (hlo : g0.om.lo ≤ g0.om.size)
    (hgrow : g0.om.size ≤ tg) (htg : tg ≤ g0.om.hi) (hn : 0 < n) (htcz : g0.om.TcZ)
    (hok : CrashOkA C Mr d lay0 alt cl k) :
    CrashOkA C Mr d (tailLay lay0 pre (rzSeg g0 tr tg n) lay0.wr) alt cl k := by
  obtain ⟨hXl, hXc⟩ := segBytesX_rzGrow (tr := tr) hn hgrow htg hlen htcz.1
  have hbs := rzSeg_bs_of_le (tr := tr) (n := n) hlen hgrow
  refine crashOkA_rz hnd hs0 rfl rfl rfl rfl rfl rfl rfl (fun fo h => ?_) (Nat.le_of_eq hXl.symm)
    hXc (fun s hs => by simp [rzSeg, rzMeta, hs]) hok
  rw [hbs] at h
  exact fileCrashedR_rzMeta_grow hgrow htg hlo htcz h

/-- **A growth's first step is a crash step** (`crashOkA_rzGrow`). -/
theorem tailCrashStep_rzGrow {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {tr : Bool} {tg n : Nat}
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [g0])
    (hlen : g0.bs.length = g0.om.size) (hlo : g0.om.lo ≤ g0.om.size)
    (hgrow : g0.om.size ≤ tg) (htg : tg ≤ g0.om.hi) (hn : 0 < n) (htcz : g0.om.TcZ) :
    TailCrashStep C Mr d lay pre g0 (rzSeg g0 tr tg n) lay.wr cl k :=
  fun _ _ hok => crashOkA_rzGrow hnd hs hlen hlo hgrow htg hn htcz hok

/-! ## The growth's landing -/

/-- The bytes a growth landed over, of candidates `zs`, each with the zero stamped `n` appended
(`rsDoneK`'s). -/
def growBytes (n : Nat) (zs : List Cands) : List ByteG := zs.map (fun c => ((0 : w8), c ++ [((0 : w8), n)]))

@[simp] theorem growBytes_length (n : Nat) (zs : List Cands) : (growBytes n zs).length = zs.length := by
  simp [growBytes]

/-- **The tail as a growth of `g0` to `tg` landed with the size `w`** (`rsPostK true`: the owner's
half, which knows the candidates past the new size and the stamp `n`), its bytes `g0`'s, then those
grown over (`growBytes n zs`). -/
def rzLandG (g0 : SegG) (tr : Bool) (tg w n : Nat) (zs : List Cands) : SegG :=
  { g0 with om := rsPostK true tr g0.om tg w n [], bs := g0.bs ++ growBytes n zs }

theorem rzLandG_length {g0 : SegG} {tr : Bool} {tg w n : Nat} {zs : List Cands}
    (hlen : g0.bs.length = g0.om.size) (hgrow : g0.om.size ≤ w) (hzl : zs.length = w - g0.om.size) :
    (rzLandG g0 tr tg w n zs).bs.length = w := by
  simp only [rzLandG, List.length_append, growBytes_length]; omega

/-- What a growth landed with the size `w` knows past it is what its first step knew. -/
theorem rsPostK_grow_tc {tr : Bool} {m : OsMeta} {tg w n b : Nat} (hgrow : m.size ≤ w) (hb : w ≤ b) :
    (rsPostK true tr m tg w n []).tc !! b = (rzMeta tr m tg n).tc !! b := by
  show rsTail tr m tg w n [] !! b = rsTail tr m tg m.size n [] !! b
  rw [rsTail_lookup, rsTail_lookup]
  by_cases hin : min m.size tg ≤ b ∧ b < rsHi tr m.size tg
  · rw [if_pos (show min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ w ≤ b from ⟨hin.1, hin.2, hb⟩),
      if_pos (show min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ m.size ≤ b from ⟨hin.1, hin.2, by omega⟩)]
  · rw [if_neg (show ¬ (min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ w ≤ b) from fun h => hin ⟨h.1, h.2.1⟩),
      if_neg (show ¬ (min m.size tg ≤ b ∧ b < rsHi tr m.size tg ∧ m.size ≤ b) from
        fun h => hin ⟨h.1, h.2.1⟩)]

theorem rsPostK_grow_pc {tr : Bool} {m : OsMeta} {tg w n b : Nat} (hgrow : m.size ≤ w) (hb : w ≤ b) :
    (rsPostK true tr m tg w n []).pc b = (rzMeta tr m tg n).pc b := by
  unfold OsMeta.pc; rw [rsPostK_grow_tc hgrow hb]; rfl

/-- **A crash after a growth landed is one its first step allows**, the bytes grown over of the
candidates the `OsMeta` knew (`hzs`). -/
theorem fileCrashedR_rzLandG {tr : Bool} {m : OsMeta} {tg w n : Nat} {bs : List ByteG}
    {zs : List Cands} {q : DFrac} {fo : Option OsFile}
    (hlen : bs.length = m.size) (hgrow : m.size ≤ w) (hw : w ≤ tg) (hzl : zs.length = w - m.size)
    (hzs : ∀ j c, j < zs.length → m.pc (m.size + j) = some c → zs[j]? = some c)
    (h : FileCrashedR (rsPostK true tr m tg w n []) [(0, q, bs ++ growBytes n zs)] fo) :
    FileCrashedR (rzMeta tr m tg n) [(0, q, bs)] fo := by
  intro f' hf'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h f' hf'
  have hrs := le_rsHi tr m.size tg
  refine ⟨h1, h2, h3, ?_, h5, ?_⟩
  · intro r hr k hk hks
    rw [List.mem_singleton] at hr; subst hr
    have hk' : k < (bs ++ growBytes n zs).length := by
      simp only [List.length_append, growBytes_length]; simp only at hk; omega
    rcases h4 _ (List.mem_singleton_self _) k hk' hks with ⟨s, hs⟩ | ⟨hl, h0⟩
    · left; refine ⟨s, ?_⟩
      have he : (bs ++ growBytes n zs)[k]'hk' = bs[k]'hk := List.getElem_append_left hk
      simp only at hs ⊢
      rw [he] at hs; exact hs
    · exact .inr ⟨hl, h0⟩
  · intro b c hb hc hbs
    replace hb : m.size ≤ b := by simpa using hb
    change rsTail tr m tg m.size n [] !! b = some c at hc
    by_cases hbw : b < w
    · rw [rsTail_lookup, if_pos ⟨by omega, by omega, hb⟩, if_neg (by omega)] at hc
      obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hc
      have hj : b - m.size < zs.length := by omega
      have hz := hzs (b - m.size) c0 hj (by rw [show m.size + (b - m.size) = b by omega]; exact hc0)
      have hk' : b < (bs ++ growBytes n zs).length := by
        simp only [List.length_append, growBytes_length]; omega
      have hy : (bs ++ growBytes n zs)[b]? = some ((0 : w8), c0 ++ [((0 : w8), n)]) := by
        rw [List.getElem?_append_right (by omega), hlen]
        simp only [growBytes, List.getElem?_map, hz, Option.map_some]
      have he : (bs ++ growBytes n zs)[b]'hk' = ((0 : w8), c0 ++ [((0 : w8), n)]) := by
        have := List.getElem?_eq_getElem hk'; rw [hy] at this; exact (Option.some.inj this).symm
      rcases h4 _ (List.mem_singleton_self _) b hk' (by simp only [Nat.zero_add]; exact hbs) with
        ⟨s, hs⟩ | ⟨hl, h0⟩
      · simp only [Nat.zero_add] at hs
        rw [he] at hs; exact .inl ⟨s, hs⟩
      · simp only [Nat.zero_add] at hl h0
        exact .inr ⟨hl, h0⟩
    · have hc' : (rsPostK true tr m tg w n []).tc !! b = some c := by
        rw [rsPostK_grow_tc hgrow (by omega)]; exact hc
      exact h6 b c (by show w ≤ b; omega) hc' hbs

/-- `pcRunN` over `k1 + k2` bytes: over the first `k1`, then, if they are all known, over the rest. -/
theorem pcRunN_add {m : OsMeta} : ∀ {b k1 : Nat} (k2 : Nat),
    pcRunN m b (k1 + k2) = pcRunN m b k1 ++
      (if (pcRunN m b k1).length = k1 then pcRunN m (b + k1) k2 else [])
  | b, 0, k2 => by simp [pcRunN]
  | b, k1 + 1, k2 => by
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega]
    cases hc : m.pc b with
    | none =>
      have h0 : ∀ k, pcRunN m b (k + 1) = [] := fun k => by simp [pcRunN, hc]
      rw [h0, h0]; simp
    | some c =>
      rw [pcRunN_succ_some hc, pcRunN_succ_some hc, pcRunN_add (b := b + 1) (k1 := k1) k2,
        show b + 1 + k1 = b + (k1 + 1) by omega]
      simp only [List.cons_append, List.length_cons, Nat.add_right_cancel_iff]

theorem pcRunN_fst {m : OsMeta} : ∀ {b k : Nat} {y : ByteG}, y ∈ pcRunN m b k → y.1 = 0
  | _, 0, _, h => by simp [pcRunN] at h
  | b, k + 1, y, h => by
    unfold pcRunN at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · rfl
      · exact pcRunN_fst h
    · simp at h

/-- **The landing keeps the tail's candidates** (`crashOkA_same`'s): `segBytesX` of the in-flight tail
(`rzSeg`) is a prefix of the landed one's (`rzLandG`), the bytes grown over of the candidates the
`OsMeta` knew (`hzs`). -/
theorem segBytesX_rzLandG {g0 : SegG} {tr : Bool} {tg w n : Nat} {zs : List Cands}
    (hlen : g0.bs.length = g0.om.size) (hgrow : g0.om.size ≤ w) (hw : w ≤ tg)
    (hzl : zs.length = w - g0.om.size) (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z)
    (hzs : ∀ j c, j < zs.length → g0.om.pc (g0.om.size + j) = some c → zs[j]? = some c) :
    segBytesX (rzSeg g0 tr tg n) <+: segBytesX (rzLandG g0 tr tg w n zs) := by
  have hbs := rzSeg_bs_of_le (tr := tr) (n := n) hlen (show g0.om.size ≤ tg by omega)
  have hrs := le_rsHi tr g0.om.size tg
  have hl2 := rzLandG_length (tr := tr) (tg := tg) (n := n) hlen hgrow hzl
  have hhi1 : (rzSeg g0 tr tg n).om.hi = max g0.om.hi tg := rfl
  have hhi2 : (rzLandG g0 tr tg w n zs).om.hi = max g0.om.hi tg := rfl
  -- the in-flight run, split at `w`
  have hsplit : pcRun (rzSeg g0 tr tg n).om (rzSeg g0 tr tg n).bs.length =
      pcRunN (rzSeg g0 tr tg n).om g0.om.size (w - g0.om.size) ++
        (if (pcRunN (rzSeg g0 tr tg n).om g0.om.size (w - g0.om.size)).length = w - g0.om.size then
          pcRunN (rzSeg g0 tr tg n).om w (max g0.om.hi tg - w) else []) := by
    unfold pcRun
    rw [hbs, hhi1, hlen,
      show max g0.om.hi tg - g0.om.size = (w - g0.om.size) + (max g0.om.hi tg - w) by omega,
      pcRunN_add, show g0.om.size + (w - g0.om.size) = w by omega]
  have hrest : pcRun (rzLandG g0 tr tg w n zs).om (rzLandG g0 tr tg w n zs).bs.length =
      pcRunN (rzSeg g0 tr tg n).om w (max g0.om.hi tg - w) := by
    unfold pcRun
    rw [hl2, hhi2]
    exact pcRunN_congr (fun j h1 _ => rsPostK_grow_pc hgrow h1)
  generalize hR1 : pcRunN (rzSeg g0 tr tg n).om g0.om.size (w - g0.om.size) = R1 at hsplit
  generalize hT : pcRunN (rzSeg g0 tr tg n).om w (max g0.om.hi tg - w) = T at hsplit hrest
  -- the run below `w` is a prefix of the bytes grown over
  have hR1l : R1.length ≤ zs.length := by rw [← hR1, hzl]; exact pcRunN_length_le
  have hpre : R1 <+: growBytes n zs := by
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem?
    intro i
    by_cases hi : i < R1.length
    · rw [List.getElem?_take_of_lt hi]
      obtain ⟨y, hy⟩ : ∃ y, R1[i]? = some y := ⟨_, List.getElem?_eq_getElem hi⟩
      have hy1 : y.1 = 0 := by
        have hm := List.mem_of_getElem? hy
        rw [← hR1] at hm; exact pcRunN_fst hm
      rw [← hR1] at hy
      obtain ⟨hiw, hpc⟩ := pcRunN_getElem? hy
      rw [hR1] at hy
      have hpc' := hpc
      change (rzMeta tr g0.om tg n).pc (g0.om.size + i) = some y.2 at hpc'
      have hcond : min g0.om.size tg ≤ g0.om.size + i ∧ g0.om.size + i < rsHi tr g0.om.size tg :=
        ⟨by omega, by omega⟩
      rw [rzMeta_pcG hzf (by omega)] at hpc'
      simp only [hcond, and_self, if_true] at hpc'
      obtain ⟨c0, hc0, hc⟩ := Option.map_eq_some_iff.1 hpc'
      have hz := hzs i c0 (by omega) hc0
      rw [hy]
      simp only [growBytes, List.getElem?_map, hz, Option.map_some, Option.some.injEq]
      rw [hc, ← hy1]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  obtain ⟨t, ht⟩ := hpre
  unfold segBytesX
  rw [hsplit, hrest, hbs]
  simp only [rzLandG]
  rw [← ht]
  split
  · rename_i hfull
    have : t = [] := by
      have := congrArg List.length ht
      simp only [List.length_append, growBytes_length] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.append_nil, List.append_assoc]
    exact List.prefix_refl _
  · simp only [List.append_nil, List.append_assoc]
    exact ⟨t ++ T, by simp⟩

/-- **The growth's landing keeps the crash condition** (from the in-flight layout, `crashOkA_same`),
the bytes grown over of the candidates the `OsMeta` knew (`hzs`). -/
theorem crashOkA_rzLandG {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {alt : Option WalLay} {cl : List Claim} {k : Nat}
    {pre : List SegG} {g0 : SegG} {tr : Bool} {tg w n : Nat} {zs : List Cands}
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [rzSeg g0 tr tg n])
    (hlen : g0.bs.length = g0.om.size) (hgrow : g0.om.size ≤ w) (hw : w ≤ tg)
    (hzl : zs.length = w - g0.om.size) (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z)
    (hzs : ∀ j c, j < zs.length → g0.om.pc (g0.om.size + j) = some c → zs[j]? = some c)
    (hok : CrashOkA C Mr d lay alt cl k) :
    CrashOkA C Mr d (tailLay lay pre (rzLandG g0 tr tg w n zs) lay.wr) alt cl k := by
  have hbs := rzSeg_bs_of_le (tr := tr) (n := n) hlen (show g0.om.size ≤ tg by omega)
  obtain ⟨t, ht⟩ := segBytesX_rzLandG (tr := tr) (n := n) hlen hgrow hw hzl hzf hzs
  refine crashOkA_same hnd hs rfl rfl rfl rfl rfl rfl rfl (fun fo h => ?_) ?_ (fun b hb => ?_)
    (fun s hs => ?_) hok
  · rw [hbs]; exact fileCrashedR_rzLandG hlen hgrow hw hzl hzs h
  · rw [← ht, List.length_append]; omega
  · rw [← ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
  · simpa [rzLandG, rzSeg, rzMeta] using hs

/-- **A growth's landing is a crash step** (`crashOkA_rzLandG`), from the in-flight layout. -/
theorem tailCrashStep_rzLandG {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {tr : Bool}
    {tg w n : Nat} {zs : List Cands}
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [rzSeg g0 tr tg n])
    (hlen : g0.bs.length = g0.om.size) (hgrow : g0.om.size ≤ w) (hw : w ≤ tg)
    (hzl : zs.length = w - g0.om.size) (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z)
    (hzs : ∀ j c, j < zs.length → g0.om.pc (g0.om.size + j) = some c → zs[j]? = some c) :
    TailCrashStep C Mr d lay pre (rzSeg g0 tr tg n) (rzLandG g0 tr tg w n zs) lay.wr cl k :=
  fun _ _ hok => crashOkA_rzLandG hnd hs hlen hgrow hw hzl hzf hzs hok

/-- **The growth's landing keeps the static relation** (from the in-flight layout): a window (exact
only if nothing was grown and the in-flight tail exact), its least crash size at most `wr` (`hlo`), the
bytes grown over within `old` (`hold`). -/
theorem walAbsD_rzLandG {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {tr : Bool} {tg w n : Nat} {zs : List Cands}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [rzSeg g0 tr tg n])
    (hlen : g0.bs.length = g0.om.size) (hgrow : g0.om.size ≤ w) (hw : w ≤ tg)
    (hzl : zs.length = w - g0.om.size) (hcut : g0.om.cut = none)
    (hlo : min g0.om.lo tg ≤ lay.wr) (hold : w ≤ lay.old.length)
    (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z)
    (hzs : ∀ j c, j < zs.length → g0.om.pc (g0.om.size + j) = some c → zs[j]? = some c) :
    WalAbsD C Mr d (tailLay lay pre (rzLandG g0 tr tg w n zs) lay.wr) ents := by
  have hg1 : lay.segs.getLast? = some (rzSeg g0 tr tg n) := by rw [hs]; simp
  have hbs := rzSeg_bs_of_le (tr := tr) (n := n) hlen (show g0.om.size ≤ tg by omega)
  have hl1 : (rzSeg g0 tr tg n).bs.length = g0.bs.length := by rw [hbs]
  have hl2 := rzLandG_length (tr := tr) (tg := tg) (n := n) hlen hgrow hzl
  obtain ⟨-, -, hlo0, -, -⟩ := habs.metas _ (List.mem_of_getLast? hg1)
  have hlo0' : min g0.om.lo tg ≤ g0.bs.length := by
    have : (rzSeg g0 tr tg n).om.lo = min g0.om.lo tg := rfl
    omega
  obtain ⟨hso, hwS, hbo, hwo, hB, hz0, hzS, hzZ, hWC⟩ := habs.lastWin _ hg1
  refine walAbsD_win habs hs rfl rfl ?_ ⟨fun hx => ?_, fun _ => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show (rsPost tr g0.om tg w).size = _; rw [hl2]; rfl
    · show (rsPost tr g0.om tg w).cut = none
      simp only [rsPost, OsMeta.announce, OsMeta.touch_cut, hcut]
    · show min g0.om.lo tg ≤ _; rw [hl2]; omega
    · show _ ≤ max g0.om.hi tg; rw [hl2]; omega
  · -- exact after the landing: nothing grown, the in-flight tail exact
    have h1 : min g0.om.lo tg = w := by have := hx.1; rw [hl2] at this; exact this
    have h2 : max g0.om.hi tg = w := by have := hx.2; rw [hl2] at this; exact this
    have hz : zs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hex1 : SegExact (rzSeg g0 tr tg n) :=
      ⟨by show min g0.om.lo tg = _; rw [hl1]; omega, by show max g0.om.hi tg = _; rw [hl1]; omega⟩
    have hbs2 : (rzLandG g0 tr tg w n zs).bs = (rzSeg g0 tr tg n).bs := by
      rw [hbs, hz]; simp [rzLandG, growBytes]
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := (habs.last _ hg1).1 hex1
    refine ⟨k1, k2, ?_, k4, fun b x hb => k5 b x (by rw [← hbs2]; exact hb), k6, k7, k8⟩
    rw [hbs2]; exact k3
  · refine ⟨⟨hso, hwS, by simp only [tailLay]; omega, by simp only [tailLay]; omega,
      fun b x hb hbw => ?_, hz0, hzS, hzZ, ?_⟩, ?_, fun hZ b x hb hx => ?_, ?_, ?_⟩
    · simp only [tailLay] at hbw ⊢
      have hb' : g0.bs[b]? = some x := by
        rw [← hb]; simp only [rzLandG]; rw [List.getElem?_append_left (by omega)]
      exact hB b x (by rw [hbs]; exact hb') hbw
    · obtain ⟨t, ht⟩ := segBytesX_rzLandG (tr := tr) (n := n) hlen hgrow hw hzl hzf hzs
      refine hWC.same (by show max g0.om.hi tg ≤ max g0.om.hi tg; exact Nat.le_refl _)
        (by rw [hl2]; show w ≤ max g0.om.hi tg; omega)
        (by rw [← ht, List.length_append]; omega) (fun b hb => ?_) (fun s hs => ?_)
      · rw [← ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hb]
      · simpa [rzLandG, rzSeg, rzMeta] using hs
    · exact WinHead.of_lo (by show min g0.om.lo tg ≤ lay.wr; exact hlo)
    · have hz := habs.zeroPast _ hg1 hZ
      simp only [tailLay] at hb
      simp only [rzLandG] at hx
      by_cases hbl : b < g0.bs.length
      · rw [List.getElem?_append_left hbl] at hx
        exact hz b x hb (by rw [hbs]; exact hx)
      · rw [List.getElem?_append_right (by omega)] at hx
        simp only [growBytes, List.getElem?_map] at hx
        obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hx
        rfl
    · have := habs.oldHi_any _ hg1
      simp only [rzSeg, rzMeta_hi] at this
      show lay.old.length ≤ max g0.om.hi tg; omega
    · have h := habs.winLo_any _ hg1; exact h

/-- **A growth's first step**: `WalsOk` and the directory keys of the layout with the tail announced
(`rzSeg` to `size ≤ tg ≤ hi`, at or past the write position, the least crash size at most `wr`), from
the old. -/
theorem rzGrow_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {tr : Bool} {tg k : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (habs : ∃ ents, WalAbsD C Mr d lay ents)
    (hgrow : g0.om.size ≤ tg) (htg : tg ≤ g0.om.hi) (hwr : lay.wr ≤ tg)
    (hlo : min g0.om.lo tg ≤ lay.wr) (hk : 0 < k) (htcz : g0.om.TcZ) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzSeg g0 tr tg k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzSeg g0 tr tg k) lay.wr]> Ls) cl n K c) := by
  obtain ⟨ents, habs⟩ := habs
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  have hg0 : g0 ∈ lay.segs := by rw [hs]; simp
  obtain ⟨hsz, hcut, hlo0, -, -⟩ := habs.metas g0 hg0
  have hstep := tailCrashStep_rzGrow (C := C) (Mr := Mr) (d := d) (cl := cl) (k := n) (tr := tr)
    hnd hs hsz.symm (by omega) hgrow htg hk htcz
  refine ⟨walsOk_tailA hW hd hl hs rfl (by simp [rzSeg, hcut]) (fun ents' h => ?_) hstep,
    fun K c h => dirKeysOk_tailA hd hl hstep h⟩
  exact walAbsD_rzStart h hs hwr hlo htg (segBytesX_rzGrow hk hgrow htg hsz.symm htcz.1)

/-- **A growth's landing**: `WalsOk` and the directory keys of the layout with the tail landed
(`rzLandG`), from the in-flight one. -/
theorem rzLandG_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {tr : Bool} {tg w k : Nat}
    {zs : List Cands}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [rzSeg g0 tr tg k])
    (hlen : g0.bs.length = g0.om.size) (hgrow : g0.om.size ≤ w) (hw : w ≤ tg)
    (hzl : zs.length = w - g0.om.size) (hcut : g0.om.cut = none)
    (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z)
    (hzs : ∀ j c, j < zs.length → g0.om.pc (g0.om.size + j) = some c → zs[j]? = some c)
    (hlo : min g0.om.lo tg ≤ lay.wr) (hold : w ≤ lay.old.length) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzLandG g0 tr tg w k zs) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzLandG g0 tr tg w k zs) lay.wr]> Ls) cl n K c) := by
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  have hstep := tailCrashStep_rzLandG (C := C) (Mr := Mr) (d := d) (cl := cl) (k := n)
    hnd hs hlen hgrow hw hzl hzf hzs
  refine ⟨walsOk_tailA hW hd hl hs rfl ?_
    (fun ents h => walAbsD_rzLandG h hs hlen hgrow hw hzl hcut hlo hold hzf hzs) hstep,
    fun K c h => dirKeysOk_tailA hd hl hstep h⟩
  simp [rzLandG, rsPostK, rsPost, OsMeta.announce, hcut]

end grow

end WalFs
end EtcdGrove
end Perennial

end
