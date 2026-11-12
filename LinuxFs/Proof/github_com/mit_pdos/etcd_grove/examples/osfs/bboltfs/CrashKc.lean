/- Lean-first (no Rocq counterpart). How the candidates the client knows of the database file
(`CSt.kc`, `CrashOk.lean`) go through the specs of the crash invariant (`Spec/os/CrashSt.lean`):
a write's second step keeps them (`kc_fin`); the states a `WriteAt` reaches (`WReach`) know each
byte of its range as its candidates before it, then the data's byte at one first stamp (`KW`,
`wreach_kw`), from which a meta slot it covers is `SlotK` (`kw_slotK`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashImg
public import LinuxFs.Spec.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Fs github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section pure
variable [GooseExts]

/-- `pwPostK`'s `pc` past the write's range is the old one. -/
theorem pwPostK_pc_out (m : OsMeta) (off : Nat) (data : List w8) (k n b : Nat) (c : Cands)
    (hr : ¬ inRange off (off + data.length) b = true) (hb : off ≤ b) (h : m.pc b = some c) :
    (pwPostK true m off data k n).pc b = some c := by
  have e : (pwPostK true m off data k n).pc b =
      (m.announce (min off m.size) (off + data.length) (max m.size (off + data.length))).pc b := by
    unfold OsMeta.pc
    simp only [pwPostK, pwPost, cond_true, pwTail_lookup, if_neg hr, announce_tc]
    by_cases hr' : inRange (min off m.size) (off + data.length) b = true
    · exfalso; apply hr; simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr' ⊢; omega
    · rw [if_neg hr']
  rw [e]
  exact announce_pc_out _ _ _ _ _ _ (by
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr ⊢; omega) (by omega) h

/-- **A write's second step keeps the candidates the client knows** of every byte. -/
theorem kc_fin {m : OsMeta} {bs : List ByteG} {fa fb t off : Nat} {data : List w8} {k n : Nat}
    {zs : List Cands} (hl : bs.length = m.size) (hoff : off ≤ m.size) (hk : k ≤ data.length)
    (hzl : zs.length = pwSize m.size off k - m.size) (hz : ZsOk m zs) :
    ∀ b c, (⟨m, bs, fa, fb, .write t off data n⟩ : CSt).kc b = some c →
      (⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ : CSt).kc b =
        some c := by
  intro b c hc
  have hmin : min off m.size = off := Nat.min_eq_left hoff
  have hS1 : m.size ≤ pwSize m.size off k := by unfold pwSize; split <;> omega
  have hS2 : pwSize m.size off k ≤ max m.size (off + k) := by unfold pwSize; split <;> omega
  have hfl : (finBytes m bs off data k n zs).length = pwSize m.size off k :=
    finBytes_length hl hoff hk
  simp only [CSt.kc, hmin] at hc
  simp only [CSt.kc, CSt.baseC] at hc ⊢
  show (if b < pwSize m.size off k then _ else _) = _
  have hP := pwBytes_length m.size off data k n (cfRange m bs off data.length) zs
  have hxl : (cfRange m bs off data.length).length = min (off + data.length) m.size - off := by
    simp only [cfRange, cfLo, cfHi, List.length_take, List.length_drop, hl, hmin]; omega
  by_cases hbS : b < pwSize m.size off k
  · rw [if_pos hbS]
    unfold finBytes
    rw [getElem?_tpd _ _ _ _ _ (by simp only [cfLo, hmin]; omega)]
    simp only [cfLo, hmin, hP]
    by_cases h1 : b < off
    · rw [if_pos h1]
      rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega),
        if_pos (by omega)] at hc
      exact hc
    · rw [if_neg h1]
      by_cases h2 : b < off + (min (off + data.length) (pwSize m.size off k) - off)
      · rw [if_pos h2]
        rw [if_pos (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega)] at hc
        rw [List.getElem?_eq_getElem (by rw [hP]; omega)]
        simp only [pwBytes, List.getElem_map, List.getElem_range, Option.map_some]
        by_cases h3 : b < m.size
        · rw [if_pos h3, List.getElem?_eq_getElem (by omega)] at hc
          simp only [Option.map_some, Option.some.injEq] at hc
          rw [if_pos (by rw [hxl]; omega), List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by rw [hxl]; omega)]
          simp only [cfRange, cfLo, hmin, List.getElem_take, List.getElem_drop,
            show off + (b - off) = b by omega, Option.getD_some, if_pos (show off ≤ b by omega)] at hc ⊢
          rw [← hc]
        · rw [if_neg h3] at hc
          obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hc
          rw [if_neg (by rw [hxl]; omega), List.getD_eq_getElem?_getD]
          have := hz (b - m.size) c0 (by rw [show m.size + (b - m.size) = b by omega]; exact hc0)
            (by rw [hzl]; omega)
          rw [show b - off - (cfRange m bs off data.length).length = b - m.size by rw [hxl]; omega,
            this, Option.getD_some, if_pos (show off ≤ b by omega)]
          try (congr 3; omega)
      · rw [if_neg h2]
        have h4 : off + data.length ≤ b := by
          have := hS1; omega
        have h5 : b < m.size := by have := hS2; omega
        rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega),
          if_pos h5] at hc
        rw [show cfHi m off data.length + (b - off - (min (off + data.length) (pwSize m.size off k) - off)) = b by
          simp only [cfHi]; omega]
        exact hc
  · rw [if_neg hbS]
    by_cases hr : inRange off (off + data.length) b = true
    · rw [if_pos hr, if_neg (show ¬ b < m.size by omega)] at hc
      show (pwPostK true m off data k n).pc b = some c
      unfold OsMeta.pc
      simp only [pwPostK, cond_true, pwTail_lookup, if_pos hr, if_pos (show m.size ≤ b by omega)]
      have hob : off ≤ b := by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr; omega
      rw [if_pos hob] at hc
      rw [hc]
    · rw [if_neg hr, if_neg (show ¬ b < m.size by omega)] at hc
      exact pwPostK_pc_out m off data k n b c hr (by
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr; omega) hc

/-- Each byte of the range, as of the write of `data` at `off`, written at one first stamp `N`
over what `K0` knew of it, and maybe again later with the same value. -/
def KWr (K0 K : Nat → Option Cands) (off : Nat) (data : List w8) : Prop :=
  ∃ N, 0 < N ∧ ∀ b, off ≤ b → b < off + data.length → ∀ c, K0 b = some c →
    ∃ L, K b = some (c ++ (data.getD (b - off) 0, N) :: L) ∧
      ∀ e ∈ L, e.1 = data.getD (b - off) 0 ∧ N < e.2

/-- **What a state a write of `data` at `off` reached knows**, against the state it started from
(`K0`): the bytes out of its range as before; those in it as before (no attempt yet, `nn = 0`), or
written (`KWr`). -/
def KW (K0 K : Nat → Option Cands) (off : Nat) (data : List w8) (nn : Nat) : Prop :=
  (∀ b, ¬ (off ≤ b ∧ b < off + data.length) → ∀ c, K0 b = some c → K b = some c) ∧
  ((nn = 0 ∧ ∀ b c, K0 b = some c → K b = some c) ∨ KWr K0 K off data)

/-- The candidates a state knows of a byte below the size are its bytes'. -/
theorem kc_idle_lt {m : OsMeta} {bs : List ByteG} {fa fb b : Nat} {c : Cands}
    (hl : bs.length = m.size) (hb : b < m.size)
    (h : (⟨m, bs, fa, fb, .idle⟩ : CSt).kc b = some c) :
    ∃ x, bs[b]? = some x ∧ x.2 = c := by
  simp only [CSt.kc, CSt.baseC, if_pos hb, List.getElem?_eq_getElem (show b < bs.length by omega),
    Option.map_some, Option.some.injEq] at h
  exact ⟨_, List.getElem?_eq_getElem (by omega), h⟩

/-- **The write's next attempt in flight**, fresh: written (`KWr`), the bytes out of the range as
before. -/
theorem kw_flight {K0 : Nat → Option Cands} {m : OsMeta} {bs : List ByteG} {fa fb off nn t n : Nat}
    {data : List w8} (hl : bs.length = m.size) (hS : off + nn ≤ m.size) (hnn : nn < data.length)
    (hfr : PwFresh m bs (off + nn) (data.drop nn) n)
    (hK : KW K0 (⟨m, bs, fa, fb, .idle⟩ : CSt).kc off data nn) :
    (∀ b, ¬ (off ≤ b ∧ b < off + data.length) → ∀ c, K0 b = some c →
      (⟨m, bs, fa, fb, .write t (off + nn) (data.drop nn) n⟩ : CSt).kc b = some c) ∧
    KWr K0 (⟨m, bs, fa, fb, .write t (off + nn) (data.drop nn) n⟩ : CSt).kc off data := by
  obtain ⟨hout, hin⟩ := hK
  have hmin : min (off + nn) m.size = off + nn := Nat.min_eq_left hS
  have hdl : (data.drop nn).length = data.length - nn := List.length_drop ..
  -- the flight's candidates, from the idle state's
  have hfl : ∀ b, (⟨m, bs, fa, fb, .write t (off + nn) (data.drop nn) n⟩ : CSt).kc b =
      if off + nn ≤ b ∧ b < off + data.length then
        ((⟨m, bs, fa, fb, .idle⟩ : CSt).kc b).map (· ++ [(data.getD (b - off) 0, n)])
      else (⟨m, bs, fa, fb, .idle⟩ : CSt).kc b := by
    intro b
    have hbase : (⟨m, bs, fa, fb, .write t (off + nn) (data.drop nn) n⟩ : CSt).baseC b =
        (⟨m, bs, fa, fb, .idle⟩ : CSt).baseC b := rfl
    show (if inRange (min (off + nn) m.size) (off + nn + (data.drop nn).length) b then
        ((⟨m, bs, fa, fb, .write t (off + nn) (data.drop nn) n⟩ : CSt).baseC b).map
          (· ++ [(if off + nn ≤ b then (data.drop nn).getD (b - (off + nn)) 0 else 0, n)])
      else (⟨m, bs, fa, fb, .write t (off + nn) (data.drop nn) n⟩ : CSt).baseC b) = _
    rw [hbase, hmin, hdl]
    show _ = if off + nn ≤ b ∧ b < off + data.length then
        ((⟨m, bs, fa, fb, .idle⟩ : CSt).baseC b).map (· ++ [(data.getD (b - off) 0, n)])
      else (⟨m, bs, fa, fb, .idle⟩ : CSt).baseC b
    by_cases h : off + nn ≤ b ∧ b < off + data.length
    · rw [if_pos (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega), if_pos h,
        if_pos h.1]
      have e : (data.drop nn).getD (b - (off + nn)) 0 = data.getD (b - off) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]
        congr 1; omega
      rw [e]
    · rw [if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega), if_neg h]
  -- a candidate of a byte of the attempt's range is older than it
  have hold : ∀ b c, off + nn ≤ b → b < off + data.length →
      (⟨m, bs, fa, fb, .idle⟩ : CSt).kc b = some c → ∀ q ∈ c, q.2 < n := by
    intro b c h1 h2 hc q hq
    by_cases hb : b < m.size
    · obtain ⟨x, hx, rfl⟩ := kc_idle_lt hl hb hc
      refine hfr.1 x ?_ q hq
      simp only [cfRange, cfLo, cfHi, hmin]
      rw [List.mem_iff_getElem?]
      refine ⟨b - (off + nn), ?_⟩
      rw [List.getElem?_take, if_pos (by rw [hdl]; omega), List.getElem?_drop,
        show off + nn + (b - (off + nn)) = b by omega, hx]
    · simp only [CSt.kc, CSt.baseC, if_neg hb] at hc
      exact hfr.2.1 b c (by omega) hc q hq
  refine ⟨fun b hb c hc => ?_, ?_⟩
  · rw [hfl, if_neg (by omega)]; exact hout b hb c hc
  rcases hin with ⟨rfl, hall⟩ | ⟨N, hN, hw⟩
  · refine ⟨n, hfr.2.2, fun b h1 h2 c hc => ⟨[], ?_, by simp⟩⟩
    rw [hfl, if_pos ⟨by omega, h2⟩, hall b c hc]; rfl
  · refine ⟨N, hN, fun b h1 h2 c hc => ?_⟩
    obtain ⟨L, hL, hLd⟩ := hw b h1 h2 c hc
    by_cases h3 : off + nn ≤ b
    · refine ⟨L ++ [(data.getD (b - off) 0, n)], ?_, fun e he => ?_⟩
      · rw [hfl, if_pos ⟨h3, h2⟩, hL]; simp
      · rcases List.mem_append.1 he with he | he
        · exact hLd e he
        · simp only [List.mem_singleton] at he; subst he
          refine ⟨rfl, hold b _ h3 h2 hL (data.getD (b - off) 0, N) (by simp)⟩
    · exact ⟨L, by rw [hfl, if_neg (by omega)]; exact hL, hLd⟩

/-- **Every state a `WriteAt` of `data` at `off` reaches knows `KW`** against the one it started
from. -/
theorem wreach_kw {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {nn : Nat}
    {m' : OsMeta} {bs' : List ByteG} (fa fb : Nat) (h : WReach m bs off data nn m' bs')
    (hl : bs.length = m.size) (hoff : off ≤ m.size) :
    KW (⟨m, bs, fa, fb, .idle⟩ : CSt).kc (⟨m', bs', fa, fb, .idle⟩ : CSt).kc off data nn := by
  induction h with
  | refl => exact ⟨fun _ _ _ hc => hc, .inl ⟨rfl, fun _ _ hc => hc⟩⟩
  | @step nn0 m0 bs0 k nn' n zs hR hnn hk hn' hzl hz hfr ih =>
    obtain ⟨hW, hS, -⟩ := hR.wIn hl hoff
    have hl0 : bs0.length = m0.size := hW.len
    obtain ⟨hout, hwr⟩ := kw_flight (t := 0) hl0 hS hnn hfr ih
    have hfin := kc_fin (t := 0) (fa := fa) (fb := fb) (n := n) (k := k) (zs := zs)
      (data := data.drop nn0) hl0 hS (by rw [List.length_drop]; omega) hzl hz
    exact ⟨fun b hb c hc => hfin b c (hout b hb c hc), .inr (by
      obtain ⟨N, hN, hw⟩ := hwr
      exact ⟨N, hN, fun b h1 h2 c hc => by
        obtain ⟨L, hL, hLd⟩ := hw b h1 h2 c hc
        exact ⟨L, hfin b _ hL, hLd⟩⟩)⟩

/-- **A meta slot a write covers**, clean before it (holding `X`), is `SlotK` with the data's
bytes there. -/
theorem kw_slotK {K0 : Nat → Option Cands} {s : CSt} {off : Nat} {data : List w8} {j : Nat}
    {X : List w8} (hX : X.length = 64) (hin : off ≤ 4096 * j + 16)
    (hend : 4096 * j + 80 ≤ off + data.length)
    (hK0 : ∀ k < 64, K0 (4096 * j + 16 + k) = some [(X.getD k 0, 0)])
    (h : (∀ b c, K0 b = some c → s.kc b = some c) ∨ KWr K0 s.kc off data) :
    SlotK s j X ((List.range 64).map fun k => data.getD (4096 * j + 16 + k - off) 0) := by
  refine ⟨hX, by simp, ?_⟩
  rcases h with hall | ⟨N, hN, hw⟩
  · exact .inl fun k hk => hall _ _ (hK0 k hk)
  · refine .inr ⟨N, hN, fun k hk => ?_⟩
    obtain ⟨L, hL, hLd⟩ := hw _ (by omega) (by omega) _ (hK0 k hk)
    have e : ((List.range 64).map fun k => data.getD (4096 * j + 16 + k - off) 0).getD k 0 =
        data.getD (4096 * j + 16 + k - off) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
    rw [e]
    exact ⟨L, by rw [hL]; rfl, hLd⟩

/-! ## Slots of byte lists -/

theorem getD_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- The 64 bytes of meta slot `j` of `B`. -/
def slotOf (B : List w8) (j : Nat) : List w8 := (List.range 64).map fun k => B.getD (4096 * j + 16 + k) 0

theorem slotOf_length (B : List w8) (j : Nat) : (slotOf B j).length = 64 := by simp [slotOf]

theorem slotOf_getD (B : List w8) (j k : Nat) (hk : k < 64) :
    (slotOf B j).getD k 0 = B.getD (4096 * j + 16 + k) 0 := by
  rw [List.getD_eq_getElem?_getD, slotOf, List.getElem?_map, List.getElem?_range hk]; rfl

/-- A slot of zeros. -/
theorem slotOf_zero {B : List w8} {j : Nat} (h : ∀ k < 64, B.getD (4096 * j + 16 + k) 0 = 0) :
    ¬ metaValid (decode (slotOf B j) : Meta) := by
  have : slotOf B j = List.replicate 64 0 := by
    apply List.ext_getElem (by simp [slotOf_length]); intro k h1 h2
    have := slotOf_getD B j k (by simpa [slotOf_length] using h1)
    rw [getD_lt _ h1] at this
    rw [this, h k (by simpa [slotOf_length] using h1), List.getElem_replicate]
  rw [this]; exact zeroSlot_invalid

/-- A slot as `fileMeta` reads it. -/
theorem slotOf_fileMeta (B : List w8) (j : Nat) (hl : 4096 * j + 80 ≤ B.length) :
    (decode (slotOf B j) : Meta) = fileMeta B j := by
  rw [fileMeta_slot]; congr 1
  apply List.ext_getElem? ; intro k
  by_cases hk : k < 64
  · rw [metaSlot_getElem? _ _ _ hk, List.getElem?_eq_some_iff.2 ⟨by simp [slotOf_length]; omega, ?_⟩]
    · rw [List.getElem?_eq_getElem (by omega)]
    · have := slotOf_getD B j k hk
      rw [getD_lt _ (by simp [slotOf_length]; omega)] at this
      rw [this, getD_lt _ (by omega)]
  · rw [List.getElem?_eq_none (by simp [slotOf_length]; omega),
      List.getElem?_eq_none (by rw [metaSlot_length]; omega)]

theorem slotOf_append_left (A C : List w8) (j : Nat) (h : 4096 * j + 80 ≤ A.length) :
    slotOf (A ++ C) j = slotOf A j := by
  apply List.ext_getElem (by simp [slotOf_length]); intro k h1 h2
  simp only [slotOf, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp [slotOf] at h1; omega)]

/-- The candidates a synced state knows of its bytes below the size: durable, holding them. -/
theorem kc_synced {m : OsMeta} {B : List w8} {fa fb b : Nat} (hl : B.length = m.size)
    (hb : b < m.size) :
    (⟨m, B.map durB, fa, fb, .idle⟩ : CSt).kc b = some [(B.getD b 0, 0)] := by
  simp only [CSt.kc, CSt.baseC, if_pos hb, List.getElem?_map, List.getElem?_eq_getElem (show b < B.length by omega),
    Option.map_some, getD_lt _ (show b < B.length by omega)]


end pure

end osfs_bboltfs
end EtcdGrove
end Perennial

end
