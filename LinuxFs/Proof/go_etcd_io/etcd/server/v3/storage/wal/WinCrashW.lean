/- Lean-first (no Rocq counterpart).

# The crash condition across a truncate from a window (I3b, `wal-tc7`; pure)

`cut` truncates the tail at its write position `wr`; the tail may already be in a window (a `Save`'s
writes past the preallocated size, `ReadAll`'s `ZeroToEnd` without a sync: `TailMetaW`). In a window
the size a crash may leave is bounded below by `lo ≤ wr` (`WalAbsD.winLo`), so a crash may leave the
zero of a byte from `wr` on whatever its candidates: every crash the truncate's layout allows (its
zeros past `wr`, the stamps known), the window's allows too, and `W1G` drops the truncate's zeros
(`W1G.drop_rz`). The exact tail is `crashOkA_win`'s case (`WinCrash.lean`).

* `crashOkA_rz`: `crashOkA_same` with the tail's candidates `RzCands` of the old ones (a known
  resize's zero appended) instead of equal.
* `fileCrashedR_rzMeta_win`, `segBytesX_rzSeg`: the truncate's first step from any tail, as
  `crashOkA_rz`/`crashOkA_win` take it.
* `crashOkA_rzStart`: the crash condition across a truncate's first step at the write position, from
  an exact tail or a window.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.WinCrash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RzStepPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section winw
variable [GooseExts]

/-- **The crash condition across a step on the tail whose crashes the old tail's allow, its
candidates the old ones or with a known resize's zero appended** (`crashOkA_same` with `RzCands`): the
layouts differ only in the tail's ghost (`g1` to `g2`, same inode); every crash `g2`'s `OsMeta` and
bytes allow, `g1`'s allow; `segBytesX g2` is at least as long as `segBytesX g1`, each candidate list
over it `g1`'s or with a zero stamped by one of `g2`'s known resizes; `g2` knows `g1`'s stamps. -/
theorem crashOkA_rz {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay1 lay2 : WalLay} {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {pre : List SegG} {g1 g2 : SegG}
    (hnd : (lay1.segs.map (·.ino)).Nodup)
    (hs1 : lay1.segs = pre ++ [g1]) (hs2 : lay2.segs = pre ++ [g2]) (hino : g2.ino = g1.ino)
    (hjr : lay2.jr = lay1.jr) (hnm : lay2.nm = lay1.nm) (hj : lay2.j = lay1.j)
    (hcuts : lay2.cuts = lay1.cuts) (hfirst : lay2.first = lay1.first)
    (hfc : ∀ fo, FileCrashedR g2.om [(0, DFrac.own (1 : Qp).half, g2.bs)] fo →
      FileCrashedR g1.om [(0, DFrac.own (1 : Qp).half, g1.bs)] fo)
    (hlen : (segBytesX g1).length ≤ (segBytesX g2).length)
    (hcand : ∀ b, b < (segBytesX g1).length →
      RzCands g2.om.rz ((segBytesX g1).getD b (0, [])).2 ((segBytesX g2).getD b (0, [])).2)
    (hrz : ∀ s ∈ g1.om.rz, s ∈ g2.om.rz)
    (hok : CrashOkA C Mr d lay1 alt cl n) : CrashOkA C Mr d lay2 alt cl n := by
  intro m' fo hr hf hnmd hw
  have hg1 : g1 ∈ lay1.segs := by rw [hs1]; simp
  have hg2 : g2 ∈ lay2.segs := by rw [hs2]; simp
  have hinos : lay2.segs.map (·.ino) = lay1.segs.map (·.ino) := by
    rw [hs2, hs1]; simp [hino]
  have hnd2 : (lay2.segs.map (·.ino)).Nodup := by rw [hinos]; exact hnd
  have hpre1 : ∀ g' ∈ lay1.segs, g' ∈ pre ∨ g' = g1 := by
    intro g' hg'; rw [hs1, List.mem_append, List.mem_singleton] at hg'; exact hg'
  have hf1 : ∀ g' ∈ lay1.segs, FileCrashedR g'.om [(0, DFrac.own (1 : Qp).half, g'.bs)]
      (fo g'.ino) := by
    intro g' hg'
    rcases hpre1 g' hg' with hp | rfl
    · exact hf g' (by rw [hs2]; simp [hp])
    · rw [← hino]; exact hfc _ (hf g2 hg2)
  have hn1 : ∀ g' ∈ lay1.segs, g'.ino ∈ walInos (entsOf m' lay1.j) → (fo g'.ino).isSome := by
    intro g' hg' hin
    rcases hpre1 g' hg' with hp | rfl
    · exact hnmd g' (by rw [hs2]; simp [hp]) (by rw [hj]; exact hin)
    · rw [← hino]; exact hnmd g2 hg2 (by rw [hj, hino]; exact hin)
  have hw1 : W1G C (walInos (entsOf m' lay1.j)) (fun i => imgOf (fo i)) (segBytesOf lay1)
      (segRzOf lay1) := by
    rw [← hj]
    refine (W1G.drop_rz hw (fun i bs hbs => ?_)).mono_rz (fun i s hs => ?_)
    · obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some hbs
      rcases hpre1 g' hg' with hp | rfl
      · exact ⟨segBytesX g', segBytesOf_mem hnd2 (by rw [hs2]; simp [hp]), Nat.le_refl _,
          fun b _ => .inl rfl⟩
      · refine ⟨segBytesX g2, by rw [← hino]; exact segBytesOf_mem hnd2 hg2, hlen,
          fun b hb => ?_⟩
        rw [← hino, segRzOf_of_mem hnd2 hg2]
        exact hcand b hb
    · obtain ⟨g', hg', hi, hs'⟩ := segRzOf_mem hs
      subst hi
      rcases hpre1 g' hg' with hp | rfl
      · rw [segRzOf_of_mem hnd2 (by rw [hs2]; simp [hp])]; exact hs'
      · rw [← hino, segRzOf_of_mem hnd2 hg2]; exact hrz s hs'
  rcases hok m' fo hr hf1 hn1 hw1 with h | ⟨la, hla, h⟩
  · left; exact crashTo_congr_lay hjr hnm hj hcuts hfirst hinos h
  · right; exact ⟨la, hla, h⟩

theorem tcz_pc {m : OsMeta} (h : m.TcZ) {z b : Nat} (hz : m.zf = some z) (hzb : z ≤ b)
    (hsb : m.size ≤ b) : m.pc b = some [((0 : w8), 0)] := by
  unfold OsMeta.pc
  cases ht : m.tc !! b with
  | some c => rw [h.2 z b c hz hzb hsb ht]
  | none => simp [hz, hzb]

/-- The truncate's first step's bytes, below the target the old ones, from it on with the zero
stamped `n` appended (`rzSeg`'s). -/
theorem rzBytes_getElem {bs : List ByteG} {tg n k : Nat} (htg : tg ≤ bs.length)
    (hk : k < (bs.take tg ++ rsAnn n (bs.drop tg)).length) :
    (bs.take tg ++ rsAnn n (bs.drop tg))[k] =
      if k < tg then bs[k]'(by simp at hk; omega)
      else ((bs[k]'(by simp at hk; omega)).1, (bs[k]'(by simp at hk; omega)).2 ++ [((0 : w8), n)]) := by
  by_cases hkt : k < tg
  · rw [if_pos hkt, List.getElem_append_left (by simp; omega), List.getElem_take]
  · rw [if_neg hkt, List.getElem_append_right (by simp; omega)]
    simp only [rsAnn, List.getElem_map, List.getElem_drop, List.length_take, Nat.min_eq_left htg]
    have e : tg + (k - tg) = k := by omega
    simp only [e]

/-- **A crash after a truncate's first step, from a window, is one the window allows**: its size at
least the window's `lo`, which is at most the target, a byte from the target on keeps one of its
candidates or is zero (allowed there: past `lo`); past the size what the window's `OsMeta` knows
(`OsMeta.TcZ`: its known zeros and the zeros' candidates agree). -/
theorem fileCrashedR_rzMeta_win {m : OsMeta} {tg n : Nat} {bs : List ByteG} {q : DFrac}
    {fo : Option OsFile} (hlo : m.lo ≤ tg) (htg : tg ≤ m.size) (hhi : m.size ≤ m.hi)
    (hlen : bs.length = m.size) (hzf : ∀ z, m.zf = some z → m.size ≤ z) (htcz : m.TcZ)
    (h : FileCrashedR (rzMeta true m tg n) [(0, q, bs.take tg ++ rsAnn n (bs.drop tg))] fo) :
    FileCrashedR m [(0, q, bs)] fo := by
  intro f' hf'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h f' hf'
  simp only [rzMeta_lo, rzMeta_hi] at h2 h3
  have hrs := le_rsHi true m.size tg
  refine ⟨h1, by omega, by omega, ?_, ?_, ?_⟩
  · intro r hr k hk hks
    rw [List.mem_singleton] at hr; subst hr
    simp only at hk hks ⊢
    have hk' : k < (bs.take tg ++ rsAnn n (bs.drop tg)).length := by simp; omega
    rcases h4 _ (List.mem_singleton_self _) k hk' hks with ⟨s, hs⟩ | ⟨hl, h0⟩
    · simp only at hs
      rw [rzBytes_getElem (by omega) hk'] at hs
      split at hs
      · exact .inl ⟨s, hs⟩
      · rcases List.mem_append.1 hs with hs | hs
        · exact .inl ⟨s, hs⟩
        · simp only [List.mem_singleton, Prod.mk.injEq] at hs
          right; refine ⟨by simp only [Nat.zero_add] at *; omega, hs.1⟩
    · right; simp only [rzMeta_lo, Nat.zero_add] at hl h0 ⊢; exact ⟨by omega, h0⟩
  · intro z hz b hzb hb
    have hz' : (rzMeta true m tg n).zf =
        some (if min m.size tg < rsHi true m.size tg then max z (rsHi true m.size tg) else z) := by
      show (m.zf.map _) = _; rw [hz]; rfl
    by_cases hb' : (if min m.size tg < rsHi true m.size tg then max z (rsHi true m.size tg) else z) ≤ b
    · exact h5 _ hz' b hb' hb
    · have hzs : m.size ≤ z := hzf z hz
      have hin : min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ m.size ≤ b := by
        split at hb' <;> omega
      have htc : (rzMeta true m tg n).tc !! b = some [((0 : w8), 0), ((0 : w8), n)] := by
        show rsTail true m tg m.size n [] !! b = _
        rw [rsTail_lookup, if_pos hin, if_neg (by omega), tcz_pc htcz hz hzb hin.2.2]; rfl
      rcases h6 b _ (by simp only [rzMeta_size]; omega) htc hb with ⟨s, hs⟩ | ⟨-, h0⟩
      · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
        rcases hs with ⟨h0, -⟩ | ⟨h0, -⟩ <;> exact h0
      · exact h0
  · intro b c hb hc hbs
    by_cases hin : min m.size tg ≤ b ∧ b < rsHi true m.size tg
    · have htc : (rzMeta true m tg n).tc !! b = some (c ++ [((0 : w8), n)]) := by
        show rsTail true m tg m.size n [] !! b = _
        have hpc : m.pc b = some c := by unfold OsMeta.pc; rw [hc]
        rw [rsTail_lookup, if_pos ⟨hin.1, hin.2, hb⟩, if_neg (by omega), hpc]; rfl
      rcases h6 b _ (by simp only [rzMeta_size]; omega) htc hbs with ⟨s, hs⟩ | ⟨-, h0⟩
      · rcases List.mem_append.1 hs with hs | hs
        · exact .inl ⟨s, hs⟩
        · simp only [List.mem_singleton, Prod.mk.injEq] at hs
          exact .inr ⟨by omega, hs.1⟩
      · exact .inr ⟨by omega, h0⟩
    · have htc : (rzMeta true m tg n).tc !! b = some c := by
        show rsTail true m tg m.size n [] !! b = _
        rw [rsTail_lookup, if_neg (fun h => hin ⟨h.1, h.2.1⟩), announce_tc,
          if_neg (by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]; omega), hc]
      rcases h6 b _ (by simp only [rzMeta_size]; omega) htc hbs with h | ⟨-, h0⟩
      · exact .inl h
      · exact .inr ⟨by omega, h0⟩

/-- `pcRunN` of an `OsMeta` that knows each byte's candidates as another, changed (`F`). -/
theorem pcRunN_map {m m' : OsMeta} {F : Nat → Cands → Cands} :
    ∀ {b k : Nat}, (∀ j, b ≤ j → j < b + k → m'.pc j = (m.pc j).map (F j)) →
      ∀ i, (pcRunN m' b k)[i]? = ((pcRunN m b k)[i]?).map (fun y => (y.1, F (b + i) y.2))
  | _, 0, _, i => by simp [pcRunN]
  | b, k + 1, h, i => by
    have hb := h b (Nat.le_refl _) (by omega)
    have ih := pcRunN_map (m := m) (m' := m') (F := F) (b := b + 1) (k := k)
      (fun j h1 h2 => h j (by omega) (by omega))
    unfold pcRunN
    cases hc : m.pc b with
    | none => rw [hc] at hb; simp [hb]
    | some c =>
      rw [hc] at hb
      simp only [Option.map_some] at hb
      rw [hb]
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem?_cons_succ]
        rw [ih i, show b + 1 + i = b + (i + 1) by omega]

/-- **The tail's ghost bytes past the size, as a truncate's first step announces them**: what the
`OsMeta` knew, with the zero stamped `n` appended inside the announced range. -/
theorem rzMeta_pc {m : OsMeta} {tg n j : Nat} (hzf : ∀ z, m.zf = some z → m.size ≤ z)
    (hj : m.size ≤ j) :
    (rzMeta true m tg n).pc j = (m.pc j).map (fun c =>
      if min m.size tg ≤ j ∧ j < rsHi true m.size tg then c ++ [((0 : w8), n)] else c) := by
  have hz' : (rzMeta true m tg n).zf = m.zf.map
      (fun z => if min m.size tg < rsHi true m.size tg then max z (rsHi true m.size tg) else z) := rfl
  by_cases hin : min m.size tg ≤ j ∧ j < rsHi true m.size tg
  · have htc : (rzMeta true m tg n).tc !! j = (m.pc j).map (· ++ [((0 : w8), n)]) := by
      show rsTail true m tg m.size n [] !! j = _
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
          · simp only [Option.map_some, if_pos (show min m.size tg < rsHi true m.size tg by omega)]
            rw [if_neg (by omega)]
  · have htc : (rzMeta true m tg n).tc !! j = m.tc !! j := by
      show rsTail true m tg m.size n [] !! j = _
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

/-- **`segBytesX` across a truncate's first step** (`rzSeg`): as long, each byte's candidates the
old ones or with the truncate's zero (stamped `n > 0`, a stamp `rzMeta` knows) appended. -/
theorem segBytesX_rzSeg {g0 : SegG} {tg n : Nat} (hn : 0 < n) (htg : tg ≤ g0.om.size)
    (hlen : g0.bs.length = g0.om.size) (hhi : g0.om.size ≤ g0.om.hi)
    (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z) :
    (segBytesX (rzSeg g0 true tg n)).length = (segBytesX g0).length ∧
    ∀ b, b < (segBytesX g0).length → RzCands (rzSeg g0 true tg n).om.rz
      ((segBytesX g0).getD b (0, [])).2 ((segBytesX (rzSeg g0 true tg n)).getD b (0, [])).2 := by
  have hl := rzSeg_length g0 true tg n
  have hhi' : (rzSeg g0 true tg n).om.hi = g0.om.hi := by
    show max g0.om.hi tg = _; omega
  have hpc := pcRunN_map (m := g0.om) (m' := (rzSeg g0 true tg n).om)
    (F := fun j c => if min g0.om.size tg ≤ j ∧ j < rsHi true g0.om.size tg then c ++ [((0 : w8), n)]
      else c) (b := g0.bs.length) (k := g0.om.hi - g0.bs.length)
    (fun j h1 _ => rzMeta_pc hzf (by omega))
  have hrun : ∀ i, (pcRun (rzSeg g0 true tg n).om (rzSeg g0 true tg n).bs.length)[i]? =
      ((pcRun g0.om g0.bs.length)[i]?).map (fun y => (y.1,
        if min g0.om.size tg ≤ g0.bs.length + i ∧ g0.bs.length + i < rsHi true g0.om.size tg then
          y.2 ++ [((0 : w8), n)] else y.2)) := by
    intro i; unfold pcRun; rw [hl, hhi']; exact hpc i
  generalize hR : pcRun (rzSeg g0 true tg n).om (rzSeg g0 true tg n).bs.length = R at hrun
  generalize hR0 : pcRun g0.om g0.bs.length = R0 at hrun
  have hRl : R.length = R0.length := by
    apply Nat.le_antisymm
    · have h := hrun R0.length
      rw [List.getElem?_eq_none (Nat.le_refl _), Option.map_none] at h
      exact List.getElem?_eq_none_iff.1 h
    · have h := hrun R.length
      rw [List.getElem?_eq_none (Nat.le_refl _)] at h
      exact List.getElem?_eq_none_iff.1 (Option.map_eq_none_iff.1 h.symm)
  have hX : segBytesX (rzSeg g0 true tg n) = (rzSeg g0 true tg n).bs ++ R := by rw [← hR]; rfl
  have hX0 : segBytesX g0 = g0.bs ++ R0 := by rw [← hR0]; rfl
  have hmin : min g0.om.size tg = tg := Nat.min_eq_right htg
  refine ⟨by rw [hX, hX0, List.length_append, List.length_append, hl, hRl], fun b hb => ?_⟩
  have hrz : n ∈ (rzSeg g0 true tg n).om.rz := by simp [rzSeg, rzMeta]
  rw [hX, hX0]
  by_cases hbs : b < g0.bs.length
  · have hbr : b < (rzSeg g0 true tg n).bs.length := by omega
    have hbr' : b < (g0.bs.take tg ++ rsAnn n (g0.bs.drop tg)).length := by
      simp only [rzSeg, hmin] at hbr; exact hbr
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hbs, List.getElem?_eq_getElem hbs,
      List.getD_eq_getElem?_getD, List.getElem?_append_left hbr, List.getElem?_eq_getElem hbr]
    simp only [Option.getD_some]
    have e : (rzSeg g0 true tg n).bs[b]'hbr = (g0.bs.take tg ++ rsAnn n (g0.bs.drop tg))[b]'hbr' := by
      simp only [rzSeg, hmin]
    rw [e, rzBytes_getElem (by omega) hbr']
    split
    · exact .inl rfl
    · exact .inr ⟨n, hn, hrz, rfl⟩
  · have hi := hrun (b - g0.bs.length)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
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

/-- **The crash condition across a truncate's first step at the write position** (`cut`'s), from an
exact tail (`crashOkA_win`) or a window (`crashOkA_rz`: a window's `lo` is at most `wr`, `winLo`, and
its `OsMeta` a state's, `OsMeta.TcZ`): the layout `lay0`, its tail `g0`, gives the layout with the tail
as the truncate's first step announced it (`rzSeg`, stamp `n > 0`). -/
theorem crashOkA_rzStart {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay0 : WalLay} {ents0 : Ents} {alt : Option WalLay} {cl : List Claim} {k : Nat}
    {pre : List SegG} {g0 : SegG} {n : Nat}
    (habs0 : WalAbsD C Mr d lay0 ents0) (hZ : TailZeros lay0) (hB : TailBound C Mr d lay0)
    (hnd : (lay0.segs.map (·.ino)).Nodup) (hs0 : lay0.segs = pre ++ [g0])
    (hzf : ∀ z, g0.om.zf = some z → g0.om.size ≤ z) (hn : 0 < n)
    (hwin : ¬ SegExact g0 → g0.om.lo ≤ lay0.wr ∧ g0.om.TcZ)
    (halt : ∀ la, alt = some la → ∀ g' ∈ la.segs, g'.ino ≠ g0.ino)
    (hok : CrashOkA C Mr d lay0 alt cl k) :
    CrashOkA C Mr d (tailLay lay0 pre (rzSeg g0 true lay0.wr n) lay0.wr) alt cl k := by
  have hg0 : lay0.segs.getLast? = some g0 := by rw [hs0]; simp
  have hg0m : g0 ∈ lay0.segs := List.mem_of_getLast? hg0
  obtain ⟨hsz, -, hlo0, hhi0, -⟩ := habs0.metas g0 hg0m
  obtain ⟨-, -, -, hwrb, -⟩ := habs0.lastWin g0 hg0
  have hlen : g0.bs.length = g0.om.size := hsz.symm
  have hwrs : lay0.wr ≤ g0.om.size := by omega
  have hmin : min g0.om.size lay0.wr = lay0.wr := Nat.min_eq_right hwrs
  obtain ⟨hXl, hXc⟩ := segBytesX_rzSeg (g0 := g0) (tg := lay0.wr) hn hwrs hlen (by omega) hzf
  have hl := rzSeg_length g0 true lay0.wr n
  by_cases hex : SegExact g0
  · have hX0 : segBytesX g0 = g0.bs := segBytesX_of_hi (Nat.le_of_eq hex.2)
    refine crashOkA_win hC habs0 hZ hB hnd hs0 rfl rfl rfl rfl rfl rfl rfl hex
      (fun z hz => by have := hzf z hz; omega) (by simp [rzSeg]; omega) (by omega)
      (by simp only [rzSeg, rzMeta_lo]; have := hex.1; omega)
      (by simp only [rzSeg, rzMeta_hi]; have := hex.2; omega) (by rw [hXl, hX0]; exact Nat.le_refl _)
      (fun b hb => ?_) (fun b hb => ?_) halt hok
    · have hbl : b < (rzSeg g0 true lay0.wr n).bs.length := by omega
      rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        rzSeg_getElem?_lt hlen (by omega)]
    · have := hXc b (by rw [hX0]; exact hb)
      rw [hX0] at this; exact this
  · obtain ⟨hlo, htcz⟩ := hwin hex
    refine crashOkA_rz hnd hs0 rfl rfl rfl rfl rfl rfl rfl (fun fo h => ?_) (Nat.le_of_eq hXl.symm)
      hXc (fun s hs => by simp [rzSeg, rzMeta, hs]) hok
    simp only [rzSeg, hmin] at h
    exact fileCrashedR_rzMeta_win hlo hwrs (by omega) hlen hzf htcz h

/-! ## The truncate's landing -/

/-- The tail as a truncate to `tg` landed (`rsPostK true`: the owner's half, which knows the cut-off
bytes' candidates and the stamp `n`), its bytes those below the target. -/
def rzLand (g0 : SegG) (tg n : Nat) : SegG :=
  { g0 with om := rsPostK true true g0.om tg tg n (g0.bs.drop tg), bs := g0.bs.take tg }

theorem pcRunN_congr {m m' : OsMeta} : ∀ {b k : Nat},
    (∀ j, b ≤ j → j < b + k → m'.pc j = m.pc j) → pcRunN m' b k = pcRunN m b k
  | _, 0, _ => rfl
  | b, k + 1, h => by
    unfold pcRunN
    rw [h b (Nat.le_refl _) (by omega),
      pcRunN_congr (b := b + 1) (k := k) (fun j h1 h2 => h j (by omega) (by omega))]

theorem pcRunN_succ_some {m : OsMeta} {b k : Nat} {c : Cands} (h : m.pc b = some c) :
    pcRunN m b (k + 1) = ((0 : w8), c) :: pcRunN m (b + 1) k := by
  simp [pcRunN, h]

/-- `pcRunN` over a run of known bytes, then the rest. -/
theorem pcRunN_known {m : OsMeta} {F : Nat → Cands} : ∀ {b k1 : Nat} (k2 : Nat),
    (∀ i, i < k1 → m.pc (b + i) = some (F i)) →
    pcRunN m b (k1 + k2) = (List.range k1).map (fun i => ((0 : w8), F i)) ++ pcRunN m (b + k1) k2
  | b, 0, k2, _ => by simp
  | b, k1 + 1, k2, h => by
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega]
    rw [pcRunN_succ_some (show m.pc b = some (F 0) by simpa using h 0 (by omega))]
    have ih := pcRunN_known (m := m) (F := fun i => F (i + 1)) (b := b + 1) (k1 := k1) k2
      (fun i hi => by rw [show b + 1 + i = b + (i + 1) by omega]; exact h (i + 1) (by omega))
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.cons_append, show b + 1 + k1 = b + (k1 + 1) by omega]
    rfl

/-- **What the landed truncate knows past the old size is what its first step knew.** -/
theorem rsPostK_pc_ge {m : OsMeta} {tg n b : Nat} {xs : List ByteG} (htg : tg ≤ m.size)
    (hb : m.size ≤ b) : (rsPostK true true m tg tg n xs).pc b = (rzMeta true m tg n).pc b := by
  have htc : (rsPostK true true m tg tg n xs).tc !! b = (rzMeta true m tg n).tc !! b := by
    show rsTail true m tg tg n xs !! b = rsTail true m tg m.size n [] !! b
    rw [rsTail_lookup, rsTail_lookup]
    by_cases h : min m.size tg ≤ b ∧ b < rsHi true m.size tg
    · rw [if_pos (show min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ tg ≤ b from ⟨h.1, h.2, by omega⟩),
        if_pos (show min m.size tg ≤ b ∧ b < rsHi true m.size tg ∧ m.size ≤ b from ⟨h.1, h.2, hb⟩),
        if_neg (show ¬ b < m.size by omega), if_neg (show ¬ b < m.size by omega)]
    · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
  unfold OsMeta.pc; rw [htc]; rfl

/-- **What the landed truncate knows of a byte it cut off**: its candidates before, then the zero. -/
theorem rsPostK_pc_mid {m : OsMeta} {tg n b : Nat} {xs : List ByteG} (htg : tg ≤ m.size)
    (hb1 : tg ≤ b) (hb2 : b < m.size) :
    (rsPostK true true m tg tg n xs).pc b = some ((xs.getD (b - tg) (0, [])).2 ++ [((0 : w8), n)]) := by
  have hrs := le_rsHi true m.size tg
  have htc : (rsPostK true true m tg tg n xs).tc !! b =
      some ((xs.getD (b - tg) (0, [])).2 ++ [((0 : w8), n)]) := by
    show rsTail true m tg tg n xs !! b = _
    rw [rsTail_lookup, if_pos ⟨by omega, by omega, hb1⟩, if_pos hb2, Nat.min_eq_right htg]
  unfold OsMeta.pc; rw [htc]

/-- **The landing keeps the tail's candidates** (`crashOkA_same`'s): `segBytesX` of the landed tail
(`rzLand`) has the candidates of `segBytesX` of the in-flight one (`rzSeg`), position by position. -/
theorem segBytesX_rzLand {g0 : SegG} {tg n : Nat} (htg : tg ≤ g0.om.size)
    (hlen : g0.bs.length = g0.om.size) (hhi : g0.om.size ≤ g0.om.hi) :
    (segBytesX (rzLand g0 tg n)).map (·.2) = (segBytesX (rzSeg g0 true tg n)).map (·.2) := by
  have hmin : min g0.om.size tg = tg := Nat.min_eq_right htg
  have hl2 : (rzLand g0 tg n).bs.length = tg := by simp [rzLand]; omega
  have hhi2 : (rzLand g0 tg n).om.hi = g0.om.hi := by
    show max g0.om.hi tg = _; omega
  have hhi1 : (rzSeg g0 true tg n).om.hi = g0.om.hi := by
    show max g0.om.hi tg = _; omega
  have hl1 := rzSeg_length g0 true tg n
  have e2 : pcRun (rzLand g0 tg n).om (rzLand g0 tg n).bs.length =
      (List.range (g0.om.size - tg)).map (fun i => ((0 : w8),
        ((g0.bs.drop tg).getD i (0, [])).2 ++ [((0 : w8), n)])) ++
      pcRunN (rzSeg g0 true tg n).om g0.om.size (g0.om.hi - g0.om.size) := by
    unfold pcRun
    rw [hl2, hhi2, show g0.om.hi - tg = (g0.om.size - tg) + (g0.om.hi - g0.om.size) by omega]
    rw [pcRunN_known (m := (rzLand g0 tg n).om)
      (F := fun i => ((g0.bs.drop tg).getD i (0, [])).2 ++ [((0 : w8), n)]) _
      (fun i hi => by
        show (rsPostK true true g0.om tg tg n (g0.bs.drop tg)).pc (tg + i) = _
        rw [rsPostK_pc_mid htg (by omega) (by omega), show tg + i - tg = i by omega])]
    rw [show tg + (g0.om.size - tg) = g0.om.size by omega]
    congr 1
    exact pcRunN_congr (fun j h1 _ => rsPostK_pc_ge htg h1)
  have e1 : pcRun (rzSeg g0 true tg n).om (rzSeg g0 true tg n).bs.length =
      pcRunN (rzSeg g0 true tg n).om g0.om.size (g0.om.hi - g0.om.size) := by
    unfold pcRun; rw [hl1, hhi1, hlen]
  unfold segBytesX
  rw [e1, e2]
  simp only [rzLand, rzSeg, hmin, List.map_append, List.append_assoc]
  congr 1
  congr 1
  simp only [rsAnn, List.map_map]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, Function.comp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1 ⊢; omega)]
  rfl

end winw

end WalFs
end EtcdGrove
end Perennial

end
