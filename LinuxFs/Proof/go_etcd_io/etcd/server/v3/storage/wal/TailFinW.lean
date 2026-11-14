/- Lean-first (no Rocq counterpart).

# The second step of a `pwrite` on the tail, any write from inside the file (W6, pure; W6 log,
twenty-fifth session)

`walAbsD_finishW`: the static relation after a write's second step (`segFinW`, `pwPostK true`), the
announced tail exact (then the write is inside the size: `walAbsD_finish`) or in a window. The window's
facts come over from the announced tail's because the finish changes no candidate that `segBytesX`
shows (`segFinW_candsX`: below the old size the candidates are the announced ones, past it the finish's
`zs` are the candidates the file had there, `wrMeta` appends the data's), only the written bytes' values
and the write position.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailMetaPw

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-! ## `segBytesX` when every byte past the bytes is known -/

theorem pcRunN_getElem?_known {m : OsMeta} : ∀ {b k : Nat}, (∀ j, j < k → (m.pc (b + j)).isSome) →
    ∀ j, (pcRunN m b k)[j]? = if j < k then (m.pc (b + j)).map (fun c => ((0 : w8), c)) else none
  | _, 0, _, j => by simp [pcRunN]
  | b, k + 1, h, j => by
    unfold pcRunN
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h 0 (by omega))
    rw [Nat.add_zero] at hc
    rw [hc]
    cases j with
    | zero => simp [hc]
    | succ j =>
      simp only [List.getElem?_cons_succ]
      rw [pcRunN_getElem?_known (fun j hj => by
        rw [show b + 1 + j = b + (j + 1) by omega]; exact h _ (by omega)) j]
      rw [show b + 1 + j = b + (j + 1) by omega]
      by_cases hj : j < k
      · rw [if_pos hj, if_pos (by omega)]
      · rw [if_neg hj, if_neg (by omega)]

/-- `segBytesX g` reaching `hi`: every byte from the bytes' end to `hi` is known. -/
theorem segBytesX_known {g : SegG} (h : g.om.hi ≤ (segBytesX g).length) {b : Nat}
    (hb1 : g.bs.length ≤ b) (hb2 : b < g.om.hi) : (g.om.pc b).isSome := by
  have hy : (segBytesX g)[b]? = some ((segBytesX g)[b]'(by omega)) := List.getElem?_eq_getElem _
  rw [(segBytesX_getElem?_ge hb1 hy).2]; rfl

theorem segBytesX_getElem?_known {g : SegG}
    (hk : ∀ b, g.bs.length ≤ b → b < g.om.hi → (g.om.pc b).isSome) (b : Nat) :
    (segBytesX g)[b]? = if b < g.bs.length then g.bs[b]? else
      if b < g.om.hi then (g.om.pc b).map (fun c => ((0 : w8), c)) else none := by
  unfold segBytesX pcRun
  by_cases hb : b < g.bs.length
  · rw [if_pos hb, List.getElem?_append_left hb]
  · rw [if_neg hb, List.getElem?_append_right (by omega),
      pcRunN_getElem?_known (fun j hj => hk _ (by omega) (by omega))]
    rw [show g.bs.length + (b - g.bs.length) = b by omega]
    by_cases h2 : b < g.om.hi
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

/-- Two lists of ghost bytes with the same candidates have the same candidates at each byte. -/
theorem candsX_getD {l l' : List ByteG} (h : l.map (·.2) = l'.map (·.2)) (b : Nat) :
    (l.getD b (0, [])).2 = (l'.getD b (0, [])).2 := by
  have e := congrArg (·[b]?) h
  simp only [List.getElem?_map] at e
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h1 : l[b]? <;> cases h2 : l'[b]? <;> rw [h1, h2] at e <;> simp at e ⊢
  exact e

/-- Past the old size, the finish's bytes are in its written range. -/
theorem pwSize_past {sz off k b : Nat} (hoff : off ≤ sz) (hb1 : sz ≤ b) (hb2 : b < pwSize sz off k) :
    off ≤ b ∧ b < off + k ∨ False := by
  unfold pwSize at hb2; split at hb2 <;> omega

/-! ## The finished tail's candidates -/

/-- **The finish changes no candidate `segBytesX` shows** (any write from inside the file, the
announced tail's known bytes reaching `hi`): below the old size the announced ones (only the values
change), in the written range past it the file's (`zs`, the finish's) then the data's, as `wrMeta`
announced them; past the new bytes the same `OsMeta` candidates (`pwPostK_true_pc`). -/
theorem segFinW_candsX {fl : SegFl} {g0 : SegG} {k : Nat} {zs : List Cands}
    (hok : fl.Ok g0) (hk : k ≤ fl.data.length) (hX : g0.om.hi ≤ (segBytesX g0).length)
    (hzl : zs.length = pwSize fl.m.size fl.off k - fl.m.size)
    (hzs : ∀ j c, fl.m.pc (fl.m.size + j) = some c → j < zs.length → zs[j]? = some c) :
    (segBytesX (segFinW fl g0 k zs)).map (·.2) = (segBytesX g0).map (·.2) := by
  have hok' := hok
  obtain ⟨hoff, -, hl, -, hom, -, -⟩ := hok'
  have hgl : g0.bs.length = fl.m.size := by
    rw [hok.eq_ann]; exact (segAnnW_length (g0 := ⟨g0.name, g0.ino, fl.m, fl.bs⟩) hoff hl).trans hl
  have hglen : (segFinW fl g0 k zs).bs.length = pwSize fl.m.size fl.off k := segFinW_length hok hk
  have hpc : ∀ b, (segFinW fl g0 k zs).om.pc b = g0.om.pc b := fun b => by
    rw [hom]; exact pwPostK_true_pc _ _ _ _ _ _
  have hhi : (segFinW fl g0 k zs).om.hi = g0.om.hi := by rw [hom]; rfl
  have hhi0 : g0.om.hi = max fl.m.hi (max fl.m.size (fl.off + fl.data.length)) := by
    rw [hom]; exact wrMeta_hi_eq _ _ _ _
  have hps := pwSize_ge_off (k := k) hoff
  have hps2 := pwSize_le_max' (sz := fl.m.size) (off := fl.off) hk
  have hk0 := fun b => segBytesX_known hX (b := b)
  have hk1 : ∀ b, (segFinW fl g0 k zs).bs.length ≤ b → b < (segFinW fl g0 k zs).om.hi →
      ((segFinW fl g0 k zs).om.pc b).isSome := by
    intro b h1 h2; rw [hpc]; rw [hhi] at h2; exact hk0 b (by omega) h2
  apply List.ext_getElem?
  intro b
  rw [List.getElem?_map, List.getElem?_map, segBytesX_getElem?_known hk1, segBytesX_getElem?_known hk0,
    hglen, hhi, hgl]
  by_cases hb : b < fl.m.size
  · rw [if_pos (by omega), if_pos hb, segFinW_getElem? hok hk]
    by_cases hr : fl.off ≤ b ∧ b < fl.off + k
    · rw [if_pos hr, if_pos hb, Option.map_map]; rfl
    · rw [if_neg hr]
  · rw [if_neg hb]
    by_cases hb2 : b < pwSize fl.m.size fl.off k
    · rw [if_pos hb2, segFinW_getElem? hok hk]
      have hr : fl.off ≤ b ∧ b < fl.off + k := by
        rcases pwSize_past hoff (by omega) hb2 with h | h
        · exact h
        · exact h.elim
      rw [if_pos hr, if_neg hb, if_pos (by omega)]
      have hsz : fl.m.size ≤ b := by omega
      have hoff' : fl.off ≤ fl.m.size := hoff
      have e0 := hk0 b (by omega) (by omega)
      rw [hom, wrMeta_pc_ge hoff' hsz, if_pos ⟨hr.1, by omega⟩] at e0 ⊢
      rw [Option.isSome_map] at e0
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 e0
      rw [hc]
      have hz := hzs (b - fl.m.size) c (by rw [show fl.m.size + (b - fl.m.size) = b by omega]; exact hc)
        (by omega)
      rw [show zs.getD (b - fl.m.size) [] = c by rw [List.getD_eq_getElem?_getD, hz]; rfl]
      rfl
    · rw [if_neg hb2]
      by_cases hb3 : b < g0.om.hi
      · rw [if_pos hb3, if_pos hb3, hpc]
      · rw [if_neg hb3, if_neg hb3]

/-! ## The finished tail, any write from inside the file -/

/-- An unsynced byte carrying an announced candidate of its intended value is written after the
finish (its value the intended one). -/
theorem ByteOk.fin {x y : w8} {a w : Bool} {g : ByteG} {n : Nat} (h : ByteOk x y a w false g)
    (hm : (x, n) ∈ g.2) (hn : 0 < n) : ByteOk x y a true false (x, g.2) := by
  obtain ⟨ex, e1, e2, e3⟩ := h.unsync
  have hmem : (x, n) ∈ ex := by
    rw [e1] at hm
    rcases List.mem_cons.1 hm with h | h
    · exact absurd (Prod.mk.inj h).2 (by omega)
    · exact h
  show ∃ ex : Cands, g.2 = (y, 0) :: ex ∧ (∀ q ∈ ex, q.1 = x ∧ 0 < q.2) ∧ (a = false → ex = []) ∧
    (x = x ∧ ex ≠ [])
  exact ⟨ex, e1, e2, e3, rfl, List.ne_nil_of_mem hmem⟩

/-- **The second step of a write from inside the file keeps the static relation**, the tail exact or
in a window (W6 log, twenty-fourth and twenty-fifth sessions), the write position past the `k` bytes
written (or where it was): the write of the intended bytes from `fl.off` (`hpre`), change number
positive; the finish's `zs` the candidates the file had past its size (`wp_osPWriteFinishK`'s). The
announced tail exact: the write is inside the size, `walAbsD_finish`. Otherwise the window stays open,
its candidates unchanged (`segFinW_candsX`). -/
theorem walAbsD_finishW {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {fl : SegFl} {k : Nat} {zs : List Cands}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0]) (hok : fl.Ok g0)
    (hwr : fl.off ≤ lay.wr) (hk : k ≤ fl.data.length) (hn : 0 < fl.n)
    (hpre : fl.data <+: (segStream C Mr d lay.cuts lay.cuts.length).drop fl.off)
    (hzl : zs.length = pwSize fl.m.size fl.off k - fl.m.size)
    (hzs : ∀ j c, fl.m.pc (fl.m.size + j) = some c → j < zs.length → zs[j]? = some c) :
    WalAbsD C Mr d (tailLay lay pre (segFinW fl g0 k zs) (max lay.wr (fl.off + k))) ents := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨hsz, -, hlo0, hhi0, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  have hok' := hok
  obtain ⟨hoff, hd, hl, hmc, hom, -, -⟩ := hok'
  have hgl : g0.bs.length = fl.m.size := by rw [← hsz, hom, wrMeta_size]
  have hhi0' : g0.om.hi = max fl.m.hi (max fl.m.size (fl.off + fl.data.length)) := by
    rw [hom]; exact wrMeta_hi_eq _ _ _ _
  by_cases hx0 : SegExact g0
  · have hin : fl.off + fl.data.length ≤ fl.m.size := by
      have := hx0.2; rw [hhi0'] at this; omega
    have e : segFinW fl g0 k zs = segFin fl g0 k zs := by
      simp only [segFinW, segFin, pwPostK_true_in hin]
    rw [e]; exact walAbsD_finish habs hs hx0 hok hin hwr hk hn
  -- the window: the announced tail's facts
  obtain ⟨hTW, hHead, hZero, hOldHi, hWLo, hWLow⟩ := (habs.last g0 hg0).2 hx0
  obtain ⟨hso', hwS, hz0o, hwb, hB, hz0, hzS, hzZ, hWC⟩ := hTW
  obtain ⟨g, hgdef⟩ : ∃ g, g = segFinW fl g0 k zs := ⟨_, rfl⟩
  rw [← hgdef]
  have hglo : g.om.lo = g0.om.lo := by rw [hgdef, hom]; rfl
  have hghi : g.om.hi = g0.om.hi := by rw [hgdef, hom]; rfl
  have hgrz : g.om.rz = g0.om.rz := by
    rw [hgdef, hom, wrMeta_rz_eq]; exact pwPostK_rz _ _ _ _ _
  have hgsz : g.om.size = pwSize fl.m.size fl.off k := by rw [hgdef]; rfl
  have hglen : g.bs.length = pwSize fl.m.size fl.off k := by rw [hgdef]; exact segFinW_length hok hk
  have hgcut : g.om.cut = none := by rw [hgdef]; simp only [segFinW]; rw [pwPostK_cut]; exact hmc
  have hgb : ∀ b, g.bs[b]? =
      if fl.off ≤ b ∧ b < fl.off + k then
        (if b < fl.m.size then g0.bs[b]?.map (fun x => (fl.data.getD (b - fl.off) 0, x.2))
         else some (fl.data.getD (b - fl.off) 0,
           zs.getD (b - fl.m.size) [] ++ [(fl.data.getD (b - fl.off) 0, fl.n)]))
      else g0.bs[b]? := fun b => by rw [hgdef]; exact segFinW_getElem? hok hk
  have hga : ∀ b, g0.bs[b]? = if fl.off ≤ b ∧ b < fl.off + fl.data.length then
      fl.bs[b]?.map (fun x => (x.1, x.2 ++ [(fl.data.getD (b - fl.off) 0, fl.n)])) else fl.bs[b]? := by
    intro b; rw [hok.eq_ann]; exact segAnnW_getElem? (g0 := ⟨g0.name, g0.ino, fl.m, fl.bs⟩) hoff hl
  have hX0 : g0.om.hi ≤ (segBytesX g0).length := hWC.1
  have hC := segFinW_candsX hok hk hX0 hzl hzs
  rw [← hgdef] at hC
  have hCd : ∀ b, ((segBytesX g).getD b (0, [])).2 = ((segBytesX g0).getD b (0, [])).2 :=
    candsX_getD hC
  have hCl : (segBytesX g).length = (segBytesX g0).length := by
    simpa using congrArg List.length hC
  have hps := pwSize_ge_off (k := k) hoff
  have hps2 := pwSize_le_max' (sz := fl.m.size) (off := fl.off) hk
  have hdl : 0 < fl.data.length := List.length_pos_iff.2 hd
  have hSl : fl.off + fl.data.length ≤ (segStream C Mr d lay.cuts lay.cuts.length).length := by
    have := hpre.length_le; rw [List.length_drop] at this; omega
  have hdS : ∀ b, fl.off ≤ b → b < fl.off + fl.data.length →
      fl.data.getD (b - fl.off) 0 = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0 := by
    intro b h1 h2
    obtain ⟨e1, -⟩ := prefix_getD hpre (j := b - fl.off) (by omega)
    rw [show fl.off + (b - fl.off) = b by omega] at e1
    exact e1
  have hnx : ¬ SegExact g := by
    intro hx
    apply hx0
    have h1 := hx.1; have h2 := hx.2
    rw [hglo, hglen] at h1
    rw [hghi, hglen] at h2
    refine ⟨?_, ?_⟩ <;> omega
  -- a byte of the finished tail: its candidates are the announced tail's, inside `segBytesX`
  have hxs : ∀ b x, g.bs[b]? = some x →
      x.2 = ((segBytesX g0).getD b (0, [])).2 ∧ b < (segBytesX g0).length := by
    intro b x hx
    have hbl : b < g.bs.length := (List.getElem?_eq_some_iff.1 hx).1
    have e := hCd b
    rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, hx, Option.getD_some] at e
    refine ⟨e, ?_⟩
    have := segBytesX_length_le (g := g); omega
  -- the announced tail's candidates from `lo` on have the window's shape
  have hcand0 : ∀ b, g0.om.lo ≤ b → b < (segBytesX g0).length →
      ∀ q ∈ ((segBytesX g0).getD b (0, [])).2,
        WinShape (segStream C Mr d lay.cuts lay.cuts.length) lay.old g0.om.rz b q := by
    intro b hb1 hb2 q hq
    by_cases hbw : b < lay.wr
    · have hbl : b < g0.bs.length := by omega
      rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl,
        Option.getD_some] at hq
      exact (hWLow b _ (List.getElem?_eq_getElem hbl) hb1 hbw).2 q hq
    · exact hWC.2 b (by omega) hb2 q hq
  refine walAbsD_win habs hs (by rw [hgdef]; rfl) (by rw [hgdef]; rfl)
    ⟨by rw [hgsz, hglen], hgcut, by rw [hglo, hglen]; omega, by rw [hghi, hglen, hhi0']; omega⟩
    ⟨fun hx => absurd hx hnx, fun _ => ?_⟩
  refine ⟨⟨by simp only [tailLay]; omega, by simp only [tailLay]; omega, hz0o,
      by simp only [tailLay]; rw [hglen]; omega, fun b x hb hbl => ?_, by simp only [tailLay]; omega,
      hzS, hzZ, ⟨by rw [hCl, hghi]; exact hX0, fun b hb1 hb2 q hq => ?_⟩⟩,
    fun b hb1 hb2 => ?_, fun hZ' b x hb hx => ?_, by simp only [tailLay]; rw [hghi]; exact hOldHi,
    by unfold WinLo at hWLo ⊢; simp only [tailLay]; rw [hglo]; exact hWLo,
    fun b x hb hlb hbw => ?_⟩
  · -- `ByteOk` below `lo`: the written bytes take the data's value
    rw [hglo] at hbl
    show ByteOk ((segStream C Mr d lay.cuts lay.cuts.length).getD b 0) (lay.old.getD b 0)
      (decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length))
      (decide (b < max lay.wr (fl.off + k))) (decide (b < lay.so)) x
    have hbs : b < fl.m.size := by omega
    rw [hgb b] at hb
    by_cases hr : fl.off ≤ b ∧ b < fl.off + k
    · rw [if_pos hr, if_pos hbs] at hb
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hb
      have hold := hB b y hy hbl
      have hr1 := hr.1; have hr2 := hr.2
      have hmem : (fl.data.getD (b - fl.off) 0, fl.n) ∈ y.2 := by
        have e := hga b
        rw [if_pos ⟨hr1, by omega⟩, hy] at e
        obtain ⟨z, -, hz⟩ := Option.map_eq_some_iff.1 e.symm
        rw [← hz]; simp
      have hbso : ¬ b < lay.so := fun hlt => by
        rw [decide_eq_true hlt] at hold
        have := hold.synced_stamps _ hmem
        simp only at this; omega
      rw [decide_eq_false hbso] at hold ⊢
      rw [decide_eq_true (show b < max lay.wr (fl.off + k) by omega)]
      rw [hdS b hr.1 (by omega)] at hmem ⊢
      exact hold.fin hmem hn
    · rw [if_neg hr] at hb
      have hold := hB b x hb hbl
      have e : decide (b < max lay.wr (fl.off + k)) = decide (b < lay.wr) := by
        by_cases h1 : b < fl.off
        · rw [decide_eq_true (show b < max lay.wr (fl.off + k) by omega),
            decide_eq_true (show b < lay.wr by omega)]
        · have h2 : fl.off + k ≤ b := by omega
          by_cases h3 : b < lay.wr
          · rw [decide_eq_true (show b < max lay.wr (fl.off + k) by omega), decide_eq_true h3]
          · rw [decide_eq_false (show ¬ b < max lay.wr (fl.off + k) by omega), decide_eq_false h3]
      rw [e]; exact hold
  · -- `WinCands`: the announced tail's
    simp only [tailLay] at hb1
    rw [hgrz]
    rw [hCd] at hq
    rw [hCl] at hb2
    exact hWC.2 b (by omega) hb2 q hq
  · -- `WinHead`: the announced tail's
    simp only [tailLay] at hb1 ⊢
    rw [hglo, hCd]
    rw [hCl] at hb2
    exact hHead b (by omega) hb2
  · -- `WinZero`: the bytes past the new write position are the announced tail's
    simp only [tailLay] at hb
    rw [hgb b, if_neg (by omega)] at hx
    exact hZero hZ' b x (by omega) hx
  · -- `WinLow`: the bytes from `lo` to the new write position
    rw [hglo] at hlb
    simp only [tailLay] at hbw ⊢
    rw [hgrz]
    have hx2 := hxs b x hb
    refine ⟨?_, fun q hq => by rw [hx2.1] at hq; exact hcand0 b hlb hx2.2 q hq⟩
    rw [hgb b] at hb
    split at hb
    · rename_i hr
      split at hb
      · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hb
        exact hdS b hr.1 (by omega)
      · cases hb; exact hdS b hr.1 (by omega)
    · exact (hWLow b x hb hlb (by omega)).1

end pure

end WalFs
end EtcdGrove
end Perennial

end
