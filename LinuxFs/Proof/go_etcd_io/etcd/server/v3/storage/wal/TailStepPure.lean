/- Lean-first (no Rocq counterpart).

# A `pwrite` step on the tail keeps what the invariant says of the WAL (W6, pure)

`notes/wal-fsext-plan.md`, "W6 implementation log". The two steps of a `pwrite` on the tail of an
open WAL (`TailWriter.lean`) change only the last segment's ghost (its `OsMeta` and bytes) and the
write position. Here, for the writes the WAL makes (inside the preallocated file, at the write
position, of the next bytes of the intended stream):

* `tailLay lay pre g wr`: the layout with the last segment `g` and the write position `wr`;
  `segAnn` (the tail as a write's first step announces it: `SegFl.Ok`) and `segFin` (as its second
  step leaves it, `k` bytes written: `finBytes`);
* `walAbsD_tail`: the static relation of such a layout, from the old one and the new tail's bytes'
  `ByteOk`; `walAbsD_announce` and `walAbsD_finish`, the two steps;
* `crashOkW_tail`: its crash condition (`crashOkA_tail`, `TailCrash.lean`; the alternative layout of a
  pending cut never holds the tail, `AltOk`'s strict prefix);
* `walsOk_tail`: the invariant's `WalsOk` with the layout replaced.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrash
public import LinuxFs.Proof.os.CrashWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- The layout `lay` with the last segment `g` (after the segments `pre`) and the write position `wr`. -/
def tailLay (lay : WalLay) (pre : List SegG) (g : SegG) (wr : Nat) : WalLay :=
  { lay with segs := pre ++ [g], wr := wr }

/-- **The tail `g0` as the first step of a write of `data` at `off` announces it** (`SegFl.Ok`). -/
def segAnn (g0 : SegG) (off : Nat) (data : List w8) (n : Nat) : SegG :=
  { g0 with om := cfMeta g0.om off data.length,
            bs := g0.bs.take (cfLo g0.om off) ++ pwAnn data n (cfRange g0.om g0.bs off data.length) ++
              g0.bs.drop (cfHi g0.om off data.length) }

/-- **The tail `g0` as the second step of the write in flight `fl` leaves it**, `k` bytes written. -/
def segFin (fl : SegFl) (g0 : SegG) (k : Nat) (zs : List Cands) : SegG :=
  { g0 with om := pwPost fl.m fl.off fl.data.length k, bs := finBytes fl.m fl.bs fl.off fl.data k fl.n zs }

theorem segAnn_ok {g0 : SegG} {off : Nat} {data : List w8} {n t : Nat}
    (hin : off + data.length ≤ g0.om.size) (hd : data ≠ []) (hlen : g0.bs.length = g0.om.size)
    (hcut : g0.om.cut = none) (hoff : 0 < off) :
    SegFl.Ok ⟨t, off, data, n, g0.om, g0.bs, none⟩ (segAnn g0 off data n) :=
  ⟨Nat.le_trans (Nat.le_add_right _ _) hin, hd, hlen, hcut, (wrMeta_in hin).symm, rfl, hoff⟩

/-! ## The bytes of a write inside the file -/

theorem cfLo_in {m : OsMeta} {off n : Nat} (h : off + n ≤ m.size) : cfLo m off = off := by
  unfold cfLo; omega

theorem cfHi_in {m : OsMeta} {off n : Nat} (h : off + n ≤ m.size) : cfHi m off n = off + n := by
  unfold cfHi; omega

/-- A byte of `bs` with the run `[off, off + |P|)` replaced by `P`. -/
theorem getElem?_repl (bs P : List ByteG) (off b : Nat) (h : off + P.length ≤ bs.length) :
    (bs.take off ++ P ++ bs.drop (off + P.length))[b]? =
      if off ≤ b ∧ b < off + P.length then P[b - off]? else bs[b]? := by
  rw [getElem?_tpd bs P off (off + P.length) b (by omega)]
  by_cases h1 : b < off
  · rw [if_pos h1, if_neg (by omega)]
  · rw [if_neg h1]
    by_cases h2 : b < off + P.length
    · rw [if_pos h2, if_pos ⟨by omega, h2⟩]
    · rw [if_neg h2, if_neg (by omega)]; congr 1; omega

theorem cfRange_getElem? {m : OsMeta} {bs : List ByteG} {off n j : Nat} (h : off + n ≤ m.size)
    (hj : j < n) : (cfRange m bs off n)[j]? = bs[off + j]? := by
  unfold cfRange
  rw [cfLo_in h, cfHi_in h, List.getElem?_take, if_pos (by omega), List.getElem?_drop]

theorem cfRange_length {m : OsMeta} {bs : List ByteG} {off n : Nat} (h : off + n ≤ m.size)
    (hl : bs.length = m.size) : (cfRange m bs off n).length = n := by
  unfold cfRange; rw [cfLo_in h, cfHi_in h]; simp only [List.length_take, List.length_drop]; omega

/-- The announced tail's bytes. -/
theorem segAnn_getElem? {g0 : SegG} {off : Nat} {data : List w8} {n b : Nat}
    (hin : off + data.length ≤ g0.om.size) (hl : g0.bs.length = g0.om.size) :
    (segAnn g0 off data n).bs[b]? =
      if off ≤ b ∧ b < off + data.length then
        g0.bs[b]?.map (fun x => (x.1, x.2 ++ [(data.getD (b - off) 0, n)]))
      else g0.bs[b]? := by
  have hP : (pwAnn data n (cfRange g0.om g0.bs off data.length)).length = data.length := by
    rw [pwAnn_length, cfRange_length hin hl]
  have e : (segAnn g0 off data n).bs = g0.bs.take off ++ pwAnn data n (cfRange g0.om g0.bs off data.length) ++
      g0.bs.drop (off + (pwAnn data n (cfRange g0.om g0.bs off data.length)).length) := by
    simp only [segAnn]; rw [cfLo_in hin, cfHi_in hin, hP]
  rw [e, getElem?_repl _ _ _ _ (by rw [hP]; omega), hP]
  split
  · rename_i hb
    simp only [pwAnn, List.getElem?_mapIdx]
    rw [cfRange_getElem? hin (by omega), show off + (b - off) = b by omega]
  · rfl

theorem segAnn_length {g0 : SegG} {off : Nat} {data : List w8} {n : Nat}
    (hin : off + data.length ≤ g0.om.size) (hl : g0.bs.length = g0.om.size) :
    (segAnn g0 off data n).bs.length = g0.bs.length := by
  simp only [segAnn, List.length_append, List.length_take, List.length_drop, pwAnn_length]
  rw [cfRange_length hin hl, cfLo_in hin, cfHi_in hin]; omega

/-- The finished tail's bytes, against the announced ones. -/
theorem segFin_getElem? {fl : SegFl} {g0 : SegG} {k b : Nat} {zs : List Cands}
    (hok : fl.Ok g0) (hin : fl.off + fl.data.length ≤ fl.m.size) (hk : k ≤ fl.data.length) :
    (segFin fl g0 k zs).bs[b]? =
      if fl.off ≤ b ∧ b < fl.off + k then
        g0.bs[b]?.map (fun x => (fl.data.getD (b - fl.off) 0, x.2))
      else g0.bs[b]? := by
  obtain ⟨-, -, hl, -, hm, hbs, -⟩ := hok
  have hR := cfRange_length (bs := fl.bs) hin hl
  have hP : (pwBytes fl.m.size fl.off fl.data k fl.n (cfRange fl.m fl.bs fl.off fl.data.length) zs).length =
      fl.data.length := by
    rw [pwBytes_length]; unfold pwSize; split <;> omega
  have hA : (pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length)).length = fl.data.length := by
    rw [pwAnn_length, hR]
  have e1 : (segFin fl g0 k zs).bs = fl.bs.take fl.off ++
      pwBytes fl.m.size fl.off fl.data k fl.n (cfRange fl.m fl.bs fl.off fl.data.length) zs ++
      fl.bs.drop (fl.off + (pwBytes fl.m.size fl.off fl.data k fl.n
        (cfRange fl.m fl.bs fl.off fl.data.length) zs).length) := by
    simp only [segFin, finBytes]; rw [cfLo_in hin, cfHi_in hin, hP]
  have e2 : g0.bs = fl.bs.take fl.off ++ pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length) ++
      fl.bs.drop (fl.off + (pwAnn fl.data fl.n (cfRange fl.m fl.bs fl.off fl.data.length)).length) := by
    rw [hbs, cfLo_in hin, cfHi_in hin, hA]
  rw [e1, getElem?_repl _ _ _ _ (by rw [hP]; omega), hP, e2, getElem?_repl _ _ _ _ (by rw [hA]; omega), hA]
  by_cases hb : fl.off ≤ b ∧ b < fl.off + fl.data.length
  · rw [if_pos hb, if_pos hb]
    have hj : b - fl.off < fl.data.length := by omega
    have hr : (cfRange fl.m fl.bs fl.off fl.data.length)[b - fl.off]? = fl.bs[b]? := by
      rw [cfRange_getElem? hin hj, show fl.off + (b - fl.off) = b by omega]
    have hbl : b < fl.bs.length := by omega
    simp only [pwAnn, List.getElem?_mapIdx, hr]
    rw [List.getElem?_eq_getElem hbl]
    have hjP : b - fl.off < min (fl.off + fl.data.length) (pwSize fl.m.size fl.off k) - fl.off := by
      rw [← pwBytes_length fl.m.size fl.off fl.data k fl.n (cfRange fl.m fl.bs fl.off fl.data.length) zs, hP]
      exact hj
    simp only [pwBytes, List.getElem?_map, List.getElem?_range hjP, Option.map_some]
    have hgd : (cfRange fl.m fl.bs fl.off fl.data.length).getD (b - fl.off) (0, []) = fl.bs[b] := by
      rw [List.getD_eq_getElem?_getD, hr, List.getElem?_eq_getElem hbl]; rfl
    have hjl : b - fl.off < (cfRange fl.m fl.bs fl.off fl.data.length).length := by rw [hR]; exact hj
    rw [if_pos hjl, hgd]
    by_cases hbk : b < fl.off + k
    · rw [if_pos ⟨hb.1, hbk⟩]
      simp only [Option.map_some, pwByte, show fl.off + (b - fl.off) = b by omega, if_pos hbk]
    · rw [if_neg (fun h => hbk h.2)]
      simp only [pwByte, show fl.off + (b - fl.off) = b by omega, if_neg hbk, hgd]
  · rw [if_neg hb, if_neg hb, if_neg (fun h => hb ⟨h.1, by omega⟩)]

theorem segFin_length {fl : SegFl} {g0 : SegG} {k : Nat} {zs : List Cands}
    (hok : fl.Ok g0) (hin : fl.off + fl.data.length ≤ fl.m.size) (hk : k ≤ fl.data.length) :
    (segFin fl g0 k zs).bs.length = g0.bs.length := by
  obtain ⟨-, -, hl, -, hm, hbs, -⟩ := hok
  simp only [segFin]
  rw [finBytes_length hl (by omega) hk, hbs]
  simp only [List.length_append, List.length_take, List.length_drop, pwAnn_length]
  rw [cfRange_length hin hl, cfLo_in hin, cfHi_in hin]
  unfold pwSize; split <;> omega

/-! ## The static relation -/

theorem getElem?_tail_cases {pre : List SegG} {g g' : SegG} {k : Nat}
    (h : (pre ++ [g])[k]? = some g') :
    (k < pre.length ∧ pre[k]? = some g') ∨ (k = pre.length ∧ g' = g) := by
  by_cases hk : k < pre.length
  · left; rw [List.getElem?_append_left hk] at h; exact ⟨hk, h⟩
  · right
    rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at h
    split at h
    · cases h; exact ⟨by omega, rfl⟩
    · cases h

/-- **The static relation with the tail and the write position changed** (see the file header). -/
theorem walAbsD_tail {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0]) (hex0 : SegExact g0)
    (hino : g.ino = g0.ino) (hname : g.name = g0.name)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hlen : g.bs.length = g0.bs.length)
    (hso : lay.so ≤ wr') (hz0 : lay.z0 ≤ wr')
    (hS : wr' ≤ (segStream C Mr d lay.cuts lay.cuts.length).length) (hold : wr' ≤ lay.old.length)
    (hbytes : ∀ b (x : ByteG), g.bs[b]? = some x →
      ByteOk ((segStream C Mr d lay.cuts lay.cuts.length).getD b 0) (lay.old.getD b 0)
        (decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length)) (decide (b < wr'))
        (decide (b < lay.so)) x) :
    WalAbsD C Mr d (tailLay lay pre g wr') ents := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨-, -, hl0, -, -, -, hzS, hzZ⟩ := (habs.last g0 hg0).1 hex0
  refine ⟨?_, ?_, ?_, habs.cut, ?_, ?_, ?_, habs.synced, habs.lastSynced, habs.fit, habs.tailStop,
    by simp [tailLay], by simpa [tailLay] using habs.cutPos⟩
  · have h1 := habs.names.1; have h2 := habs.names.2
    rw [hs] at h1 h2
    simp only [tailLay, List.map_append, List.map_cons, List.map_nil] at h1 h2 ⊢
    rw [hino, hname]; exact ⟨h1, h2⟩
  · have h := habs.cuts; rw [hs] at h; simpa [tailLay] using h
  · intro k g' hk
    rcases getElem?_tail_cases hk with ⟨hk1, hk2⟩ | ⟨rfl, rfl⟩
    · exact habs.nameBound k g' (by rw [hs, List.getElem?_append_left hk1]; exact hk2)
    · obtain ⟨sq, ix, h1, h2⟩ := habs.nameBound pre.length g0 (by rw [hs]; simp)
      exact ⟨sq, ix, by rw [hname]; exact h1, h2⟩
  · intro g' hg'
    simp only [tailLay, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · obtain ⟨h1, h2, h3, h4, h5⟩ := habs.metas g' (by rw [hs]; exact List.mem_append_left _ hg')
      refine ⟨h1, h2, h3, h4, h5.elim (fun h => Or.inr ?_) Or.inr⟩
      rw [hs, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] at h
      exact h ▸ hex0
    · exact ⟨hmeta.1, hmeta.2.1, (Nat.le_of_eq hmeta.2.2.1), (Nat.le_of_eq hmeta.2.2.2.symm), Or.inr hmeta.2.2⟩
  · intro k g' hk hg'
    simp only [tailLay, List.length_append, List.length_singleton] at hk
    rcases getElem?_tail_cases hg' with ⟨hk1, hk2⟩ | ⟨hk1, -⟩
    · exact habs.intact k g' (by rw [hs]; simpa using hk) (by rw [hs, List.getElem?_append_left hk1]; exact hk2)
    · omega
  · intro g' hg'
    simp only [tailLay, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hg'
    subst hg'
    exact ⟨fun _ => ⟨hso, hS, by rw [hlen]; exact hl0, hold, hbytes, hz0, hzS, hzZ⟩,
      fun hne => absurd hmeta.2.2 hne⟩

/-- `ByteOk` of an unsynced, unwritten byte. -/
theorem byteOk_ff {x y : w8} {a : Bool} {g : ByteG} :
    ByteOk x y a false false g ↔ ∃ ex : Cands, g.2 = (y, 0) :: ex ∧ (∀ q ∈ ex, q.1 = x ∧ 0 < q.2) ∧
      (a = false → ex = []) ∧ g.1 = y := by
  unfold ByteOk; simp

theorem prefix_getD {data S : List w8} {off j : Nat} (h : data <+: S.drop off) (hj : j < data.length) :
    data.getD j 0 = S.getD (off + j) 0 ∧ off + j < S.length := by
  obtain ⟨t, ht⟩ := h
  have hl := congrArg List.length ht
  simp only [List.length_append, List.length_drop] at hl
  refine ⟨?_, by omega⟩
  have : (S.drop off).getD j 0 = data.getD j 0 := by
    rw [← ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD]
  rw [← this, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-- An unsynced byte's candidates: the old value's, then candidates of the intended value, stamped
positive. -/
theorem ByteOk.unsync {x y : w8} {a w : Bool} {g : ByteG} (h : ByteOk x y a w false g) :
    ∃ ex : Cands, g.2 = (y, 0) :: ex ∧ (∀ q ∈ ex, q.1 = x ∧ 0 < q.2) ∧ (a = false → ex = []) := by
  unfold ByteOk at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨ex, h1, h2, h3, -⟩ := h
  exact ⟨ex, h1, h2, h3⟩

/-- **An announced candidate of the intended value keeps an unsynced byte's `ByteOk`** (written
or not: a write announces the bytes it rewrites too). -/
theorem ByteOk.ann {x y : w8} {a w : Bool} {g : ByteG} {n : Nat} (h : ByteOk x y a w false g)
    (ha : a = true) (hn : 0 < n) : ByteOk x y a w false (g.1, g.2 ++ [(x, n)]) := by
  unfold ByteOk at h ⊢
  simp only [Bool.false_eq_true, if_false] at h ⊢
  obtain ⟨ex, h1, h2, -, h4⟩ := h
  refine ⟨ex ++ [(x, n)], by rw [h1]; rfl, ?_, fun h => absurd (ha.symm.trans h) (by decide), ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact h2 q hq
    · simp only [List.mem_singleton] at hq; subst hq; exact ⟨rfl, hn⟩
  · cases w
    · simpa using h4
    · simp only [if_true] at h4 ⊢; exact ⟨h4.1, by simp⟩

/-- A synced byte has no candidate stamped positive. -/
theorem ByteOk.synced_stamps {x y : w8} {a w : Bool} {g : ByteG} (h : ByteOk x y a w true g) :
    ∀ q ∈ g.2, q.2 = 0 := by
  unfold ByteOk at h
  simp only [if_true] at h
  subst h
  intro q hq
  simp only [durB, List.mem_singleton] at hq
  subst hq; rfl

/-- **The first step of a write keeps the static relation**: the write past the synced bytes and at
or below the write position (a retry rewrites bytes an earlier attempt wrote), of the intended
bytes from there, inside the file, change number positive. -/
theorem walAbsD_announce {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {off : Nat} {data : List w8} {n : Nat}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0]) (hex0 : SegExact g0)
    (hso : lay.so ≤ off) (hin : off + data.length ≤ g0.om.size)
    (hpre : data <+: (segStream C Mr d lay.cuts lay.cuts.length).drop off) (hn : 0 < n) :
    WalAbsD C Mr d (tailLay lay pre (segAnn g0 off data n) lay.wr) ents := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hg0m : g0 ∈ lay.segs := List.mem_of_getLast? hg0
  obtain ⟨hsz, hcut, -, -, -⟩ := habs.metas g0 hg0m
  obtain ⟨hlo, hhi⟩ := hex0
  obtain ⟨hso', hwS, -, hwo, hB, -⟩ := (habs.last g0 hg0).1 ⟨hlo, hhi⟩
  have hl : g0.bs.length = g0.om.size := hsz.symm
  have hlen := segAnn_length (n := n) hin hl
  refine walAbsD_tail habs hs ⟨hlo, hhi⟩ rfl rfl ?_ hlen hso' ((habs.last g0 hg0).1 ⟨hlo, hhi⟩).2.2.2.2.2.1
    hwS hwo ?_
  · rw [hlen]
    have hT : max g0.om.size (off + data.length) = g0.om.size := by omega
    simp only [segAnn, cfMeta, announce_size, OsMeta.announce_cut, announce_lo, announce_hi, hT]
    exact ⟨hsz, hcut, by omega, by omega⟩
  · intro b x hx
    rw [segAnn_getElem? hin hl] at hx
    split at hx
    · rename_i hb
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      have hold := hB b y hy
      rw [decide_eq_false (show ¬ b < lay.so by omega)] at hold ⊢
      obtain ⟨hdj, hbS⟩ := prefix_getD hpre (j := b - off) (by omega)
      rw [show off + (b - off) = b by omega] at hdj hbS
      rw [decide_eq_true hbS] at hold ⊢
      show ByteOk _ _ _ _ _ (y.1, y.2 ++ [(data.getD (b - off) 0, n)])
      rw [hdj]
      exact ByteOk.ann hold rfl hn
    · exact hB b x hx

/-- **The second step of a write keeps the static relation**, the write position past the `k`
bytes written (or where it was, if a retry rewrote bytes below it). -/
theorem walAbsD_finish {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {pre : List SegG} {g0 : SegG} {fl : SegFl} {k : Nat} {zs : List Cands}
    (habs : WalAbsD C Mr d lay ents) (hs : lay.segs = pre ++ [g0]) (hex0 : SegExact g0) (hok : fl.Ok g0)
    (hin : fl.off + fl.data.length ≤ fl.m.size)
    (hwr : fl.off ≤ lay.wr) (hk : k ≤ fl.data.length) (hn : 0 < fl.n) :
    WalAbsD C Mr d (tailLay lay pre (segFin fl g0 k zs) (max lay.wr (fl.off + k))) ents := by
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  have hg0m : g0 ∈ lay.segs := List.mem_of_getLast? hg0
  obtain ⟨hsz, hcut, -, -, -⟩ := habs.metas g0 hg0m
  obtain ⟨hlo, hhi⟩ := hex0
  obtain ⟨hso, hwS, hlo0, hwo, hB, hz0, -⟩ := (habs.last g0 hg0).1 ⟨hlo, hhi⟩
  have hok' := hok
  obtain ⟨-, hd, hl, hmc, hm, hbs, -⟩ := hok'
  rw [wrMeta_in hin] at hm
  have hlen := segFin_length (zs := zs) hok hin hk
  have hdl : 0 < fl.data.length := List.length_pos_iff.2 hd
  have hg0l : g0.bs.length = fl.m.size := by rw [← hsz, hm]; simp [cfMeta]
  -- the announced bytes of the range
  have hya : ∀ b, fl.off ≤ b → b < fl.off + fl.data.length → ∃ hbl : b < fl.bs.length,
      g0.bs[b]? = some (fl.bs[b].1, fl.bs[b].2 ++ [(fl.data.getD (b - fl.off) 0, fl.n)]) := by
    intro b h1 h2
    have hbl : b < fl.bs.length := by omega
    refine ⟨hbl, ?_⟩
    have e : g0 = segAnn ⟨g0.name, g0.ino, fl.m, fl.bs⟩ fl.off fl.data fl.n := by
      cases g0 with
      | mk nm ino om bs => simp only at hm hbs; subst hm hbs; rfl
    rw [e, segAnn_getElem? hin hl, if_pos ⟨h1, h2⟩, List.getElem?_eq_getElem hbl]; rfl
  -- the write starts past the synced bytes: its first byte carries the write's candidate
  have hso' : lay.so ≤ fl.off := by
    refine Nat.le_of_not_lt fun hlt => ?_
    obtain ⟨hbl, hy⟩ := hya fl.off (Nat.le_refl _) (by omega)
    have hold := hB fl.off _ hy
    rw [decide_eq_true hlt] at hold
    have h0 := hold.synced_stamps (fl.data.getD (fl.off - fl.off) 0, fl.n) (by simp)
    simp only at h0; omega
  -- a byte of the range: its intended value is the data's, and it is in the stream
  have hrng : ∀ b, fl.off ≤ b → b < fl.off + fl.data.length → ∃ y : ByteG, g0.bs[b]? = some y ∧
      fl.data.getD (b - fl.off) 0 = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0 ∧
      b < (segStream C Mr d lay.cuts lay.cuts.length).length ∧
      ∃ ex : Cands, y.2 = (lay.old.getD b 0, 0) :: ex ∧
        (∀ q ∈ ex, q.1 = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0 ∧ 0 < q.2) ∧
        ex ≠ [] := by
    intro b h1 h2
    obtain ⟨hbl, hy⟩ := hya b h1 h2
    refine ⟨_, hy, ?_⟩
    have hold := hB b _ hy
    rw [decide_eq_false (show ¬ b < lay.so by omega)] at hold
    obtain ⟨ex, e1, e2, e3⟩ := hold.unsync
    simp only at e1
    have hmem : (fl.data.getD (b - fl.off) 0, fl.n) ∈ ex := by
      cases hc : fl.bs[b].2 with
      | nil => rw [hc] at e1; simp at e1; omega
      | cons c cs =>
        rw [hc, List.cons_append, List.cons.injEq] at e1
        rw [← e1.2]; simp
    have hne : ex ≠ [] := List.ne_nil_of_mem hmem
    have hq := e2 _ hmem
    have hbS : b < (segStream C Mr d lay.cuts lay.cuts.length).length := by
      rcases Nat.lt_or_ge b (segStream C Mr d lay.cuts lay.cuts.length).length with h | h
      · exact h
      · exact absurd (e3 (decide_eq_false (by omega))) hne
    exact ⟨hq.1, hbS, ex, e1, e2, hne⟩
  have hkS : fl.off + k ≤ (segStream C Mr d lay.cuts lay.cuts.length).length := by
    by_cases hk0 : k = 0
    · subst hk0; omega
    · obtain ⟨-, -, -, hbS, -⟩ := hrng (fl.off + k - 1) (by omega) (by omega); omega
  refine walAbsD_tail habs hs ⟨hlo, hhi⟩ rfl rfl ?_ hlen (by omega) (by omega) (by omega) (by omega) ?_
  · have hT : max fl.m.size (fl.off + fl.data.length) = fl.m.size := by omega
    have hps : pwSize fl.m.size fl.off k = fl.m.size := by unfold pwSize; split <;> omega
    have hlo' := hlo; have hhi' := hhi
    rw [hm] at hlo' hhi' hcut
    simp only [cfMeta, announce_lo, announce_hi, OsMeta.announce_cut] at hlo' hhi' hcut
    rw [hlen]
    simp only [segFin, pwPost, hps, announce_lo, announce_hi, OsMeta.announce_cut]
    exact ⟨hg0l.symm, hcut, hlo', hhi'⟩
  · intro b x hx
    rw [segFin_getElem? hok hin hk] at hx
    split at hx
    · rename_i hb
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨y', hy', hdv, hbS, ex, e1, e2, hne⟩ := hrng b hb.1 (by omega)
      rw [hy] at hy'; cases hy'
      rw [decide_eq_true (show b < max lay.wr (fl.off + k) by omega),
        decide_eq_false (show ¬ b < lay.so by omega)]
      unfold ByteOk
      simp only [Bool.false_eq_true, if_false, if_true]
      exact ⟨ex, e1, e2, fun h => by simp at h; omega, hdv, hne⟩
    · rename_i hb
      have hold := hB b x hx
      have e : decide (b < max lay.wr (fl.off + k)) = decide (b < lay.wr) := by
        by_cases h1 : b < fl.off
        · rw [decide_eq_true (show b < max lay.wr (fl.off + k) by omega),
            decide_eq_true (show b < lay.wr by omega)]
        · have h2 : fl.off + k ≤ b := by omega
          by_cases h3 : b < lay.wr
          · rw [decide_eq_true (show b < max lay.wr (fl.off + k) by omega), decide_eq_true h3]
          · rw [decide_eq_false (show ¬ b < max lay.wr (fl.off + k) by omega), decide_eq_false h3]
      rw [e]; exact hold

/-- **A finished write's range carries its candidate** (stamped positive): a retry from a byte of the
range starts past the synced bytes (`wp_tailPWriteStart`'s premise). -/
theorem segFin_cand {fl : SegFl} {g0 : SegG} {k : Nat} {zs : List Cands} (hok : fl.Ok g0)
    (hin : fl.off + fl.data.length ≤ fl.m.size) (hk : k ≤ fl.data.length) (hn : 0 < fl.n) (b : Nat) (h1 : fl.off ≤ b)
    (h2 : b < fl.off + fl.data.length) :
    ∃ q ∈ ((segFin fl g0 k zs).bs.getD b (0, [])).2, 0 < q.2 := by
  have hok' := hok
  obtain ⟨-, -, hl, -, hm, hbs, -⟩ := hok'
  rw [wrMeta_in hin] at hm
  have hbl : b < fl.bs.length := by omega
  have hy : g0.bs[b]? = some (fl.bs[b].1, fl.bs[b].2 ++ [(fl.data.getD (b - fl.off) 0, fl.n)]) := by
    have e : g0 = segAnn ⟨g0.name, g0.ino, fl.m, fl.bs⟩ fl.off fl.data fl.n := by
      cases g0 with
      | mk nm ino om bs => simp only at hm hbs; subst hm hbs; rfl
    rw [e, segAnn_getElem? hin hl, if_pos ⟨h1, h2⟩, List.getElem?_eq_getElem hbl]; rfl
  refine ⟨(fl.data.getD (b - fl.off) 0, fl.n), ?_, hn⟩
  rw [List.getD_eq_getElem?_getD, segFin_getElem? hok hin hk, hy]
  split <;> simp

/-! ## The crash condition and `WalsOk` -/

/-- **A step on the tail keeps `CrashOkW`** (`crashOkA_tail`; a pending cut's alternative layout is a
strict prefix, so it never holds the tail). -/
theorem crashOkW_tail {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents ents' : Ents} {pre : List SegG} {g0 g : SegG} {wr' : Nat} {cl : List Claim} {n : Nat}
    (habs : WalAbsD C Mr d lay ents) (habs' : WalAbsD C Mr d (tailLay lay pre g wr') ents')
    (hZ : TailZeros lay) (hB : TailBound C Mr d lay) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino) (hlen : g.bs.length = g0.bs.length)
    (hzf : (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧ SegExact g0 ∧ SegExact g)
    (hok : CrashOkW C Mr d lay cl n) : CrashOkW C Mr d (tailLay lay pre g wr') cl n := by
  obtain ⟨alt, halt, hA⟩ := hok
  have hpre : ∀ lay0, alt = some lay0 → lay0.segs <+: pre := by
    intro lay0 h
    obtain ⟨-, -, -, -, hp, hlt⟩ := halt lay0 h
    rw [hs] at hp hlt
    obtain ⟨t, ht⟩ := hp
    cases t with
    | nil => rw [List.append_nil] at ht; rw [ht] at hlt; omega
    | cons c t =>
      refine ⟨(c :: t).dropLast, ?_⟩
      have := congrArg List.dropLast ht
      rwa [List.dropLast_append_of_ne_nil (List.cons_ne_nil c t),
        List.dropLast_append_of_ne_nil (List.cons_ne_nil g0 []), List.dropLast_singleton,
        List.append_nil] at this
  have hnd' : ((tailLay lay pre g wr').segs.map (·.ino)).Nodup := by
    rw [hs] at hnd; simpa [tailLay, hino] using hnd
  refine ⟨alt, fun lay0 h => ?_, crashOkA_tail hC habs habs' hZ hB hnd' hs rfl hino rfl rfl rfl rfl rfl
    hlen hzf ?_ hA⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := halt lay0 h
    have hp := hpre lay0 h
    refine ⟨h1, h2, h3, h4, hp.trans (List.prefix_append _ _), ?_⟩
    have := hp.length_le; simp [tailLay]; omega
  · intro la h g' hg' he
    have hg'p : g' ∈ pre := (hpre la h).subset hg'
    rw [hs, List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 g'.ino (List.mem_map_of_mem hg'p) g0.ino (by simp) (by rw [he, hino])

/-- **`WalsOk` with a WAL's layout replaced by a tail step's** (see the file header). -/
theorem walsOk_tail {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino) (hcut : g.om.cut = none)
    (hlen : g.bs.length = g0.bs.length) (hzf : (∀ z, g0.om.zf = some z → g0.bs.length ≤ z) ∧ SegExact g0 ∧ SegExact g)
    (hZ : TailZeros lay) (hB : TailBound C Mr d lay)
    (habs' : ∀ ents, WalAbsD C Mr d lay ents → WalAbsD C Mr d (tailLay lay pre g wr') ents) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre g wr']> Ls) cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  have hsub : ∀ dir' lay', (<[dir := tailLay lay pre g wr']> Ls) !! dir' = some lay' →
      ∃ lay1, Ls !! dir' = some lay1 ∧ (lay'.segs.map (·.ino)).Sublist (lay1.segs.map (·.ino)) := by
    intro dir' lay' h
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at h; cases h
      refine ⟨lay, hl, ?_⟩
      rw [hs]; simp [tailLay, hino]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      exact ⟨lay', h, List.Sublist.refl _⟩
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => ?_, segsAll_nodup_sub h3 hsub, fun g' hg' => ?_, h5, h6⟩
  · by_cases e : dir' = dir
    · subst e
      rw [hd] at hd'; cases hd'
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, hcr⟩ := h1 dir' d hd
      have e : lay1 = lay := by rw [hl] at hl1; exact (Option.some.inj hl1).symm
      rw [e] at hjr hnm hc habs hcr
      have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 h3).1 dir' lay hl
      exact ⟨tailLay lay pre g wr', nm, hj, GMap.lookup_insert _ _ _, hA, hjr, hnm, hc, habs' _ habs,
        crashOkW_tail hC habs (habs' _ habs) hZ hB hnd hs hino hlen hzf hcr⟩
    · obtain ⟨lay1, nm, hj, hl1, rest⟩ := h1 dir' d' hd'
      exact ⟨lay1, nm, hj, by rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact hl1, rest⟩
  · have e : dir' ≠ dir := by rintro rfl; rw [hd] at hn; cases hn
    rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact h2 dir' hn
  · obtain ⟨dir', lay', hl', hg''⟩ := segsAll_mem hg'
    by_cases e : dir' = dir
    · subst e
      rw [GMap.lookup_insert] at hl'; cases hl'
      simp only [tailLay, List.mem_append, List.mem_singleton] at hg''
      rcases hg'' with hg'' | rfl
      · exact h4 g' (mem_segsAll hl (by rw [hs]; exact List.mem_append_left _ hg''))
      · exact hcut
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hl'
      exact h4 g' (mem_segsAll hl' hg'')

end pure

end WalFs
end EtcdGrove
end Perennial

end
