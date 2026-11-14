/- Lean-first (no Rocq counterpart).

# The crash of a tail registered, not yet zeroed (I3b, `wal-tc16`; pure)

`ReadAll` registers the tail a crash left (`walTailsRes_registerPend`): `wr = z0`, nothing appended
(the stream ends at `wr`), its `old` past `z0` unknown (a torn frame), so no F-Z (`TailZeros`), and
the decoding of a crash over `TailShape` (`crashTo_tailW`, which needs the stamp-0 candidates past `z0`
zero) does not apply. `ReadAll` reaches `ZeroToEnd` only when the decoder stopped with `io.EOF` at `wr`
(decoder.go:95: a zero length word, or the file's end): the 8 bytes of `old` from `wr` are zeros
(`LenZ`; `getD` reads zero past `old`'s end). Every candidate of a byte from `wr` on that the tail's
resizes leave (`WinShape`: `old`'s byte stamped 0, a known resize's zero; no write, the stream ending at
`wr`) is then a zero below `wr + 8`, so every crash image's length word at `wr` is zero or short and
the reader stops there (`decStep_zeroWord`): no W1 is needed, nothing is appended.

* `LenZ`, `TailPend`: the zero length word at `wr`, with `wr = z0`.
* `decStep_zeroWord`: the reader accepts nothing at a zero length word (or short of one).
* `crashTo_tailP`: `crashTo_tailL`'s tree part with the history whole (`I = H`), the image the stream
  below `wr` and the stream's value (zero) on `[wr, wr + 8)`.
* `WalAbsD.pendVals`: every candidate of the last segment below `wr + 8` has the stream's value,
  exact tail or window, given `TailPend` and the stream ending at `wr`.
* `crashOkA_tailPend`: `crashOkA_tailAny` for such a tail (any tail step: a resize's first step, its
  landing, a growth), `TailPend` of the new layout in place of F-Z.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashW

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

/-- **The reader accepts nothing at a zero length word** (or with fewer than 8 bytes left). -/
theorem decStep_zeroWord (C : WalCodec) (last : Bool) {bs : List w8} {off : Nat} {c : w32}
    (hz : ∀ j, j < 8 → bs.getD (off + j) 0 = 0) (r : WalRec) (len : Nat) (c' : w32) :
    decStep C last bs off c ≠ .accept r len c' := by
  unfold decStep
  dsimp only
  by_cases h0 : (bs.drop off).length = 0
  · rw [if_pos h0]; intro h; cases h
  rw [if_neg h0]
  by_cases h8 : (bs.drop off).length < 8
  · rw [if_pos h8]; intro h; cases h
  rw [if_neg h8]
  have ht : (bs.drop off).take 8 = List.replicate 8 (0#8) := by
    rw [List.length_drop] at h8
    exact take8_ext (by simp) (by omega) (fun i hi => by rw [hz i hi, getD_rep8 hi])
  rw [ht, leToU64_zero8, if_pos rfl]
  intro h; cases h

section crash
variable [GooseExts]

/-- **The crash of a tail with nothing appended past its write position** (see the file header): the
tree part from a `CrashTo` of the layout over another image `fo0` of the tail (`crashTo_tailL`'s), the
history whole; the tail's image at least the stream long, the stream's value below `|S| + 8`. -/
theorem crashTo_tailP {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {m' : Tree} {fo fo0 : Ino → Option Fs.OsFile} {g : SegG}
    (habs : WalAbsD C Mr d lay ents) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hg : lay.segs.getLast? = some g)
    (m0 : Nat) (hm0 : segStart lay.cuts lay.cuts.length ≤ m0)
    (h0 : CrashTo C Mr { d with m := m0 } lay m' fo0) (hfo : ∀ i, i ≠ g.ino → fo0 i = fo i)
    (himg : ∀ f, fo g.ino = some f →
      (segStream C Mr d lay.cuts lay.cuts.length).length ≤ f.size ∧
      ∀ b, b < f.size → b < (segStream C Mr d lay.cuts lay.cuts.length).length + 8 →
        f.cache b = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0)
    (hn : g.ino ∈ walInos (entsOf m' lay.j) → (fo g.ino).isSome) :
    CrashTo C Mr d lay m' fo := by
  rcases h0 with hl | ⟨q, I0, hent, hq, hinos, hI0, hLI0, hpur, hmid, -⟩
  · exact Or.inl hl
  have hsorted := habs.cuts.2.1
  have hmH : d.m ≤ d.H.length := habs.synced.1
  have hLm : segStart lay.cuts lay.cuts.length ≤ d.m := habs.lastSynced
  have hgq : (lay.segs.drop q).getLast? = some g := by
    rw [List.getLast?_drop, if_neg (by omega), hg]
  have hgin : g.ino ∈ walInos (entsOf m' lay.j) := by
    rw [hinos]; exact List.mem_map_of_mem (List.mem_of_getLast? hgq)
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hn hgin)
  obtain ⟨hlen, hval⟩ := himg f hf
  have hI0H : I0.length ≤ d.H.length := walImg_length_le hI0
  have hiI0 : initSegs { d with H := I0 } lay.cuts = initSegs d lay.cuts :=
    initSegs_of_take hsorted (walImg_take hI0 hm0)
  have hpur' := Nat.le_min.1 hpur
  refine Or.inr ⟨q, d.H, hent, hq, hinos, ⟨d.H.length, hmH, Nat.le_refl _, Or.inl (by simp)⟩,
    by omega, Nat.le_min.2 ⟨hpur'.1, Nat.le_trans hpur'.2 hI0H⟩, ?_, ?_⟩
  · intro k g' hk hkc
    have hne : g'.ino ≠ g.ino := by
      intro he
      have hcl := habs.cuts.2.2
      have h1 : (lay.segs.map (·.ino))[q + k]? = some g.ino := by
        rw [List.getElem?_map, ← List.getElem?_drop, hk]; simp [he]
      have h2 : (lay.segs.map (·.ino))[lay.segs.length - 1]? = some g.ino := by
        rw [List.getElem?_map, ← List.getLast?_eq_getElem?, hg]; simp
      have hi1 : q + k < (lay.segs.map (·.ino)).length := by
        simp only [List.length_map]; omega
      have hi2 : lay.segs.length - 1 < (lay.segs.map (·.ino)).length := by
        simp only [List.length_map]; omega
      have := hnd.eq_of_getElem?_eq hi1 (h1.trans h2.symm)
      omega
    rw [← hfo g'.ino hne, hmid k g' hk hkc]
    change segStream C Mr { d with H := I0 } lay.cuts (lay.first + q + k) =
      segStream C Mr d lay.cuts (lay.first + q + k)
    unfold segStream
    rw [segRecs_init_congr C Mr (d := d) (d' := { d with H := I0 }) rfl hiI0 hkc]
  · intro g'' hg''
    rw [hg] at hg''
    cases hg''
    change segStream C Mr d lay.cuts lay.cuts.length <+: imgOf (fo g.ino) ∧ ∀ r len c',
      decStep C true (imgOf (fo g.ino)) (segStream C Mr d lay.cuts lay.cuts.length).length _ ≠
        .accept r len c'
    simp only [imgOf, hf, Option.map_some, Option.getD_some]
    generalize segStream C Mr d lay.cuts lay.cuts.length = S at hlen hval ⊢
    refine ⟨prefix_of_getD (by rw [contents_length]; exact hlen) (fun b hb => ?_),
      fun r len c' => decStep_zeroWord C true (fun j hj => ?_) r len c'⟩
    · rw [contents_getD f b (by omega)]; exact hval b (by omega) (by omega)
    · by_cases hb : S.length + j < f.size
      · rw [contents_getD f _ hb, hval _ hb (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega)]; rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [contents_length]; omega)]; rfl

/-- **Every candidate of a pending tail below `wr + 8` has the stream's value** (see the file header):
below `wr` `ByteOk` (`old` is the stream below `z0 = wr`), from `wr` on `WinShape` (`old`'s byte, zero
by `LenZ`, or a resize's zero; no write, the stream ending at `wr`). -/
theorem WalAbsD.pendVals {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (habs : WalAbsD C Mr d lay ents) (hg : lay.segs.getLast? = some g)
    (hP : TailPend lay) (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr) :
    ∀ b (q : w8 × Nat), b < lay.wr + 8 → q ∈ ((segBytesX g).getD b (0, [])).2 →
      q.1 = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0 := by
  obtain ⟨hwz, hLZ⟩ := hP
  obtain ⟨hso, hwS, hbo, hwo, -, hz0, htake, -, hWC⟩ := habs.lastWin g hg
  -- below `wr` (`= z0`, `TailPend`) `ByteOk`: `WalAbsD.low`'s `WinW` arm is past `z0`
  have hB : ∀ b (x : ByteG), g.bs[b]? = some x → b < lay.wr →
      ByteOk ((segStream C Mr d lay.cuts lay.cuts.length).getD b 0) (lay.old.getD b 0)
        (decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length)) (decide (b < lay.wr))
        (decide (b < lay.so)) x := by
    intro b x hx hbw
    rcases habs.low g hg b x hx hbw with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact h
    · have : lay.wr = lay.z0 := hwz
      omega
  intro b q hb hq
  generalize segStream C Mr d lay.cuts lay.cuts.length = S at hS hwS hB htake hWC ⊢
  by_cases hbw : b < lay.wr
  · have hbl : b < g.bs.length := by omega
    rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl,
      Option.getD_some] at hq
    have hx := hB b (g.bs[b]) (List.getElem?_eq_getElem hbl) hbw
    have hold : lay.old.getD b 0 = S.getD b 0 := by
      have h1 := congrArg (fun l => l.getD b 0) htake
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (show b < lay.z0 by omega)]
        at h1
      simp only [List.getD_eq_getElem?_getD]
      exact h1.symm
    unfold ByteOk at hx
    split at hx
    · rw [hx] at hq
      simp only [List.mem_singleton] at hq
      rw [hq]
    · obtain ⟨ex, h1, h2, -, -⟩ := hx
      rw [h1] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hold
      · exact (h2 q hq).1
  · have hbX : b < (segBytesX g).length := by
      refine Nat.lt_of_not_le fun hc => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc] at hq
      simp at hq
    have hSb : S.getD b 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hSb]
    rcases hWC.2 b (by omega) hbX q hq with rfl | ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hLZ (b - lay.wr) (by omega)
      rwa [show lay.wr + (b - lay.wr) = b by omega] at this
    · exact h1
    · omega

/-- **A step on a pending tail keeps the crash condition** (`crashOkA_tailAny` for a tail registered, not
yet zeroed, see the file header): the layouts `lay0` (tail `g0`) and `lay` (tail `g`, same inode) differ
only in the tail's ghost; the old condition at the tail's image as of its last sync, then
`crashTo_tailP` on `lay` (`WalAbsD.pendVals`: `TailPend lay`, the stream ending at `wr`); the new tail's
zeros known from its length on; no alternative layout holds the tail. -/
theorem crashOkA_tailPend {C : WalCodec} {Mr : WalMarshal} {d : WalDur}
    {lay0 lay : WalLay} {ents0 ents : Ents} {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {pre : List SegG} {g0 g : SegG}
    (habs0 : WalAbsD C Mr d lay0 ents0) (habs : WalAbsD C Mr d lay ents)
    (hP : TailPend lay) (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
    (hnd : (lay.segs.map (·.ino)).Nodup)
    (hs0 : lay0.segs = pre ++ [g0]) (hs : lay.segs = pre ++ [g]) (hino : g.ino = g0.ino)
    (hjr : lay.jr = lay0.jr) (hnm : lay.nm = lay0.nm) (hj : lay.j = lay0.j)
    (hcuts : lay.cuts = lay0.cuts) (hfirst : lay.first = lay0.first)
    (hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hzf : ∀ z, g.om.zf = some z → g.bs.length ≤ z)
    (halt : ∀ la, alt = some la → ∀ g' ∈ la.segs, g'.ino ≠ g.ino)
    (hok : CrashOkA C Mr d lay0 alt cl n) : CrashOkA C Mr d lay alt cl n := by
  intro m' fo hr hf hnmd hw
  have hgm : g ∈ lay.segs := by rw [hs]; simp
  have hg : lay.segs.getLast? = some g := by rw [hs]; simp
  have hg0 : lay0.segs.getLast? = some g0 := by rw [hs0]; simp
  have hinos : lay.segs.map (·.ino) = lay0.segs.map (·.ino) := by
    rw [hs, hs0]; simp [hino]
  have hpre : ∀ g' ∈ pre, g'.ino ≠ g.ino := by
    intro g' hg' he
    have hnd' := hnd
    rw [hs, List.map_append, List.nodup_append] at hnd'
    exact hnd'.2.2 _ (List.mem_map_of_mem hg') _ (by simp) he
  have hpreX : ∀ g' ∈ pre, SegExact g' := by
    intro g' hg'
    obtain ⟨-, -, -, -, h5⟩ := habs0.metas g' (by rw [hs0]; simp [hg'])
    rcases h5 with h5 | h5
    · rw [hg0] at h5; cases h5; exact absurd hino.symm (hpre _ hg')
    · exact h5
  let fo0 : Ino → Option Fs.OsFile := fun i =>
    if i = g.ino then (fo i).map (fun _ => syncImg g0.bs g0.bs.length) else fo i
  have hfo : ∀ i, i ≠ g.ino → fo0 i = fo i := fun i hi => by simp [fo0, hi]
  have hfo0g : fo0 g.ino = (fo g.ino).map (fun _ => syncImg g0.bs g0.bs.length) := by simp [fo0]
  have hfc0 : FileCrashedR g0.om [(0, DFrac.own (1 : Qp).half, g0.bs)] (fo0 g0.ino) := by
    rw [← hino, hfo0g]
    refine fileCrashedR_syncImg habs0 hg0 hzf0 (fun f hf' => ?_)
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf'
    rfl
  have hf0 : ∀ g' ∈ lay0.segs, FileCrashedR g'.om [(0, DFrac.own (1 : Qp).half, g'.bs)]
      (fo0 g'.ino) := by
    intro g' hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hf g' (by rw [hs]; simp [hg'])
    · exact hfc0
  have hn0 : ∀ g' ∈ lay0.segs, g'.ino ∈ walInos (entsOf m' lay0.j) → (fo0 g'.ino).isSome := by
    intro g' hg' hnd'
    rw [hs0, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · rw [hfo _ (hpre g' hg')]; exact hnmd g' (by rw [hs]; simp [hg']) (by rw [hj]; exact hnd')
    · rw [← hino, hfo0g, Option.isSome_map]; exact hnmd g hgm (by rw [hino, hj]; exact hnd')
  have hw0 : W1G C (walInos (entsOf m' lay0.j)) (fun i => imgOf (fo0 i)) (segBytesOf lay0)
      (segRzOf lay0) := by
    apply w1G_sync
    intro i bs hbs b hb
    obtain ⟨g', hg', rfl, rfl⟩ := segBytesOf_some hbs
    have hg'' := hg'
    rw [hs0, List.mem_append, List.mem_singleton] at hg''
    rcases hg'' with hgp | rfl
    · have hX := hpreX g' hgp
      rw [segBytesX_of_hi (Nat.le_of_eq hX.2)]
      rw [hfo _ (hpre g' hgp)] at hb ⊢
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hgp
      have hk' : lay0.segs[k]? = some g' := by
        rw [hs0, List.getElem?_append_left ((List.getElem?_eq_some_iff.1 hk).1)]; exact hk
      have hkl : k + 1 < lay0.segs.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; rw [hs0]; simp; omega
      have hint := habs0.intact k g' hkl hk'
      have hdur : ∀ y ∈ g'.bs, y = durB y.1 := by
        rw [hint]; intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
      cases hfg : fo g'.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        have hfc := hf g' (by rw [hs]; simp [hgp])
        rw [hfg] at hfc
        have hc := img_durable hfc hdur hX.1 hX.2
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, hc] at hb ⊢
        simp only [List.length_map] at hb
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hb,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
        simp only [Option.map_some, Option.getD_some]
        rw [hdur _ (List.getElem_mem hb)]
        exact (valAt_durB _).symm
    · rw [← hino, hfo0g] at hb ⊢
      cases hfg : fo g.ino with
      | none => simp [imgOf, hfg] at hb
      | some f' =>
        simp only [imgOf, hfg, Option.map_some, Option.getD_some, syncImg_length] at hb ⊢
        rw [syncImg_getD _ _ _ hb, segBytesX_getD_lt hb]
  rcases hok m' fo0 hr hf0 hn0 hw0 with h | ⟨la, hla, h⟩
  · left
    have h' := crashTo_congr_lay hjr hnm hj hcuts hfirst hinos h
    have hsz := (habs.metas g hgm).1
    obtain ⟨hso, -, -, hwo, -, hz0, -⟩ := habs.lastWin g hg
    have hzf' : ∀ z, g.om.zf = some z → max lay.so lay.z0 ≤ z := fun z hz => by
      have := hzf z hz; omega
    have hV := habs.pendVals hg hP hS
    refine crashTo_tailP habs hnd hg d.m habs.lastSynced h' hfo (fun f hf1 => ?_) (hnmd g hgm)
    obtain ⟨h1, -, h3⟩ := crashImg_tail (by rw [← hf1]; exact hf g hgm) hsz (habs.winLo_any g hg)
      hzf' (habs.hiX hg)
    have hmx : max lay.so lay.z0 = lay.wr := by have := hP.1; omega
    refine ⟨by omega, fun b hb hb8 => ?_⟩
    rcases h3 b hb with ⟨s, hs'⟩ | ⟨hb1, hb2⟩
    · exact hV b _ (by omega) hs'
    · rw [hb2, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · right
    exact ⟨la, hla, crashTo_congr_fo (fun g' hg' => hfo _ (halt la hla g' hg')) h⟩

end crash

end WalFs
end EtcdGrove
end Perennial

end
