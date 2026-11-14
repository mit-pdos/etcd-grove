/- Lean-first (no Rocq counterpart).

# The crash of a tail in a resize window (W6, I3b; pure; W6 log, twenty-third session)

`crashTo_tailL` (`TailCrash.lean`) decodes a crash of an exact tail: the image no longer than its bytes,
each byte one of their candidates (`TailCands`). A write past the preallocated size, and every write
in a resize window after it or after `cut`'s truncate, leaves the tail in a window: a crash may leave it
up to `om.hi` long, its bytes past the size those its `OsMeta` knows (`segBytesX`), and the candidates
from the write position on of the window's shapes (`WinShape`: `old`'s byte stamped 0, a known
resize's zero, the stream's byte stamped by a write). Here the decoding over such candidates:

* `TailShape`: what the decoding needs of the candidates (in place of `TailCands`' exact form): below
  `so` the durable intended byte; from `so` on, each candidate the intended byte or (past `max so z0`)
  a zero, those stamped 0 the byte under the stream, one stamped 0 below `z0`, those of a write (a
  positive stamp no resize's) the intended byte. `TailCands.shape` (exact tails), `tailShape_win`
  (from `ByteOk` below `wr` and `WinShape` from `wr` on).
* `TailShape.vals`/`TailShape.asOf`: the image's values and W1 (`AsOfW`, the resize amendment's: a
  frame as of a change is as of a write) as `tail_decodeV` reads them.
* `crashTo_tailW`: `crashTo_tailL` for a tail in a window (the image up to `segBytesX`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.WinCrash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailStepPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section shape

/-- **The candidates `cs` of a crashed tail's bytes, as the decoding reads them** (see the file header):
the intended stream `X`, the synced offset `so`, the end `z0` of the frames found at the generation's
start, the known resizes' stamps `rz`. -/
structure TailShape (X : Nat → w8) (so z0 : Nat) (rz : List Nat) (cs : Nat → Cands) : Prop where
  synced : ∀ b, b < so → cs b = [(X b, 0)]
  val : ∀ b (q : w8 × Nat), so ≤ b → q ∈ cs b → q.1 = X b ∨ (max so z0 ≤ b ∧ q.1 = 0)
  zero : ∀ b (q : w8 × Nat), so ≤ b → q ∈ cs b → q.2 = 0 → q.1 = if b < z0 then X b else 0
  head : ∀ b, so ≤ b → b < z0 → ∃ q ∈ cs b, q.2 = 0
  pos : ∀ b (q : w8 × Nat), so ≤ b → q ∈ cs b → 0 < q.2 → q.2 ∉ rz → q.1 = X b

variable {X : Nat → w8} {so z0 : Nat} {rz : List Nat} {cs : Nat → Cands}

/-- The image's values (`tail_decodeV`'s `TailVals`): each byte a candidate, or a zero past
`max so z0` (a crash's zero at or past `lo`, `WinLo`, or past the zeros known). -/
theorem TailShape.vals (h : TailShape X so z0 rz cs) {img : List w8}
    (himg : ∀ b, b < img.length →
      (∃ s, (img.getD b 0, s) ∈ cs b) ∨ (max so z0 ≤ b ∧ img.getD b 0 = 0)) :
    TailVals X so z0 img := by
  intro b hb
  rcases himg b hb with ⟨s, hs⟩ | hz
  rotate_left
  · exact .inr hz
  by_cases hbs : b < so
  · rw [h.synced b hbs, List.mem_singleton] at hs
    exact .inl (Prod.mk.inj hs).1
  · exact h.val b _ (by omega) hs

/-- W1 of a frame core (`AsOfW`) as the decoding reads it (`TailAsOf`). -/
theorem TailShape.asOf (h : TailShape X so z0 rz cs) {img : List w8} {o len : Nat}
    (ha : AsOfW cs rz (fun b => img.getD b 0) o len) : TailAsOf X so z0 img o len := by
  rcases ha with ha | ⟨n, hn, ha⟩
  · left
    intro b h1 h2
    have hb := ha b h1 h2
    dsimp only at hb
    rw [hb]
    by_cases hbs : b < so
    · rw [h.synced b hbs, valAt_single, if_pos (by omega)]
    · rw [valAt_latestAt]
      cases hl : latestAt (cs b) 0 with
      | some p =>
        obtain ⟨hpm, hp0⟩ := latestAt_mem hl
        simp only [Option.map_some, Option.getD_some]
        rw [h.zero b p (by omega) hpm (by omega)]
        by_cases hz : b < z0
        · rw [if_pos hz, if_pos (by omega)]
        · rw [if_neg hz, if_neg (by omega)]
      | none =>
        simp only [Option.map_none, Option.getD_none]
        by_cases hz : b < z0
        · exfalso
          obtain ⟨q, hq, hq0⟩ := h.head b (by omega) hz
          unfold latestAt at hl
          rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hl
          exact hl q hq (by simp [hq0])
        · rw [if_neg (by omega)]
  · right
    intro b h1 h2
    obtain ⟨p, hp, hv, hp0, hpr⟩ := ha b h1 h2
    obtain ⟨hpm, -⟩ := latestAt_mem hp
    dsimp only at hv
    rw [hv]
    by_cases hbs : b < so
    · rw [h.synced b hbs, List.mem_singleton] at hpm; subst hpm; simp at hp0
    · exact h.pos b p (by omega) hpm hp0 hpr

/-- An exact tail's candidates (`TailCands`) have the shape, for any resizes known. -/
theorem TailCands.shape {Y : Nat → w8} (h : TailCands X Y cs so z0) (rz : List Nat) :
    TailShape X so z0 rz cs where
  synced := h.synced
  val := fun b q _ hq => h.mem_val (v := q.1) (s := q.2) hq
  zero := by
    intro b q hb hq hq0
    obtain ⟨ex, he, hex⟩ := h.unsynced b hb
    rw [he] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · by_cases hz : b < z0
      · rw [if_pos hz]; exact h.old_lo b hz
      · rw [if_neg hz]; exact h.old_hi b (by omega)
    · have := (hex q hq).2; omega
  head := fun b hb _ => by
    obtain ⟨ex, he, -⟩ := h.unsynced b hb
    exact ⟨_, by rw [he]; exact List.mem_cons_self .., rfl⟩
  pos := fun b q hb hq hq0 _ => by
    obtain ⟨ex, he, hex⟩ := h.unsynced b hb
    rw [he] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simp at hq0
    · exact (hex q hq).1

/-- **A window's candidates have the shape** (`TailWin`'s): below `wr` each byte's `ByteOk`, from `wr`
on each candidate `WinShape`; the stream `S` is `old` below `z0` and `old` zero from `z0` on (F-Z). -/
theorem tailShape_win {S old : List w8} {wr : Nat} (hso : so ≤ wr) (hz0 : z0 ≤ wr)
    (hlow : ∀ b, b < wr → ∃ (y : ByteG) (a w : Bool), cs b = y.2 ∧
      ByteOk (S.getD b 0) (old.getD b 0) a w (decide (b < so)) y)
    (hhi : ∀ b q, wr ≤ b → q ∈ cs b → WinShape S old rz b q)
    (htake : S.take z0 = old.take z0) (hZ : ∀ b, z0 ≤ b → b < old.length → old.getD b 0 = 0) :
    TailShape (fun b => S.getD b 0) so z0 rz cs := by
  have hlo : ∀ b, b < z0 → old.getD b 0 = S.getD b 0 := by
    intro b hb
    have h1 := congrArg (fun l => l.getD b 0) htake
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hb] at h1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]; exact h1.symm
  have hhi0 : ∀ b, z0 ≤ b → old.getD b 0 = 0 := by
    intro b hb
    by_cases hbo : b < old.length
    · exact hZ b hb hbo
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have hold : ∀ b, old.getD b 0 = if b < z0 then S.getD b 0 else 0 := by
    intro b; split
    · exact hlo b (by omega)
    · exact hhi0 b (by omega)
  -- below `wr`, not synced: `(old b, 0)` first, then the stream's byte stamped positive
  have hun : ∀ b, so ≤ b → b < wr → ∃ ex : Cands, cs b = (old.getD b 0, 0) :: ex ∧
      ∀ q ∈ ex, q.1 = S.getD b 0 ∧ 0 < q.2 := by
    intro b h1 h2
    obtain ⟨y, a, w, hc, hy⟩ := hlow b h2
    rw [show decide (b < so) = false by simp; omega] at hy
    simp only [ByteOk, Bool.false_eq_true, ite_false] at hy
    obtain ⟨ex, he, hex, -⟩ := hy
    exact ⟨ex, by rw [hc, he], hex⟩
  refine ⟨fun b hb => ?_, fun b q hb hq => ?_, fun b q hb hq hq0 => ?_, fun b hb hbz => ?_,
    fun b q hb hq hq0 hqr => ?_⟩
  · obtain ⟨y, a, w, hc, hy⟩ := hlow b (by omega)
    rw [show decide (b < so) = true by simp; omega] at hy
    simp only [ByteOk, ite_true] at hy
    rw [hc, hy]
  · by_cases hbw : b < wr
    · obtain ⟨ex, he, hex⟩ := hun b hb hbw
      rw [he] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · dsimp only; rw [hold b]
        split
        · exact .inl rfl
        · exact .inr ⟨by omega, rfl⟩
      · exact .inl (hex q hq).1
    · rcases hhi b q (by omega) hq with rfl | ⟨h1, -⟩ | ⟨-, h1, -⟩
      · dsimp only; exact .inr ⟨by omega, hhi0 b (by omega)⟩
      · exact .inr ⟨by omega, h1⟩
      · exact .inl h1
  · by_cases hbw : b < wr
    · obtain ⟨ex, he, hex⟩ := hun b hb hbw
      rw [he] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hold b
      · have := (hex q hq).2; omega
    · rw [if_neg (by omega)]
      rcases hhi b q (by omega) hq with rfl | ⟨h1, -⟩ | ⟨-, -, h1⟩
      · exact hhi0 b (by omega)
      · exact h1
      · omega
  · obtain ⟨ex, he, -⟩ := hun b hb (by omega)
    exact ⟨_, by rw [he]; exact List.mem_cons_self .., rfl⟩
  · by_cases hbw : b < wr
    · obtain ⟨ex, he, hex⟩ := hun b hb hbw
      rw [he] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · simp at hq0
      · exact (hex q hq).1
    · rcases hhi b q (by omega) hq with rfl | ⟨-, h1⟩ | ⟨-, h1, -⟩
      · simp at hq0
      · exact absurd h1 hqr
      · exact h1

end shape

section crash
variable [GooseExts]

/-- **The crash of a tail in a resize window** (see the file header; `crashTo_tailL` for any tail): the
tail's image `f` at least `max so z0` long, no longer than `segBytesX g`, each byte below its size one of
`segBytesX g`'s candidates, these of the shape the decoding needs (`TailShape`, with the resizes W1 knows
of the tail). -/
theorem crashTo_tailW {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {m' : Tree} {fo fo0 : Ino → Option Fs.OsFile} {g : SegG}
    (habs : WalAbsD C Mr d lay ents) (hB : TailBound C Mr d lay)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hg : lay.segs.getLast? = some g)
    (m0 : Nat) (hm0 : segStart lay.cuts lay.cuts.length ≤ m0)
    (h0 : CrashTo C Mr { d with m := m0 } lay m' fo0) (hfo : ∀ i, i ≠ g.ino → fo0 i = fo i)
    (himg0 : ∀ f, fo g.ino = some f → max lay.so lay.z0 ≤ f.size ∧ f.size ≤ (segBytesX g).length ∧
      ∀ b, b < f.size → (∃ s, (f.cache b, s) ∈ ((segBytesX g).getD b (0, [])).2) ∨
        (max lay.so lay.z0 ≤ b ∧ f.cache b = 0))
    (hn : g.ino ∈ walInos (entsOf m' lay.j) → (fo g.ino).isSome)
    {rzOf : Ino → List Nat}
    (hT : TailShape (fun b => (segStream C Mr d lay.cuts lay.cuts.length).getD b 0) lay.so lay.z0
      (rzOf g.ino) (fun b => ((segBytesX g).getD b (0, [])).2))
    (hw : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay) rzOf) :
    CrashTo C Mr d lay m' fo := by
  rcases h0 with hl | ⟨q, I0, hent, hq, hinos, hI0, hLI0, hpur, hmid, -⟩
  · exact Or.inl hl
  have hsorted := habs.cuts.2.1
  have hLm : segStart lay.cuts lay.cuts.length ≤ d.m := habs.lastSynced
  have hmH : d.m ≤ d.H.length := habs.synced.1
  have hgm : g ∈ lay.segs := List.mem_of_getLast? hg
  -- the tail is named, so kept
  have hgq : (lay.segs.drop q).getLast? = some g := by
    rw [List.getLast?_drop, if_neg (by omega), hg]
  have hgin : g.ino ∈ walInos (entsOf m' lay.j) := by
    rw [hinos]; exact List.mem_map_of_mem (List.mem_of_getLast? hgq)
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hn hgin)
  obtain ⟨hszlo, hsz, hrun⟩ := himg0 f hf
  -- the decoding core
  generalize hR : lastSegRecs C Mr d lay.cuts = R
  have hRS : segStream C Mr d lay.cuts lay.cuts.length = recFrames C R := by rw [← hR]; rfl
  rw [hRS] at hT
  generalize hcs : (fun b => ((segBytesX g).getD b (0, [])).2) = cs at hT
  have himg : ∀ b, b < f.contents.length → (∃ s, (f.contents.getD b 0, s) ∈ cs b) ∨
      (max lay.so lay.z0 ≤ b ∧ f.contents.getD b 0 = 0) := by
    intro b hb
    rw [contents_length] at hb
    rw [contents_getD f b hb, ← hcs]
    exact hrun b hb
  have hlenI : max lay.so lay.z0 ≤ f.contents.length := by rw [contents_length]; exact hszlo
  obtain ⟨jE, hjE, hEb⟩ := hB
  have hRdef : (segRecs C Mr d lay.cuts).getD lay.cuts.length [] = R := hR
  rw [hRdef] at hjE hEb
  have hfit : RecsFit C R := fun r hr => habs.fit r (by
    rw [allRecs_split, hR]; exact List.mem_append_right _ hr)
  have hch : ChainOk C (lastC0 C Mr d lay.cuts) R := hR ▸ chainOk_lastRecs hC Mr d lay.cuts
  -- the synced records (headers included) are below `jE`
  generalize hA : (lastHdr Mr d lay.cuts).length + (((lastOps d lay.cuts).take
    (d.m - segStart lay.cuts lay.cuts.length)).flatMap (opDs Mr)).length = a
  have haR : a ≤ R.length := by
    rw [← hA, ← hR, lastRecs_length]
    have := (flatMap_take_prefix (opDs Mr) (lastOps d lay.cuts)
      (d.m - segStart lay.cuts lay.cuts.length)).length_le
    omega
  have hajE : a ≤ jE := by
    apply take_le_of_frames_le C R haR
    have hs := habs.synced.2
    have e : (segRecs C Mr { d with H := d.H.take d.m } lay.cuts).getD lay.cuts.length [] =
        R.take a := by
      rw [← hA, ← hR]; exact lastRecs_synced C Mr d hsorted hLm
    rw [e] at hs
    rw [hEb]; omega
  have hha : 1 ≤ a := by have := lastHdr_pos Mr d lay.cuts; omega
  -- the image below `max so z0` is the intended stream
  have hV := hT.vals himg
  have hlo' : ∀ b, b < max lay.so lay.z0 → f.contents.getD b 0 = (recFrames C R).getD b 0 := by
    intro b hb
    rcases hV b (by omega) with h | ⟨h1, -⟩
    · exact h
    · omega
  -- W1 along the reader's path, from the fresh reader's
  have hW : ∀ p ∈ acceptsFrom C true f.contents 0 (lastC0 C Mr d lay.cuts),
      TailAsOf (fun b => (recFrames C R).getD b 0) lay.so lay.z0 f.contents p
        (frameCore f.contents p) := by
    have hW0 : ∀ p ∈ acceptsFrom C true f.contents 0 0#32,
        TailAsOf (fun b => (recFrames C R).getD b 0) lay.so lay.z0 f.contents p
          (frameCore f.contents p) := by
      intro p hp
      have hjs : (walInos (entsOf m' lay.j)).drop ((walInos (entsOf m' lay.j)).length - 1) =
          [g.ino] := by
        rw [hinos]
        have hne : lay.segs.drop q ≠ [] := by simp; omega
        rw [List.length_map, ← List.map_drop, drop_length_sub_one' hne]
        simp only [List.map_cons, List.map_nil]
        rw [(List.getLast_eq_iff_getLast?_eq_some _).2 hgq]
      have hp' : (0, p) ∈ acceptsFiles C (((walInos (entsOf m' lay.j)).drop
          ((walInos (entsOf m' lay.j)).length - 1)).map (fun i => imgOf (fo i))) 0#32 := by
        rw [hjs]
        simp only [List.map_cons, List.map_nil, acceptsFiles, imgOf, hf, Option.map_some,
          Option.getD_some, List.mem_map]
        exact ⟨p, hp, rfl⟩
      obtain ⟨x, hx, hxb⟩ := acceptsFiles_bound C _ _ _ hp'
      have h1 := hw _ (0, p) hp' g.ino (segBytesX g) (by rw [hjs]; rfl) (segBytesOf_mem hnd hgm) (by
        show p + frameCore (imgOf (fo g.ino)) p ≤ (segBytesX g).length
        have hl : (imgOf (fo g.ino)).length ≤ (segBytesX g).length := by
          simpa [imgOf, hf, contents_length] using hsz
        rw [hjs] at hx
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx] at hxb; simp only at hxb; omega)
      rw [hjs] at hx
      simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, imgOf, hf, Option.map_some,
        Option.getD_some, Option.some.injEq] at hx
      rw [← hx] at hxb; simp only at hxb
      simp only [imgOf, hf, Option.map_some, Option.getD_some] at h1
      unfold AsOfOneG at h1
      rw [hcs] at h1
      exact hT.asOf h1
    by_cases hc0 : lay.cuts = []
    · rw [hc0, lastC0_nil]; exact hW0
    · -- the first frame is the CRC record, intact: the fresh reader reads as the chained one
      obtain ⟨r0, rs, hR0, ht0⟩ := lastRecs_head_crc C Mr d hc0
      rw [hR] at hR0
      subst hR0
      have hfr0 : frame (C.encRec r0) <+: f.contents := by
        have hpre : frame (C.encRec r0) <+: recFrames C ((r0 :: rs).take jE) := by
          obtain ⟨k, hk⟩ : ∃ k, jE = k + 1 := ⟨jE - 1, by omega⟩
          rw [hk, List.take_succ_cons, recFrames_cons]; exact List.prefix_append _ _
        have hl := hpre.length_le
        rw [hEb] at hl
        apply prefix_of_getD (by omega)
        intro b hb
        rw [hlo' b (by omega), recFrames_cons, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hb, ← List.getD_eq_getElem?_getD]
      obtain ⟨rest, hrest⟩ := hfr0
      have hd := decStep_frame hC true (bs := f.contents) (off := 0) (rest := rest)
        (hfit r0 (List.mem_cons_self ..)) (by rw [List.drop_zero, hrest]) hch.1
      rw [← acceptsFrom_crc0 ht0 hd]
      exact hW0
  obtain ⟨j, hjj, hjR, hpre, hrej⟩ := tail_decodeV hC hfit hch hjE hEb hV hlenI hW
  have hLH : segStart lay.cuts lay.cuts.length ≤ d.H.length := by omega
  have hhdr : (lastHdr Mr d lay.cuts).length ≤ j := by omega
  obtain ⟨nI, hnI⟩ : ∃ nI, nI = j - (lastHdr Mr d lay.cuts).length := ⟨_, rfl⟩
  have hIimg := tailImg_walImg Mr d lay.cuts nI hLm hmH (by omega)
  have hIL := walImg_length_ge hIimg
  have hiI := initSegs_tailImg Mr d nI hsorted hLH
  have hiI0 : initSegs { d with H := I0 } lay.cuts = initSegs d lay.cuts :=
    initSegs_of_take hsorted (walImg_take hI0 hm0)
  have hlastI : lastSegRecs C Mr { d with H := tailImg Mr d lay.cuts nI } lay.cuts = R.take j := by
    rw [lastRecs_tailImg C Mr d _ hsorted hLH, hR, hnI, Nat.add_sub_cancel' hhdr]
  refine Or.inr ⟨q, tailImg Mr d lay.cuts nI, hent, hq, hinos,
    hIimg, by omega, ?_, ?_, ?_⟩
  · exact Nat.le_min.2 ⟨(Nat.le_min.1 hpur).1,
      Nat.le_trans (segStart_le_length hsorted _) (by omega)⟩
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
    change segStream C Mr { d with H := I0 } lay.cuts (lay.first + q + k) = _
    unfold segStream
    rw [segRecs_init_congr C Mr (d := { d with H := I0 })
      (d' := { d with H := tailImg Mr d lay.cuts nI }) rfl
      (hiI.trans hiI0.symm) hkc]
  · intro g'' hg''
    rw [hg] at hg''
    cases hg''
    have e1 : segStream C Mr { d with H := tailImg Mr d lay.cuts nI } lay.cuts lay.cuts.length = recFrames C (R.take j) := by
      show recFrames C (lastSegRecs C Mr _ lay.cuts) = _
      rw [hlastI]
    have e2 := chainEnd_allRecs_split C Mr { d with H := tailImg Mr d lay.cuts nI } lay.cuts
    have e3 : lastC0 C Mr { d with H := tailImg Mr d lay.cuts nI } lay.cuts = lastC0 C Mr d lay.cuts := by
      unfold lastC0; rw [hiI]
    rw [hlastI, e3] at e2
    simp only [imgOf, hf, Option.map_some, Option.getD_some]
    rw [e1]
    refine ⟨hpre, fun r len c' => ?_⟩
    have := hrej r len c'
    rwa [← e2] at this

/-- A candidate list's value as of stamp 0 is one of its candidates' values, or zero. -/
theorem valAt0_casesW (c : Cands) : valAt c 0 = 0 ∨ ∃ s, (valAt c 0, s) ∈ c := by
  cases h : (c.filter (fun q => decide (q.2 ≤ 0))).getLast? with
  | none => left; unfold valAt; rw [h]; rfl
  | some z =>
    right
    refine ⟨z.2, ?_⟩
    have hzm : z ∈ c := (List.mem_filter.1 (List.mem_of_getLast? h)).1
    unfold valAt
    rw [h]
    exact hzm

/-- **The image of a tail `g0` as of its last sync, of its size, is a crash its ghost allows**: below
`wr` a stamp-0 candidate (`ByteOk`'s head); from `wr` on, in a window, a stamp-0 candidate, else a zero
candidate or the zero arm past `lo` (`WinHead`); an exact tail's bytes all `ByteOk`. -/
theorem fileCrashedR_syncImg {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {g0 : SegG} (habs : WalAbsD C Mr d lay ents) (hg0 : lay.segs.getLast? = some g0)
    (hzf : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) {fo : Option Fs.OsFile}
    (hfo : ∀ f, fo = some f → f = syncImg g0.bs g0.bs.length) :
    FileCrashedR g0.om [(0, DFrac.own (1 : Qp).half, g0.bs)] fo := by
  intro f' hf'
  rw [hfo f' hf']
  have hsz' : (syncImg g0.bs g0.bs.length).size = g0.bs.length := rfl
  obtain ⟨hm1, -, hm3, hm4, -⟩ := habs.metas g0 (List.mem_of_getLast? hg0)
  refine ⟨⟨_, rfl⟩, by omega, by omega, ?_, ?_, fun b c hb _ hb2 => absurd hb2 (by omega)⟩
  · intro r hr k hk hks
    rw [List.mem_singleton] at hr; subst hr
    simp only [Nat.zero_add] at hks ⊢
    rw [syncImg_cache g0.bs g0.bs.length k (show k < g0.bs.length by omega)]
    have e : g0.bs.getD k (0, []) = g0.bs[k]'hk := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rw [e]
    by_cases hx : SegExact g0
    · obtain ⟨-, -, -, -, hbytes, -⟩ := (habs.last g0 hg0).1 hx
      exact .inl (valAt_mem0 (hbytes k (g0.bs[k]'hk) (List.getElem?_eq_getElem hk)).head0)
    · have hwin := habs.lastWin g0 hg0
      by_cases hkw : k < lay.wr
      · obtain ⟨-, -, -, -, hbytes, -⟩ := hwin
        exact .inl (valAt_mem0 (hbytes k (g0.bs[k]'hk) (List.getElem?_eq_getElem hk) hkw).head0)
      · have hhd := habs.winHead g0 hg0 hx
        rcases valAt0_casesW (g0.bs[k]'hk).2 with h0 | h0
        · have hkX : k < (segBytesX g0).length := Nat.lt_of_lt_of_le hk segBytesX_length_le
          rcases hhd k (by omega) hkX with hl | ⟨s0, hs0⟩
          · exact .inr ⟨by omega, h0⟩
          · rw [segBytesX_getD_lt hk, e] at hs0
            exact .inl ⟨s0, by rw [h0]; exact hs0⟩
        · exact .inl h0
  · intro z hz b hzb hb
    have := hzf z hz; omega

/-- **A crash of a tail, its bytes**: below its size each byte a candidate of `segBytesX g` or a zero
past `max so z0` (at or past `lo`, `WinLo`; past the zeros known), given the size within `segBytesX`. -/
theorem crashImg_tail {g : SegG} {so z0 : Nat} {f : Fs.OsFile}
    (hfc : FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (some f))
    (hsz : g.om.size = g.bs.length) (hlo : max so z0 ≤ g.om.lo)
    (hzf : ∀ z, g.om.zf = some z → max so z0 ≤ z) (hhiX : g.om.hi ≤ (segBytesX g).length) :
    max so z0 ≤ f.size ∧ f.size ≤ (segBytesX g).length ∧
      ∀ b, b < f.size → (∃ s, (f.cache b, s) ∈ ((segBytesX g).getD b (0, [])).2) ∨
        (max so z0 ≤ b ∧ f.cache b = 0) := by
  obtain ⟨-, hflo, hfhi, hrun, hzfc, htc⟩ := hfc f rfl
  refine ⟨by omega, by omega, fun b hb => ?_⟩
  by_cases hbg : b < g.bs.length
  · have := hrun (0, DFrac.own (1 : Qp).half, g.bs) (List.mem_singleton_self _) b hbg
      (by simp only [Nat.zero_add]; exact hb)
    simp only [Nat.zero_add] at this
    rcases this with ⟨s, hs'⟩ | ⟨h1, h2⟩
    · left; refine ⟨s, ?_⟩
      rw [segBytesX_getD_lt hbg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbg,
        Option.getD_some]
      exact hs'
    · right; exact ⟨by omega, h2⟩
  · have hbX : b < (segBytesX g).length := by omega
    have hy := segBytesX_getElem?_ge (g := g) (by omega) (List.getElem?_eq_getElem hbX)
    rcases OsMeta.pc_some hy.2 with ht | ⟨z, hz, hzb, -⟩
    · rcases htc b _ (by omega) ht hb with ⟨s, hs'⟩ | ⟨h1, h2⟩
      · left; refine ⟨s, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbX, Option.getD_some]
        exact hs'
      · right; exact ⟨by omega, h2⟩
    · have := hzf z hz
      right; exact ⟨by omega, hzfc z hz b hzb hb⟩

/-- **A step on the tail, any window, keeps the crash condition** (W6 log, twenty-third session; the
`crashOkA_tail` pattern for a tail in a window, before or after): the layouts `lay0` (tail `g0`) and
`lay` (tail `g`, same inode) differ only in the tail's ghost and the write position; the old condition
at the tail's image as of its last sync (`fileCrashedR_syncImg`), then `crashTo_tailW` on `lay` with the
new tail's candidates' shape (`hT`), its least crash size and its zeros known past `max so z0` and its
`segBytesX` reaching `hi`; no alternative layout holds the tail. -/
theorem crashOkA_tailW {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay0 lay : WalLay} {ents0 ents : Ents} {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {pre : List SegG} {g0 g : SegG}
    (habs0 : WalAbsD C Mr d lay0 ents0) (habs : WalAbsD C Mr d lay ents)
    (hB : TailBound C Mr d lay) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hs0 : lay0.segs = pre ++ [g0]) (hs : lay.segs = pre ++ [g]) (hino : g.ino = g0.ino)
    (hjr : lay.jr = lay0.jr) (hnm : lay.nm = lay0.nm) (hj : lay.j = lay0.j)
    (hcuts : lay.cuts = lay0.cuts) (hfirst : lay.first = lay0.first)
    (hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hzf : ∀ z, g.om.zf = some z → max lay.so lay.z0 ≤ z) (hlo : max lay.so lay.z0 ≤ g.om.lo)
    (hhiX : g.om.hi ≤ (segBytesX g).length)
    (hT : TailShape (fun b => (segStream C Mr d lay.cuts lay.cuts.length).getD b 0) lay.so lay.z0
      g.om.rz (fun b => ((segBytesX g).getD b (0, [])).2))
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
    refine crashTo_tailW hC habs hB hnd hg d.m habs.lastSynced h' hfo
      (fun f hf1 => crashImg_tail (by rw [← hf1]; exact hf g hgm) hsz hlo hzf hhiX)
      (hnmd g hgm) (rzOf := segRzOf lay) ?_ hw
    rw [segRzOf_of_mem hnd hgm]; exact hT
  · right
    exact ⟨la, hla, crashTo_congr_fo (fun g' hg' => hfo _ (halt la hla g' hg')) h⟩


/-- **The last segment's candidates have the decoding's shape** (`TailShape`, over `segBytesX`), window
or not, given F-Z: below `wr` `ByteOk`, from `wr` on `WinShape` (`WinCands`; an exact tail's unsynced
bytes, `ByteOk.winShape`), nothing past `segBytesX`. -/
theorem WalAbsD.tailShape {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (habs : WalAbsD C Mr d lay ents) (hZ : TailZeros lay)
    (hg : lay.segs.getLast? = some g) :
    TailShape (fun b => (segStream C Mr d lay.cuts lay.cuts.length).getD b 0) lay.so lay.z0
      g.om.rz (fun b => ((segBytesX g).getD b (0, [])).2) := by
  obtain ⟨hso, hwS, hbo, hwo, hB, hz0, htake, -, hWC⟩ := habs.lastWin g hg
  refine tailShape_win (wr := lay.wr) hso hz0 (fun b hb => ?_) (fun b q hb hq => ?_) htake hZ
  · have hbl : b < g.bs.length := by omega
    refine ⟨g.bs[b], decide (b < (segStream C Mr d lay.cuts lay.cuts.length).length),
      decide (b < lay.wr), ?_, hB b _ (List.getElem?_eq_getElem hbl) hb⟩
    rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl,
      Option.getD_some]
  · by_cases hbX : b < (segBytesX g).length
    · exact hWC.2 b hb hbX q hq
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hq
      simp at hq

/-- **A crash leaves the last segment no longer than `segBytesX`** (an exact tail's `hi` is its
length; a window's `WinCands`). -/
theorem WalAbsD.hiX {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (habs : WalAbsD C Mr d lay ents) (hg : lay.segs.getLast? = some g) :
    g.om.hi ≤ (segBytesX g).length :=
  (habs.lastWin g hg).2.2.2.2.2.2.2.2.1

/-- **A step on the tail keeps the crash condition, from the static relations alone** (`crashOkA_tailW`
with the new tail's facts from `WalAbsD`: `tailShape`, `winLo_any`, `hiX`): the new tail's zeros known
from its length on (`hzf`, `MetaOk.zf`'s), F-Z of the new layout. -/
theorem crashOkA_tailAny {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay0 lay : WalLay} {ents0 ents : Ents} {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {pre : List SegG} {g0 g : SegG}
    (habs0 : WalAbsD C Mr d lay0 ents0) (habs : WalAbsD C Mr d lay ents) (hZ : TailZeros lay)
    (hB : TailBound C Mr d lay) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hs0 : lay0.segs = pre ++ [g0]) (hs : lay.segs = pre ++ [g]) (hino : g.ino = g0.ino)
    (hjr : lay.jr = lay0.jr) (hnm : lay.nm = lay0.nm) (hj : lay.j = lay0.j)
    (hcuts : lay.cuts = lay0.cuts) (hfirst : lay.first = lay0.first)
    (hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z)
    (hzf : ∀ z, g.om.zf = some z → g.bs.length ≤ z)
    (halt : ∀ la, alt = some la → ∀ g' ∈ la.segs, g'.ino ≠ g.ino)
    (hok : CrashOkA C Mr d lay0 alt cl n) : CrashOkA C Mr d lay alt cl n := by
  have hg : lay.segs.getLast? = some g := by rw [hs]; simp
  obtain ⟨hso, -, -, hwo, -, hz0, -⟩ := habs.lastWin g hg
  exact crashOkA_tailW hC habs0 habs hB hnd hs0 hs hino hjr hnm hj hcuts hfirst hzf0
    (fun z hz => by have := hzf z hz; omega) (habs.winLo_any g hg) (habs.hiX hg)
    (habs.tailShape hZ hg) halt hok


/-- **A step on the tail, any window, keeps `CrashOkW`** (`crashOkW_tail` over `crashOkA_tailAny`: no
exactness asked of either tail). -/
theorem crashOkW_tailW {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents ents' : Ents} {pre : List SegG} {g0 g : SegG} {wr' : Nat} {cl : List Claim} {n : Nat}
    (habs : WalAbsD C Mr d lay ents) (habs' : WalAbsD C Mr d (tailLay lay pre g wr') ents')
    (hZ : TailZeros (tailLay lay pre g wr')) (hB : TailBound C Mr d (tailLay lay pre g wr'))
    (hnd : (lay.segs.map (·.ino)).Nodup)
    (hs : lay.segs = pre ++ [g0]) (hino : g.ino = g0.ino)
    (hzf0 : ∀ z, g0.om.zf = some z → g0.bs.length ≤ z) (hzf : ∀ z, g.om.zf = some z → g.bs.length ≤ z)
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
  refine ⟨alt, fun lay0 h => ?_, crashOkA_tailAny hC habs habs' hZ hB hnd' hs rfl hino rfl rfl rfl rfl rfl
    hzf0 hzf ?_ hA⟩
  · obtain ⟨h1, h2, h3, h4, -, -⟩ := halt lay0 h
    have hp := hpre lay0 h
    refine ⟨h1, h2, h3, h4, hp.trans (List.prefix_append _ _), ?_⟩
    have := hp.length_le; simp [tailLay]; omega
  · intro la h g' hg' he
    have hg'p : g' ∈ pre := (hpre la h).subset hg'
    rw [hs, List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 g'.ino (List.mem_map_of_mem hg'p) g0.ino (by simp) (by rw [he, hino])


end crash

end WalFs
end EtcdGrove
end Perennial

end
