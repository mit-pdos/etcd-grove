/- Lean-first (no Rocq counterpart).

# The crash of a tail whose frame at `wr` the reader rejects, under a truncate (L4; pure)

`Repair` truncates the last segment of an idle WAL at its write position `wr` (the stream's end) when the
decoder found a torn frame there (`io.ErrUnexpectedEOF`): the length word at `wr` is in general nonzero,
so `TailPend` (`TailCrashPend.lean`) does not hold, and a crash may leave the bytes past `wr` mixed of
the durable image's and the truncate's zeros (the W7-W12 log, eleventh session, L4's finding). The
argument (the coordinator's, the W7-W12 log, twelfth session): every candidate of a byte from `wr` on is
the durable one (stamp 0) or a resize's zero (its stamp among the file's resize stamps), nothing being
written past the stream (`WinShape`, the stream ending at `wr`). W1's exact form (`AsOfW`) accepts a
frame at `wr` only if

* every byte of its core is its value as of the last sync: then the core is the durable image's frame
  at `wr` (`RepOld`: the stamp-0 values from `wr` on are `old`'s, the segment no longer than `old`),
  which the reader rejects (`WalAbsD.tailStop`: nothing appended, `z0 = wr = |S|`; the decoder reads only
  the core and the length, `decStep_congr`); or
* every byte's candidate as of some change `n > 0` is stamped by a change that is no resize: impossible
  at `wr`, whose candidates are stamped 0 or by a resize.

So the reader stops at `wr` in every crash image, whatever mix of the durable bytes and the zeros it keeps.
No decoder evidence from the program is needed: `tailStop` is the invariant's (a crash's `wr = z0 =
|S|`). The segment must stay no longer than `old` (`RepOld`): a growth's zeros past `old` could complete
a frame the durable image tears short.

* `RepOld` (now `Inv.lean`'s, the lent registry's channel): `wr = z0`, and from `wr` on each byte the segment may leave lies within `old` and reads `old`'s
  byte as of the last sync; every exact tail with `wr = z0` has it (`TailLast.repOld`); a truncate's first
  step (`RzCands`: zeros appended with stamps `> 0`) and its landing keep it (`repOld_rzSeg`,
  `repOld_rzLand`).
* `decStep_congr`: the reader's step depends on the core and the file's length only.
* `acceptsFrom_frames_sub`: a reader at the end of intended frames is on the path of the reader from
  their start.
* `crashTo_tailR`, `crashOkA_tailRep`: `crashTo_tailP`/`crashOkA_tailPend` with `RepOld` in place of
  `TailPend`, through W1.
* `tailCrashStep_rzStartR`, `rzStart_pureR`: the truncate's first step at `wr` from such a tail.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSupPend
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrash

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

/-! ## The reader -/

/-- **The reader's step depends on the core and the file's length only**: a file at least as long that
agrees on the core of an accepted frame accepts it too. -/
theorem decStep_congr {C : WalCodec} {last : Bool} {bs bs' : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (h : decStep C last bs off c = .accept r len c')
    (hl : bs.length ≤ bs'.length)
    (hv : ∀ b, off ≤ b → b < off + frameCore bs off → bs'.getD b 0 = bs.getD b 0) :
    decStep C last bs' off c = .accept r len c' := by
  have hcb := decStep_core_bound h
  have hrb := decStep_rec_bound h
  have ht : (bs'.drop off).take (frameCore bs off) = (bs.drop off).take (frameCore bs off) := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]; omega
    · intro i h1 h2
      simp only [List.length_take, List.length_drop] at h1 h2
      have := hv (off + i) (by omega) (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
      simp only [Option.getD_some] at this
      simp only [List.getElem_take, List.getElem_drop]
      exact this
  have hfc : 8 ≤ frameCore bs off := by unfold frameCore; omega
  have h8 : (bs'.drop off).take 8 = (bs.drop off).take 8 := by
    have e1 := congrArg (List.take 8) ht
    rwa [List.take_take, List.take_take, Nat.min_eq_left hfc] at e1
  have hdc : ((bs'.drop off).drop 8).take (frameCore bs off - 8) =
      ((bs.drop off).drop 8).take (frameCore bs off - 8) := by
    have e1 := congrArg (List.drop 8) ht
    rwa [List.drop_take, List.drop_take] at e1
  unfold frameCore at hdc
  rw [Nat.add_sub_cancel_left] at hdc
  unfold decStep at h ⊢
  simp only at h ⊢
  split at h; · cases h
  split at h; · cases h
  rename_i h1 h2
  rw [h8]
  split at h; · cases h
  rename_i h3
  split at h; · cases h
  rename_i h4
  split at h; · cases h
  rename_i h5
  have hd : (((bs'.drop off).drop 8).take ((decodeFrameSize (leToU64 ((bs.drop off).take 8))).1 +
        (decodeFrameSize (leToU64 ((bs.drop off).take 8))).2)).take
        (decodeFrameSize (leToU64 ((bs.drop off).take 8))).1 =
      (((bs.drop off).drop 8).take ((decodeFrameSize (leToU64 ((bs.drop off).take 8))).1 +
        (decodeFrameSize (leToU64 ((bs.drop off).take 8))).2)).take
        (decodeFrameSize (leToU64 ((bs.drop off).take 8))).1 := by
    rw [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _), hdc]
  have hl' : (bs.drop off).length ≤ (bs'.drop off).length := by
    simp only [List.length_drop]; omega
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h3,
    ite_eq_right (by omega), ite_eq_right (by omega), hd]
  split at h
  · cases h
  · rename_i r0 _
    by_cases ht : r0.typ ≠ crcType
    · rw [if_pos ht] at h ⊢
      by_cases hc : r0.crc = C.crc32c c r0.data
      · rw [if_pos hc] at h ⊢; exact h
      · rw [if_neg hc] at h; cases h
    · rw [if_neg ht] at h ⊢; exact h

/-- **A reader at the end of intended frames is on the path of the reader from their start** (the
frames of `R` from `off`, their CRCs a chain from `c0`). -/
theorem acceptsFrom_frames_sub {C : WalCodec} (hC : C.Ok) {last : Bool} {img : List w8} :
    ∀ (R : List WalRec) (off : Nat) (c0 : w32), RecsFit C R → ChainOk C c0 R →
      (∃ t, img.drop off = recFrames C R ++ t) →
      ∀ p ∈ acceptsFrom C last img (off + (recFrames C R).length) (chainEnd C c0 R),
        p ∈ acceptsFrom C last img off c0
  | [], off, c0, _, _, _, p, hp => by simpa [recFrames_nil, chainEnd] using hp
  | r :: rs, off, c0, hfit, hch, ⟨t, ht⟩, p, hp => by
    have hbs : img.drop off = frame (C.encRec r) ++ (recFrames C rs ++ t) := by
      rw [ht, recFrames_cons, List.append_assoc]
    have hd := decStep_frame hC last (hfit r (List.mem_cons_self ..)) hbs hch.1
    rw [acceptsFrom_accept hd]
    apply List.mem_cons_of_mem
    have ht' : img.drop (off + (frame (C.encRec r)).length) = recFrames C rs ++ t := by
      rw [← List.drop_drop, hbs, List.drop_left]
    refine acceptsFrom_frames_sub hC rs _ _ (fun x hx => hfit x (List.mem_cons_of_mem _ hx)) hch.2
      ⟨t, ht'⟩ p ?_
    rw [recFrames_cons, List.length_append, ← Nat.add_assoc] at hp
    exact hp

/-! ## The tail's durable bytes past `wr` -/

section rep
variable [GooseExts]

/-- **An exact tail with `wr = z0` has `RepOld`**: past `wr` its bytes are unsynced, `old`'s byte
stamped 0 first, then writes' candidates stamped `> 0` (`ByteOk`); the segment is `old` long. -/
theorem TailLast.repOld {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {g : SegG}
    (h : TailLast C Mr d lay g) (hx : SegExact g) (hwz : lay.wr = lay.z0) :
    ∀ b, lay.wr ≤ b → b < (segBytesX g).length →
      b < lay.old.length ∧ valAt ((segBytesX g).getD b (0, [])).2 0 = lay.old.getD b 0 := by
  obtain ⟨hso, -, hlen, -, hB, -⟩ := h
  have hX : segBytesX g = g.bs := segBytesX_of_hi (Nat.le_of_eq hx.2)
  intro b hb1 hb2
  rw [hX] at hb2 ⊢
  refine ⟨by omega, ?_⟩
  have hok := hB b (g.bs[b]) (List.getElem?_eq_getElem hb2)
  rw [show decide (b < lay.so) = false from decide_eq_false (by omega)] at hok
  obtain ⟨ex, he, hex, -, -⟩ := hok
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb2, Option.getD_some, he]
  exact valAt_head_zero (fun q hq => (hex q hq).2)

theorem WalAbsD.repOld {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (habs : WalAbsD C Mr d lay ents) (hex : TailExact lay) (hwz : lay.wr = lay.z0) : RepOld lay :=
  ⟨hwz, fun g hg => (habs.lastEx hex g hg).repOld (hex g hg) hwz⟩

/-- A resize's zero, stamped `> 0`, leaves the value as of the last sync. -/
theorem valAt0_rzCands {rz : List Nat} {cs cs' : Cands} (h : RzCands rz cs cs') :
    valAt cs' 0 = valAt cs 0 := by
  rcases h with rfl | ⟨n, hn, -, rfl⟩
  · rfl
  · unfold valAt
    rw [List.filter_append, List.filter_cons_of_neg (by simp; omega), List.filter_nil,
      List.append_nil]

/-- **`RepOld` across a resize's first step** (`segBytesX` as long, each byte's candidates the old ones
or with a resize's zero appended, `segBytesX_rzSeg`'s form). -/
theorem repOld_rzCands {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (hs : lay.segs = pre ++ [g0]) (hwr : wr' = lay.wr) (hR : RepOld lay)
    (hlen : (segBytesX g).length = (segBytesX g0).length)
    (hc : ∀ b, b < (segBytesX g0).length →
      RzCands g.om.rz ((segBytesX g0).getD b (0, [])).2 ((segBytesX g).getD b (0, [])).2) :
    RepOld (tailLay lay pre g wr') := by
  subst hwr
  refine ⟨hR.1, fun g' hg' b hb1 hb2 => ?_⟩
  simp only [tailLay, List.getLast?_concat, Option.some.injEq] at hg'
  subst hg'
  have hg0 : lay.segs.getLast? = some g0 := by rw [hs]; simp
  obtain ⟨h1, h2⟩ := hR.2 g0 hg0 b hb1 (by rw [← hlen]; exact hb2)
  exact ⟨h1, by rw [valAt0_rzCands (hc b (by rw [← hlen]; exact hb2)), h2]; rfl⟩

/-- **`RepOld` across a step that keeps each byte's candidates** (a truncate's landing,
`segBytesX_rzLand`). -/
theorem repOld_sameCands {lay : WalLay} {pre : List SegG} {g0 g : SegG} {wr' : Nat}
    (hs : lay.segs = pre ++ [g0]) (hwr : wr' = lay.wr) (hR : RepOld lay)
    (hc : (segBytesX g).map (·.2) = (segBytesX g0).map (·.2)) :
    RepOld (tailLay lay pre g wr') := by
  have hlen : (segBytesX g).length = (segBytesX g0).length := by
    have := congrArg List.length hc; simpa using this
  refine repOld_rzCands hs hwr hR hlen (fun b hb => Or.inl ?_)
  have e1 := congrArg (fun l => l.getD b []) hc
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at e1 ⊢
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hb] at e1 ⊢
  simpa using e1

end rep

section crash
variable [GooseExts]

/-- **Every candidate of a tail with `wr = z0` below `wr` has the stream's value** (`WalAbsD.pendVals`'s
first half: `ByteOk` below `wr = z0`). -/
theorem WalAbsD.repValsLo {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (habs : WalAbsD C Mr d lay ents) (hg : lay.segs.getLast? = some g)
    (hwz : lay.wr = lay.z0) :
    ∀ b (q : w8 × Nat), b < lay.wr → q ∈ ((segBytesX g).getD b (0, [])).2 →
      q.1 = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0 := by
  obtain ⟨hso, hwS, hbo, hwo, -, hz0, htake, -, -⟩ := habs.lastWin g hg
  intro b q hbw hq
  generalize hSd : segStream C Mr d lay.cuts lay.cuts.length = S at hwS htake ⊢
  have hbl : b < g.bs.length := by omega
  rw [segBytesX_getD_lt hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl,
    Option.getD_some] at hq
  have hx : ByteOk (S.getD b 0) (lay.old.getD b 0) (decide (b < S.length)) (decide (b < lay.wr))
      (decide (b < lay.so)) (g.bs[b]) := by
    rcases habs.low g hg b (g.bs[b]) (List.getElem?_eq_getElem hbl) hbw with ⟨-, h⟩ | ⟨-, h, -⟩
    · rw [← hSd]; exact h
    · omega
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

/-- **The crash of a tail whose frame at `wr` is the durable image's** (see the file header): the tree
part from a `CrashTo` of the layout over another image `fo0` of the tail (`crashTo_tailP`'s), the history
whole; the tail's image at least the stream long and no longer than `segBytesX`, the stream below `wr`;
the reader's stop at `wr` from W1 (`hw`) and `RepOld`. -/
theorem crashTo_tailR {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {m' : Tree} {fo fo0 : Ino → Option Fs.OsFile} {g : SegG}
    (habs : WalAbsD C Mr d lay ents) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hg : lay.segs.getLast? = some g) (hR : RepOld lay)
    (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
    (m0 : Nat) (hm0 : segStart lay.cuts lay.cuts.length ≤ m0)
    (h0 : CrashTo C Mr { d with m := m0 } lay m' fo0) (hfo : ∀ i, i ≠ g.ino → fo0 i = fo i)
    (himg : ∀ f, fo g.ino = some f →
      lay.wr ≤ f.size ∧ f.size ≤ (segBytesX g).length ∧
      ∀ b, b < lay.wr → f.cache b = (segStream C Mr d lay.cuts lay.cuts.length).getD b 0)
    (hn : g.ino ∈ walInos (entsOf m' lay.j) → (fo g.ino).isSome)
    (hw : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay)
      (segRzOf lay)) :
    CrashTo C Mr d lay m' fo := by
  rcases h0 with hl | ⟨q, I0, hent, hq, hinos, hI0, hLI0, hpur, hmid, -⟩
  · exact Or.inl hl
  have hsorted := habs.cuts.2.1
  have hmH : d.m ≤ d.H.length := habs.synced.1
  have hgm : g ∈ lay.segs := List.mem_of_getLast? hg
  have hgq : (lay.segs.drop q).getLast? = some g := by
    rw [List.getLast?_drop, if_neg (by omega), hg]
  have hgin : g.ino ∈ walInos (entsOf m' lay.j) := by
    rw [hinos]; exact List.mem_map_of_mem (List.mem_of_getLast? hgq)
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hn hgin)
  obtain ⟨hlen, hszX, hval⟩ := himg f hf
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
      decStep C true (imgOf (fo g.ino)) (segStream C Mr d lay.cuts lay.cuts.length).length
        (WalEnc.chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts))) ≠
        .accept r len c'
    have himgf : imgOf (fo g.ino) = f.contents := by simp only [imgOf, hf, Option.map_some, Option.getD_some]
    rw [himgf]
    have hpreS : segStream C Mr d lay.cuts lay.cuts.length <+: f.contents :=
      prefix_of_getD (by rw [contents_length]; omega) (fun b hb => by
        rw [contents_getD f b (by omega)]; exact hval b (by omega))
    refine ⟨hpreS, fun r len c' hd => ?_⟩
    have hd0 := hd
    -- the fresh reader's path reaches `wr`
    generalize hR' : lastSegRecs C Mr d lay.cuts = R
    have hSR : segStream C Mr d lay.cuts lay.cuts.length = recFrames C R := by rw [← hR']; rfl
    have hfit : RecsFit C R := fun r hr => habs.fit r (by
      rw [allRecs_split, hR']; exact List.mem_append_right _ hr)
    have hch : ChainOk C (lastC0 C Mr d lay.cuts) R := hR' ▸ chainOk_lastRecs hC Mr d lay.cuts
    rw [chainEnd_allRecs_split, hR', hSR] at hd
    rw [hSR] at hpreS
    obtain ⟨t, ht⟩ := hpreS
    have hp1 : (recFrames C R).length ∈ acceptsFrom C true f.contents 0 (lastC0 C Mr d lay.cuts) := by
      refine acceptsFrom_frames_sub hC R 0 _ hfit hch ⟨t, by rw [List.drop_zero, ht]⟩ _ ?_
      rw [Nat.zero_add, acceptsFrom_accept hd]; exact List.mem_cons_self ..
    have hp0 : (recFrames C R).length ∈ acceptsFrom C true f.contents 0 0#32 := by
      by_cases hc0 : lay.cuts = []
      · rw [hc0, lastC0_nil] at hp1; exact hp1
      · obtain ⟨r0, rs, hR0, ht0⟩ := lastRecs_head_crc C Mr d hc0
        rw [hR'] at hR0
        subst hR0
        have hdr := decStep_frame hC true (bs := f.contents) (off := 0)
          (rest := recFrames C rs ++ t) (hfit r0 (List.mem_cons_self ..))
          (by rw [List.drop_zero, ← ht, recFrames_cons, List.append_assoc]) hch.1
        rw [acceptsFrom_crc0 ht0 hdr]
        exact hp1
    -- W1 at the last file
    have hjs : (walInos (entsOf m' lay.j)).drop ((walInos (entsOf m' lay.j)).length - 1) =
        [g.ino] := by
      rw [hinos]
      have hne : lay.segs.drop q ≠ [] := by simp; omega
      rw [List.length_map, ← List.map_drop, drop_length_sub_one' hne]
      simp only [List.map_cons, List.map_nil]
      rw [(List.getLast_eq_iff_getLast?_eq_some _).2 hgq]
    have hp' : (0, (recFrames C R).length) ∈ acceptsFiles C (((walInos (entsOf m' lay.j)).drop
        ((walInos (entsOf m' lay.j)).length - 1)).map (fun i => imgOf (fo i))) 0#32 := by
      rw [hjs]
      simp only [List.map_cons, List.map_nil, acceptsFiles, himgf, List.mem_map]
      exact ⟨_, hp0, rfl⟩
    have hcore := decStep_core_bound hd
    have hcore8 : 8 ≤ frameCore f.contents (recFrames C R).length := by
      unfold frameCore; omega
    rw [contents_length] at hcore
    have h1 := hw _ _ hp' g.ino (segBytesX g) (by rw [hjs]; rfl) (segBytesOf_mem hnd hgm) (by
      show (recFrames C R).length + frameCore (imgOf (fo g.ino)) (recFrames C R).length ≤ _
      rw [himgf]; omega)
    rw [segRzOf_of_mem hnd hgm] at h1
    simp only [himgf] at h1
    unfold AsOfOneG at h1
    rw [← hSR, hS] at h1 hcore hcore8 hd
    rw [hS] at hd0
    rcases h1 with h1 | ⟨n, hn0, h1⟩
    · -- as of the last sync: the durable image's frame, which the reader rejects
      have hXo : (segBytesX g).length ≤ lay.old.length := by
        have := (hR.2 g hg ((segBytesX g).length - 1) (by omega) (by omega)).1
        omega
      have hold := decStep_congr (bs' := lay.old) hd0 (by rw [contents_length]; omega)
        (fun b hb1 hb2 => by
          have e := h1 b hb1 hb2
          simp only at e
          rw [e]; exact ((hR.2 g hg b hb1 (by omega)).2).symm)
      rw [hR.1] at hold
      exact habs.tailStop (by rw [← hR.1, hS]) r len c' hold
    · -- as of a change: the candidate at `wr` stamped by a write, but none is
      obtain ⟨p, hp, -, hp0, hpr⟩ := h1 lay.wr (Nat.le_refl _) (by omega)
      have hpm := (latestAt_mem hp).1
      obtain ⟨-, -, -, -, -, -, -, -, -, hWC⟩ := habs.lastWin g hg
      rcases hWC lay.wr (Nat.le_refl _) (by omega) p hpm with h | ⟨-, h⟩ | ⟨h, -⟩
      · rw [h] at hp0; exact absurd hp0 (Nat.lt_irrefl 0)
      · exact hpr h
      · omega

/-- **A step on a tail whose frame at `wr` is the durable image's keeps the crash condition**
(`crashOkA_tailPend` with `RepOld` of the new layout in place of `TailPend`, see the file header): the
old condition at the tail's image as of its last sync, then `crashTo_tailR` on `lay` (W1). -/
theorem crashOkA_tailRep {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay0 lay : WalLay} {ents0 ents : Ents} {alt : Option WalLay} {cl : List Claim} {n : Nat}
    {pre : List SegG} {g0 g : SegG}
    (habs0 : WalAbsD C Mr d lay0 ents0) (habs : WalAbsD C Mr d lay ents)
    (hR : RepOld lay) (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
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
    have hV := habs.repValsLo hg hR.1
    refine crashTo_tailR hC habs hnd hg hR hS d.m habs.lastSynced h' hfo (fun f hf1 => ?_) (hnmd g hgm) hw
    obtain ⟨h1, h2, h3⟩ := crashImg_tail (by rw [← hf1]; exact hf g hgm) hsz (habs.winLo_any g hg)
      hzf' (habs.hiX hg)
    have hmx : max lay.so lay.z0 = lay.wr := by have := hR.1; omega
    refine ⟨by omega, h2, fun b hb => ?_⟩
    rcases h3 b (by omega) with ⟨s, hs'⟩ | ⟨hb1, -⟩
    · exact hV b _ hb hs'
    · omega
  · right
    exact ⟨la, hla, crashTo_congr_fo (fun g' hg' => hfo _ (halt la hla g' hg')) h⟩

end crash

/-! ## The truncate's first step at `wr` from a tail whose frame there is the durable image's -/

section pure
variable [GooseExts]

/-- **The truncate's start at `wr` from a `RepOld` tail is a crash step** (`crashOkA_tailRep`; `RepOld`
of the announced tail by `repOld_rzCands` over `segBytesX_rzSeg`). -/
theorem tailCrashStep_rzStartR {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur}
    {lay : WalLay} {ents : Ents} {cl : List Claim} {k : Nat} {pre : List SegG} {g0 : SegG} {n : Nat}
    (habs : WalAbsD C Mr d lay ents)
    (habs' : WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr) ents)
    (hR : RepOld lay) (hS : (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hs : lay.segs = pre ++ [g0])
    (hlen : g0.bs.length = g0.om.size) (htcz : g0.om.TcZ) (hn : 0 < n) :
    TailCrashStep C Mr d lay pre g0 (rzSeg g0 true lay.wr n) lay.wr cl k := by
  intro alt halt hok
  have hnd' : ((tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr).segs.map (·.ino)).Nodup := by
    have e : (tailLay lay pre (rzSeg g0 true lay.wr n) lay.wr).segs.map (·.ino) = lay.segs.map (·.ino) := by
      rw [hs]; simp [tailLay, rzSeg]
    rw [e]; exact hnd
  obtain ⟨-, -, -, hhi, -⟩ := habs.metas g0 (by rw [hs]; simp)
  obtain ⟨-, -, -, hwb, -⟩ := habs.lastWin g0 (by rw [hs]; simp)
  obtain ⟨hXl, hXc⟩ := segBytesX_rzSeg (tg := lay.wr) hn (by omega) hlen (by omega) htcz.1
  have hR' := repOld_rzCands hs rfl hR hXl hXc
  exact crashOkA_tailRep hC habs habs' hR' hS hnd' hs rfl rfl rfl rfl rfl rfl rfl
    (fun z hz => by rw [hlen]; exact htcz.1 z hz) (rzSeg_zf hlen htcz) halt hok

/-- **The truncate's first step at the write position, F-Z or `RepOld`**: `rzStart_pure` with `TailZeros
lay ∨ (RepOld lay ∧ |S| = wr)` in place of F-Z (`rzStart_pureP`'s form; `Repair`'s truncate of the
torn frame at `wr`). -/
theorem rzStart_pureR {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (habs : ∃ ents, WalAbsD C Mr d lay ents)
    (hcut : g0.om.cut = none)
    (hZR : TailZeros lay ∨ (RepOld lay ∧ (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr))
    (hB : TailBound C Mr d lay) (hk : 0 < k)
    (htcz : g0.om.TcZ) (hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n K c) := by
  rcases hZR with hZ | ⟨hR, hS⟩
  · exact rzStart_pure hC hW hd hl hs habs hcut hZ hB hk htcz hlo
  obtain ⟨ents, habs⟩ := habs
  have hnd : (lay.segs.map (·.ino)).Nodup := ((segsAll_nodup_iff Ls).1 hW.2.2.1).1 dir lay hl
  obtain ⟨hsz, -, -, hhi, -⟩ := habs.metas g0 (by rw [hs]; simp)
  obtain ⟨-, -, -, hwb, -⟩ := habs.lastWin g0 (by rw [hs]; simp)
  have habs' : ∀ ents', WalAbsD C Mr d lay ents' →
      WalAbsD C Mr d (tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr) ents' := fun ents' h =>
    walAbsD_rzStart h hs (Nat.le_refl _) (Nat.min_le_right _ _) (by omega)
      (segBytesX_rzSeg hk (by omega) hsz.symm (by omega) htcz.1)
  have hstep := tailCrashStep_rzStartR (cl := cl) (k := n) hC habs (habs' ents habs) hR hS hnd hs
    hsz.symm htcz hk
  exact ⟨walsOk_tailA hW hd hl hs rfl (by simp [rzSeg, hcut]) habs' hstep,
    fun K c h => dirKeysOk_tailA hd hl hstep h⟩

/-- **The truncate's first step at the write position, by the tail's right** (`walTail_truncSup`'s start;
the W7-W12 log, thirteenth session): F-Z by the key; F-Z or `TailPend` lent (`rzStart_pureP`); F-Z or
`RepOld` registered, not yet zeroed (`rzStart_pureR`), the last kept for the announced tail
(`repOld_rzCands`); a lent tail's write position the stream's end (`hS`). -/
theorem rzStart_pureK {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} {pre : List SegG} {g0 : SegG} {k : Nat} {ok : Option (Nat × Bool)}
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hs : lay.segs = pre ++ [g0]) (habs : ∃ ents, WalAbsD C Mr d lay ents)
    (hcut : g0.om.cut = none) (hZ : TailZK ok lay)
    (hS : ok ≠ none → (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr)
    (hB : TailBound C Mr d lay) (hk : 0 < k)
    (htcz : g0.om.TcZ) (hlo : ¬ SegExact g0 → g0.om.lo ≤ lay.wr) :
    WalsOk C Mr R jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n ∧
      (∀ K c, DirKeysOk C Mr jr s Ls cl n K c →
        DirKeysOk C Mr jr s (<[dir := tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr]> Ls) cl n K c) ∧
      TailRK ok (tailLay lay pre (rzSeg g0 true lay.wr k) lay.wr) := by
  rcases ok with _ | ⟨kk, _ | _⟩
  · exact ⟨(rzStart_pure hC hW hd hl hs habs hcut hZ hB hk htcz hlo).1,
      (rzStart_pure hC hW hd hl hs habs hcut hZ hB hk htcz hlo).2, trivial⟩
  · have hZP : TailZeros lay ∨
        (TailPend lay ∧ (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr) :=
      (hZ : TailZeros lay ∨ TailPend lay).elim Or.inl (fun h => Or.inr ⟨h, hS (by simp)⟩)
    obtain ⟨h1, h2⟩ := rzStart_pureP hC hW hd hl hs habs hcut hZP hB hk htcz hlo
    exact ⟨h1, h2, trivial⟩
  · obtain ⟨-, hR⟩ := (hZ : TailZ0 lay ∧ (TailZeros lay ∨ RepOld lay))
    have hZR : TailZeros lay ∨
        (RepOld lay ∧ (segStream C Mr d lay.cuts lay.cuts.length).length = lay.wr) :=
      hR.elim Or.inl (fun h => Or.inr ⟨h, hS (by simp)⟩)
    obtain ⟨h1, h2⟩ := rzStart_pureR hC hW hd hl hs habs hcut hZR hB hk htcz hlo
    refine ⟨h1, h2, ?_⟩
    rcases hR with hR | hR
    · exact Or.inl hR
    · obtain ⟨ents, habs⟩ := habs
      obtain ⟨hsz, -, -, hhi, -⟩ := habs.metas g0 (by rw [hs]; simp)
      obtain ⟨-, -, -, hwb, -⟩ := habs.lastWin g0 (by rw [hs]; simp)
      obtain ⟨hXl, hXc⟩ := segBytesX_rzSeg (tg := lay.wr) hk (by omega) hsz.symm (by omega) htcz.1
      exact Or.inr (repOld_rzCands hs rfl hR hXl hXc)

/-- **`RepOld` across the truncate's landing at `wr`** (`segBytesX_rzLand`: the same candidates). -/
theorem repOld_rzLand {lay : WalLay} {pre : List SegG} {g0 : SegG} {n : Nat}
    (hs : lay.segs = pre ++ [rzSeg g0 true lay.wr n]) (hR : RepOld lay)
    (hlen : g0.bs.length = g0.om.size) (hwr : lay.wr ≤ g0.om.size) (hhi : g0.om.size ≤ g0.om.hi) :
    RepOld (tailLay lay pre (rzLand g0 lay.wr n) lay.wr) :=
  repOld_sameCands hs rfl hR (segBytesX_rzLand hwr hlen hhi)

end pure

end WalFs
end EtcdGrove
end Perennial

end
