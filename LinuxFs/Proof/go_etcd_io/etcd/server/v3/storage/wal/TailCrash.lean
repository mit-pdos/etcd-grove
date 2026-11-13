/- Lean-first (no Rocq counterpart).

# The tail's crash after appends, lifted to `CrashTo` (W6, pure; `notes/wal-fsext-plan.md`, "W6 implementation log")

`TailCrashPure.lean`'s `tail_decode` says what the reader of a crashed tail reads: the intended records of
the last segment up to some `j`, at least those below `max so z0`, then a frame it rejects. Here that is
lifted to the WAL's crash condition:

* **the last segment's records** (`lastRecs`): the chain from the CRC after every earlier segment
  (`lastC0`), the segment's headers (`lastHdr`) then its operations' records; every other segment's
  records depend only on the history before the last cut (`SegPre.lean`'s `segsInit`);
* **the image of the history** a record count `j` of the last segment gives (`tailImg`): the history
  before the last cut, then `histCut` of the last segment's operations; it is a `walImg` of the history
  when `j` covers the synced operations (`tailImg_walImg`), and its last segment's records are the
  first `j` (`lastRecs_tailImg`);
* **`crashTo_tail`**: a crash of a layout whose tail satisfies `ByteOk`, F-Z (`TailZeros`) and the record
  boundary (`TailBound`), under W1, gives `CrashTo`, the tree part (where the WAL directory is, which
  files are kept, the purge bound) taken from a `CrashTo` of the same layout over another image of the
  tail (any: `fo0`);
* **`crashOkA_tail`**: a step that changes only the tail's bytes (a `pwrite`'s announce or finish) keeps
  the crash condition: the old one, applied to the crash with the tail imaged as of the last sync
  (`syncImg`, which the old candidates allow and on which W1 holds by itself), gives the tree part.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section lastrecs
variable [GooseExts]

/-! ## The last segment's records -/

/-- The last segment's records. -/
def lastRecs (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) : List WalRec :=
  (segRecs C Mr d cuts).getD cuts.length []

/-- The segments before the last. -/
def initSegs (d : WalDur) (cuts : List Nat) : List WalHist := segsInit (histM d) cuts

/-- The chain's CRC at the start of the last segment. -/
def lastC0 (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) : w32 :=
  crcAfter C 0#32 (segsDs Mr d.metadata true [] (initSegs d cuts)).flatten

/-- The last segment's header records. -/
def lastHdr (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) : List (w64 × List w8) :=
  segHdrDs Mr d.metadata (if initSegs d cuts = [] then true else false) (initSegs d cuts).flatten

/-- The last segment's operations. -/
def lastOps (d : WalDur) (cuts : List Nat) : WalHist := (histM d).drop (segStart cuts cuts.length)

theorem lastRecs_eq (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    lastRecs C Mr d cuts = chainRecs C (lastC0 C Mr d cuts)
      (lastHdr Mr d cuts ++ (lastOps d cuts).flatMap (opDs Mr)) := by
  unfold lastRecs segRecs lastC0 lastHdr lastOps initSegs
  rw [segsOf_split, segsDs_snoc, chainSegs_snoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_chainSegs, length_segsDs, length_segsInit]; exact Nat.le_refl _)]
  rw [length_chainSegs, length_segsDs, length_segsInit, Nat.sub_self]
  rfl

/-- The WAL's records: the earlier segments', then the last's. -/
theorem allRecs_split (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    recsOfSegs C Mr d.metadata (segsOf (histM d) cuts) =
      chainRecs C 0#32 (segsDs Mr d.metadata true [] (initSegs d cuts)).flatten ++
        lastRecs C Mr d cuts := by
  rw [lastRecs_eq]
  unfold recsOfSegs lastC0 lastHdr lastOps initSegs
  rw [segsOf_split, segsDs_snoc, List.flatten_append, chainRecs_append]
  simp

/-- The chain's CRC after every record of the WAL: after the last segment's, from `lastC0`. -/
theorem chainEnd_allRecs_split (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    chainEnd C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) cuts)) =
      chainEnd C (lastC0 C Mr d cuts) (lastRecs C Mr d cuts) := by
  rw [allRecs_split, chainEnd_append, chainEnd_chainRecs]
  rfl

theorem chainOk_lastRecs {C : WalCodec} (hC : C.Ok) (Mr : WalMarshal) (d : WalDur)
    (cuts : List Nat) : ChainOk C (lastC0 C Mr d cuts) (lastRecs C Mr d cuts) := by
  have h : ChainOk C 0#32 (recsOfSegs C Mr d.metadata (segsOf (histM d) cuts)) :=
    chainOk_chainRecs hC _ _ (segsDs_crcOk Mr d.metadata true [] _)
  rw [allRecs_split, chainOk_append, chainEnd_chainRecs] at h
  exact h.2

/-- The segments but the last of two WALs with the same earlier segments and metadata. -/
theorem segRecs_init_congr (C : WalCodec) (Mr : WalMarshal) {d d' : WalDur} {cuts : List Nat}
    (hmd : d'.metadata = d.metadata) (hinit : initSegs d' cuts = initSegs d cuts) {k : Nat}
    (hk : k < cuts.length) : (segRecs C Mr d' cuts).getD k [] = (segRecs C Mr d cuts).getD k [] := by
  unfold initSegs at hinit
  unfold segRecs
  rw [segsOf_split, segsOf_split, hinit, hmd, segsDs_snoc, segsDs_snoc, chainSegs_snoc,
    chainSegs_snoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [length_chainSegs, length_segsDs, length_segsInit]; exact hk),
    List.getElem?_append_left (by rw [length_chainSegs, length_segsDs, length_segsInit]; exact hk)]

/-! ## The image of the history a record count gives -/

/-- **The image of the history at `n` operation records of the last segment**: the history before
the last cut, then `histCut` of the last segment's operations. -/
def tailImg (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (n : Nat) : List (WalOpG WalEnt) :=
  d.H.take (segStart cuts cuts.length) ++ (histCut Mr (lastOps d cuts) n).map WalOpG.toRaw

theorem map_toM_toRaw (X : WalHist) : (X.map WalOpG.toRaw).map WalOpG.toM = X := by
  rw [List.map_map]
  exact (List.map_congr_left (fun o _ => WalOpG.toM_toRaw o)).trans (List.map_id' X)

theorem map_toRaw_toM (X : List (WalOpG WalEnt)) : (X.map WalOpG.toM).map WalOpG.toRaw = X := by
  rw [List.map_map]
  exact (List.map_congr_left (fun o _ => WalOpG.toRaw_toM o)).trans (List.map_id' X)

theorem histM_tailImg (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (n : Nat) :
    histM { d with H := tailImg Mr d cuts n } =
      (histM d).take (segStart cuts cuts.length) ++ histCut Mr (lastOps d cuts) n := by
  simp only [histM, tailImg, List.map_append, List.map_take, map_toM_toRaw]

theorem initSegs_tailImg (Mr : WalMarshal) (d : WalDur) {cuts : List Nat} (n : Nat)
    (hc : cuts.Pairwise (· < ·)) (hL : segStart cuts cuts.length ≤ d.H.length) :
    initSegs { d with H := tailImg Mr d cuts n } cuts = initSegs d cuts := by
  unfold initSegs
  rw [histM_tailImg]
  apply segsInit_congr (le_segStart_length hc)
  rw [List.take_append_of_le_length (by simp [histM]; omega), List.take_take, Nat.min_self]

theorem lastOps_tailImg (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (n : Nat)
    (hL : segStart cuts cuts.length ≤ d.H.length) :
    lastOps { d with H := tailImg Mr d cuts n } cuts = histCut Mr (lastOps d cuts) n := by
  unfold lastOps
  rw [histM_tailImg]
  exact List.drop_left' (by simp [histM]; omega)

/-- **The last segment's records of the image: the first `|hdr| + n`.** -/
theorem lastRecs_tailImg (C : WalCodec) (Mr : WalMarshal) (d : WalDur) {cuts : List Nat} (n : Nat)
    (hc : cuts.Pairwise (· < ·)) (hL : segStart cuts cuts.length ≤ d.H.length) :
    lastRecs C Mr { d with H := tailImg Mr d cuts n } cuts =
      (lastRecs C Mr d cuts).take ((lastHdr Mr d cuts).length + n) := by
  have hi := initSegs_tailImg Mr d n hc hL
  have e0 : lastC0 C Mr { d with H := tailImg Mr d cuts n } cuts = lastC0 C Mr d cuts := by
    unfold lastC0; rw [hi]
  have eh : lastHdr Mr { d with H := tailImg Mr d cuts n } cuts = lastHdr Mr d cuts := by
    unfold lastHdr; rw [hi]
  rw [lastRecs_eq, lastRecs_eq, e0, eh, lastOps_tailImg Mr d cuts n hL, flatMap_histCut,
    ← chainRecs_take, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)]
  simp

/-- An image over the model's entries is one over raw entries. -/
theorem walImg_toRaw {H : List (WalOpG WalEnt)} {m : Nat} {J : WalHist}
    (h : walImg (H.map WalOpG.toM) m J) : walImg H m (J.map WalOpG.toRaw) := by
  obtain ⟨j, h1, h2, hI⟩ := h
  simp only [List.length_map] at h2
  refine ⟨j, h1, h2, ?_⟩
  rcases hI with rfl | ⟨hs, es, k, hj, hk, rfl⟩
  · left; rw [← List.map_take, map_toRaw_toM]
  · right
    have hjl : j < H.length := by
      rcases Nat.lt_or_ge j H.length with h | h
      · exact h
      · rw [List.getElem?_map, List.getElem?_eq_none h] at hj; cases hj
    rw [List.getElem?_map, List.getElem?_eq_getElem hjl] at hj
    simp only [Option.map_some, Option.some.injEq] at hj
    cases hH : H[j] with
    | snap m => rw [hH] at hj; cases hj
    | save hs' es' =>
      rw [hH] at hj
      simp only [WalOpG.toM, WalOpG.save.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      refine ⟨hs', es', k, by rw [List.getElem?_eq_getElem hjl, hH], by simpa using hk, ?_⟩
      rw [List.map_append, ← List.map_take, map_toRaw_toM]
      simp only [List.map_cons, List.map_nil, WalOpG.toRaw, List.map_take, List.map_map]
      have e : List.map (EntryM.toRaw ∘ WalEnt.toM) es' = es' :=
        (List.map_congr_left (fun e _ => EntryM.toRaw_toM e)).trans (List.map_id' _)
      rw [e]

/-- **The image is one of the history** when its records cover the synced operations'. -/
theorem tailImg_walImg (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) (n : Nat)
    (hL : segStart cuts cuts.length ≤ d.m) (hm : d.m ≤ d.H.length)
    (hn : (((lastOps d cuts).take (d.m - segStart cuts cuts.length)).flatMap (opDs Mr)).length ≤ n) :
    walImg d.H d.m (tailImg Mr d cuts n) := by
  have hS : (lastOps d cuts).length = d.H.length - segStart cuts cuts.length := by
    simp [lastOps, histM]
  have hJ := walImg_histCut Mr (lastOps d cuts) (d.m - segStart cuts cuts.length) n (by omega) hn
  have := walImg_lift (P := (histM d).take (segStart cuts cuts.length)) (R := []) (m := d.m) hJ
    (by simp [histM]; omega)
  have e : (histM d).take (segStart cuts cuts.length) ++ lastOps d cuts ++ [] = d.H.map WalOpG.toM := by
    simp [lastOps, histM]
  rw [e] at this
  have := walImg_toRaw this
  simp only [List.map_append, List.map_take, histM, map_toRaw_toM] at this
  exact this

end lastrecs

/-! ## Helpers -/

section helpers
variable [GooseExts]

/-- An image of a history keeps its operations up to the mark. -/
theorem walImg_take {E : Type} {H I : List (WalOpG E)} {m L : Nat} (h : walImg H m I) (hL : L ≤ m) :
    I.take L = H.take L := by
  obtain ⟨j, h1, h2, rfl | ⟨_, _, _, _, _, rfl⟩⟩ := h
  · rw [List.take_take, Nat.min_eq_left (by omega)]
  · rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left (by omega)]

theorem initSegs_of_take {d d' : WalDur} {cuts : List Nat} (hc : cuts.Pairwise (· < ·))
    (h : d'.H.take (segStart cuts cuts.length) = d.H.take (segStart cuts cuts.length)) :
    initSegs d' cuts = initSegs d cuts := by
  unfold initSegs histM
  apply segsInit_congr (le_segStart_length hc)
  rw [← List.map_take, ← List.map_take, h]

/-- **Frames grow strictly with the records**: a record count whose frames are no longer than
another's is no larger. -/
theorem take_le_of_frames_le (C : WalCodec) (R : List WalRec) {a b : Nat} (ha : a ≤ R.length)
    (h : (recFrames C (R.take a)).length ≤ (recFrames C (R.take b)).length) : a ≤ b := by
  apply Nat.le_of_not_lt; intro hlt
  have h1 := recFrames_take_mono C R (show b + 1 ≤ a by omega)
  have hbl : b < R.length := by omega
  rw [recFrames_take_succ C R hbl, List.length_append] at h1
  have := frame_length_ge (C.encRec R[b]); omega

theorem acceptsFrom_crc0 {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    {r : WalRec} {len : Nat} {c' : w32} (ht : r.typ = crcType)
    (h : decStep C last bs off c = .accept r len c') :
    acceptsFrom C last bs off 0#32 = acceptsFrom C last bs off c := by
  rw [acceptsFrom_accept h, acceptsFrom_accept (decStep_crc0 ht h)]

/-- The image of a crashed tail below `max so z0` is the intended stream. -/
theorem TailCands.img_lo {X Y : Nat → w8} {cs : Nat → Cands} {so z0 : Nat}
    (hT : TailCands X Y cs so z0) {img : List w8}
    (himg : ∀ b, b < img.length → ∃ s, (img.getD b 0, s) ∈ cs b) (hlen : max so z0 ≤ img.length) :
    ∀ b, b < max so z0 → img.getD b 0 = X b := by
  intro b hb
  rcases hT.mem_val (himg b (by omega)).choose_spec with h | ⟨h1, -⟩
  · exact h
  · omega

/-- Bytes equal up to a list's length: the list is a prefix. -/
theorem prefix_of_getD {xs img : List w8} (hl : xs.length ≤ img.length)
    (h : ∀ b, b < xs.length → img.getD b 0 = xs.getD b 0) : xs <+: img := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have := h i h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
  simp only [Option.getD_some] at this
  rw [List.getElem_take]; exact this.symm

/-- The last segment of a WAL with cuts begins with a CRC record. -/
theorem lastRecs_head_crc (C : WalCodec) (Mr : WalMarshal) (d : WalDur) {cuts : List Nat}
    (hc : cuts ≠ []) : ∃ r rs, lastRecs C Mr d cuts = r :: rs ∧ r.typ = crcType := by
  have hne : initSegs d cuts ≠ [] := by
    intro h; have := length_segsInit (histM d) cuts; unfold initSegs at h; rw [h] at this
    cases cuts with
    | nil => exact hc rfl
    | cons _ _ => simp at this
  rw [lastRecs_eq]
  unfold lastHdr segHdrDs cutHdrDs
  rw [if_neg hne]
  simp only [Bool.false_eq_true, ite_false, List.cons_append, chainRecs]
  exact ⟨_, _, rfl, rfl⟩

theorem lastC0_nil (C : WalCodec) (Mr : WalMarshal) (d : WalDur) : lastC0 C Mr d [] = 0#32 := by
  simp [lastC0, initSegs, segsInit, segsDs, crcAfter]

end helpers

/-! ## The crash of the tail -/

section crash
variable [GooseExts]

theorem drop_length_sub_one' {α : Type} : ∀ {l : List α} (h : l ≠ []),
    l.drop (l.length - 1) = [l.getLast h]
  | [a], _ => rfl
  | a :: b :: t, _ => by
    have := drop_length_sub_one' (l := b :: t) (by simp)
    simp only [List.length_cons, Nat.add_sub_cancel, List.drop_succ_cons] at this ⊢
    rw [this, List.getLast_cons_cons]

/-- A segment of distinct inodes is the one `segBytesOf` finds. -/
theorem segBytesOf_mem {lay : WalLay} {g : SegG} (hnd : (lay.segs.map (·.ino)).Nodup)
    (hg : g ∈ lay.segs) : segBytesOf lay g.ino = some g.bs := by
  unfold segBytesOf
  cases hf : lay.segs.find? (fun g' => decide (g'.ino = g.ino)) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hf g hg
    simp at this
  | some g' =>
    have hg' := List.mem_of_find?_eq_some hf
    have hi : g'.ino = g.ino := by simpa using List.find?_some hf
    have : g' = g := Fs.eq_of_nodup_map hnd hg' hg hi
    subst this; rfl

/-- **The tail's candidates** (`TailCands`) from the static relation and F-Z. -/
theorem tailCands_of_abs {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    {g : SegG} (habs : WalAbsD C Mr d lay ents) (hZ : TailZeros lay)
    (hg : lay.segs.getLast? = some g) :
    TailCands (fun b => (segStream C Mr d lay.cuts lay.cuts.length).getD b 0)
      (fun b => lay.old.getD b 0)
      (fun b => if b < g.bs.length then (g.bs.getD b (0, [])).2 else [(0, 0)]) lay.so lay.z0 := by
  obtain ⟨hso, hwr, hlen, hwro, hbytes, hz0, htake, -⟩ := habs.last g hg
  generalize segStream C Mr d lay.cuts lay.cuts.length = S at hwr hbytes htake ⊢
  have hb : ∀ b, b < g.bs.length → ByteOk (S.getD b 0) (lay.old.getD b 0) (decide (b < S.length))
      (decide (b < lay.wr)) (decide (b < lay.so)) (g.bs.getD b (0, [])) := by
    intro b hbl
    have := hbytes b (g.bs[b]) (List.getElem?_eq_getElem hbl)
    have e : g.bs.getD b (0, []) = g.bs[b] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl, Option.getD_some]
    rw [e]; exact this
  refine ⟨fun b hbs => ?_, fun b hbs => ?_, fun b hbz => ?_, fun b hbz => ?_⟩
  · have hbl : b < g.bs.length := by omega
    have h := hb b hbl
    rw [show decide (b < lay.so) = true by simp; omega] at h
    simp only [ByteOk, ite_true] at h
    simp only [if_pos hbl, h]
  · by_cases hbl : b < g.bs.length
    · have h := hb b hbl
      rw [show decide (b < lay.so) = false by simp; omega] at h
      simp only [ByteOk, Bool.false_eq_true, ite_false] at h
      obtain ⟨ex, h1, h2, -, -⟩ := h
      exact ⟨ex, by simp only [if_pos hbl, h1], h2⟩
    · refine ⟨[], ?_, by simp⟩
      simp only [if_neg hbl]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · by_cases hbo : b < lay.old.length
    · have h1 := congrArg (fun l => l.getD b 0) htake
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hbz] at h1
      exact h1.symm
    · rw [List.getD_eq_getElem?_getD (l := lay.old), List.getElem?_eq_none (by omega)]
      have h1 := congrArg List.length htake
      simp only [List.length_take] at h1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  · by_cases hbo : b < lay.old.length
    · exact hZ b hbz hbo
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- The synced operations' records are the first `a` of the last segment's, `a` covering its
headers and the synced operations. -/
theorem lastRecs_synced (C : WalCodec) (Mr : WalMarshal) (d : WalDur) {cuts : List Nat}
    (hc : cuts.Pairwise (· < ·)) (hL : segStart cuts cuts.length ≤ d.m) :
    lastRecs C Mr { d with H := d.H.take d.m } cuts = (lastRecs C Mr d cuts).take
      ((lastHdr Mr d cuts).length +
        (((lastOps d cuts).take (d.m - segStart cuts cuts.length)).flatMap (opDs Mr)).length) := by
  have hi : initSegs { d with H := d.H.take d.m } cuts = initSegs d cuts :=
    initSegs_of_take hc (by simp only; rw [List.take_take, Nat.min_eq_left hL])
  have e0 : lastC0 C Mr { d with H := d.H.take d.m } cuts = lastC0 C Mr d cuts := by
    unfold lastC0; rw [hi]
  have eh : lastHdr Mr { d with H := d.H.take d.m } cuts = lastHdr Mr d cuts := by
    unfold lastHdr; rw [hi]
  have eo : lastOps { d with H := d.H.take d.m } cuts =
      (lastOps d cuts).take (d.m - segStart cuts cuts.length) := by
    unfold lastOps histM; simp only; rw [List.map_take, List.drop_take]
  rw [lastRecs_eq, lastRecs_eq, e0, eh, eo, ← chainRecs_take]
  congr 1
  obtain ⟨t, ht⟩ := flatMap_take_prefix (opDs Mr) (lastOps d cuts) (d.m - segStart cuts cuts.length)
  rw [← ht, ← List.append_assoc, List.take_left' (by simp)]

theorem lastHdr_pos (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    1 ≤ (lastHdr Mr d cuts).length := by
  unfold lastHdr segHdrDs hdrDs cutHdrDs
  split <;> split <;> simp

theorem lastRecs_length (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) :
    (lastRecs C Mr d cuts).length =
      (lastHdr Mr d cuts).length + ((lastOps d cuts).flatMap (opDs Mr)).length := by
  rw [lastRecs_eq, length_chainRecs, List.length_append]

/-- **The crash of a tail written this generation** (see the file header): the tree part from a
`CrashTo` of the layout over another image `fo0` of the tail. -/
theorem crashTo_tail {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} {m' : Tree} {fo fo0 : Ino → Option Fs.OsFile} {g : SegG}
    (habs : WalAbsD C Mr d lay ents) (hZ : TailZeros lay) (hB : TailBound C Mr d lay)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hg : lay.segs.getLast? = some g)
    (h0 : CrashTo C Mr d lay m' fo0) (hfo : ∀ i, i ≠ g.ino → fo0 i = fo i)
    (hfc : FileCrashedR g.om [(0, DFrac.own (1 : Qp).half, g.bs)] (fo g.ino))
    (hn : Named m' g.ino → (fo g.ino).isSome)
    (hw : W1G C (walInos (entsOf m' lay.j)) (fun i => imgOf (fo i)) (segBytesOf lay)) :
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
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (hn (named_of_mem_walInos hgin))
  obtain ⟨-, hlo, hhi, hrun, -⟩ := hfc f hf
  obtain ⟨-, -, hmlo, hmhi⟩ := habs.metas g hgm
  have hsz : f.size = g.bs.length := by omega
  obtain ⟨hso, hwr, hlen, hwro, -, hz0, -, -⟩ := habs.last g hg
  -- the decoding core
  generalize hR : lastRecs C Mr d lay.cuts = R
  have hRS : segStream C Mr d lay.cuts lay.cuts.length = recFrames C R := by rw [← hR]; rfl
  have hT := tailCands_of_abs habs hZ hg
  rw [hRS] at hT
  generalize hcs : (fun b => if b < g.bs.length then (g.bs.getD b (0, [])).2 else [(0, 0)]) = cs
    at hT
  have himgl : f.contents.length = g.bs.length := by rw [contents_length, hsz]
  have himg : ∀ b, b < f.contents.length → ∃ s, (f.contents.getD b 0, s) ∈ cs b := by
    intro b hb
    rw [himgl] at hb
    have := hrun (0, DFrac.own (1 : Qp).half, g.bs) (List.mem_singleton_self _) b hb
      (by simp only [Nat.zero_add]; omega)
    simp only [Nat.zero_add] at this
    rw [contents_getD f b (by omega), ← hcs]
    simp only [if_pos hb]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
    exact this
  have hlenI : max lay.so lay.z0 ≤ f.contents.length := by rw [himgl, hlen]; omega
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
  have hlo' := hT.img_lo himg hlenI
  -- W1 along the reader's path, from the fresh reader's
  have hW : ∀ p ∈ acceptsFrom C true f.contents 0 (lastC0 C Mr d lay.cuts),
      AsOf cs f.contents p (frameCore f.contents p) := by
    have hW0 : ∀ p ∈ acceptsFrom C true f.contents 0 0#32,
        AsOf cs f.contents p (frameCore f.contents p) := by
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
      have h1 := hw _ (0, p) hp' g.ino g.bs (by rw [hjs]; rfl) (segBytesOf_mem hnd hgm)
      obtain ⟨x, hx, hxb⟩ := acceptsFiles_bound C _ _ _ hp'
      rw [hjs] at hx
      simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, imgOf, hf, Option.map_some,
        Option.getD_some, Option.some.injEq] at hx
      rw [← hx] at hxb; simp only at hxb
      simp only [imgOf, hf, Option.map_some, Option.getD_some] at h1
      have hcsb : ∀ b, b < p + frameCore f.contents p → cs b = (g.bs.getD b (0, [])).2 := by
        intro b hb; rw [← hcs]; simp only; rw [if_pos (by rw [← himgl]; omega)]
      rcases h1 with h1 | ⟨n, hn0, h1⟩
      · left; intro b hb1 hb2; rw [hcsb b hb2]; exact h1 b hb1 hb2
      · right; refine ⟨n, hn0, fun b hb1 hb2 => ?_⟩
        rw [hcsb b hb2]; exact h1 b hb1 hb2
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
  obtain ⟨j, hjj, hjR, hpre, hrej⟩ := tail_decode hC hfit hch hT hjE hEb himg hlenI hW
  have hLH : segStart lay.cuts lay.cuts.length ≤ d.H.length := by omega
  have hhdr : (lastHdr Mr d lay.cuts).length ≤ j := by omega
  obtain ⟨nI, hnI⟩ : ∃ nI, nI = j - (lastHdr Mr d lay.cuts).length := ⟨_, rfl⟩
  have hIimg := tailImg_walImg Mr d lay.cuts nI hLm hmH (by omega)
  have hIL := walImg_length_ge hIimg
  have hiI := initSegs_tailImg Mr d nI hsorted hLH
  have hiI0 : initSegs { d with H := I0 } lay.cuts = initSegs d lay.cuts :=
    initSegs_of_take hsorted (walImg_take hI0 hLm)
  have hlastI : lastRecs C Mr { d with H := tailImg Mr d lay.cuts nI } lay.cuts = R.take j := by
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
    unfold segStream
    rw [segRecs_init_congr C Mr (d := { d with H := I0 })
      (d' := { d with H := tailImg Mr d lay.cuts nI }) rfl
      (hiI.trans hiI0.symm) hkc]
  · intro g'' hg''
    rw [hg] at hg''
    cases hg''
    have e1 : segStream C Mr { d with H := tailImg Mr d lay.cuts nI } lay.cuts lay.cuts.length = recFrames C (R.take j) := by
      show recFrames C (lastRecs C Mr _ lay.cuts) = _
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

/-- **The synced offset is past the start of the tail**: the headers are synced (a tail write lands
after them: `SegFl.Ok`'s `0 < fl.off`). -/
theorem walAbsD_so_pos {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (habs : WalAbsD C Mr d lay ents) : 0 < lay.so := by
  have hs := habs.synced.2
  have e : (segRecs C Mr { d with H := d.H.take d.m } lay.cuts).getD lay.cuts.length [] =
      (lastRecs C Mr d lay.cuts).take ((lastHdr Mr d lay.cuts).length +
        (((lastOps d lay.cuts).take (d.m - segStart lay.cuts lay.cuts.length)).flatMap
          (opDs Mr)).length) :=
    lastRecs_synced C Mr d habs.cuts.2.1 habs.lastSynced
  rw [e] at hs
  have h1 := lastHdr_pos Mr d lay.cuts
  have hR := lastRecs_length C Mr d lay.cuts
  generalize lastRecs C Mr d lay.cuts = R at hs hR
  obtain ⟨k, hk⟩ : ∃ k, (lastHdr Mr d lay.cuts).length + (((lastOps d lay.cuts).take
      (d.m - segStart lay.cuts lay.cuts.length)).flatMap (opDs Mr)).length = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hk] at hs
  cases R with
  | nil => simp at hR; omega
  | cons r rs =>
    rw [List.take_succ_cons, recFrames_cons, List.length_append] at hs
    have := frame_length_ge (C.encRec r); omega

end crash

end WalFs
end EtcdGrove
end Perennial

end
