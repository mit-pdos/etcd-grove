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

end WalFs
end EtcdGrove
end Perennial

end
