/- Lean-first (no Rocq counterpart).

# `Save`'s commit keeps the static relation and the crash condition (W6; plan §3, "W6 implementation log")

Pure. `Save`/`SaveSnapshot`'s update commits before any record is written: the invariant's history
gains the operation `o` while the layout (cuts, segments, bytes, `wr`, `so`) stays. Then:

* the crash condition holds of the new history (`crashOkA_snoc`): a crash image of the old
  history is one of the new (`walImg_snoc`), and nothing else in `CrashTo` reads the history;
* the static relation holds of it (`walAbsD_snoc`), given that the bytes under the tail's stream
  past the frames found at the generation's start are zeros once the operation adds a record (F-Z
  for a reopened tail, the preallocation for a cut's; the handle's knowledge) and that the new
  records fit a frame: the tail's intended stream only grows (`segRecs_snoc_op`), and the bytes
  already written are a prefix of it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveRecs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section snoc
variable [GooseExts]

/-! ## The crash condition -/

/-- **An image of a history is one of the history with an operation appended.** -/
theorem walImg_snoc {E : Type} {H : List (WalOpG E)} {m : Nat} {I : List (WalOpG E)}
    (o : WalOpG E) (h : walImg H m I) : walImg (H ++ [o]) m I := by
  obtain ⟨j, hmj, hjH, hI⟩ := h
  refine ⟨j, hmj, by simp; omega, ?_⟩
  rcases hI with hI | ⟨hh, es, k, hj, hk, hI⟩
  · left; rw [hI, List.take_append_of_le_length hjH]
  · right
    have hjl : j < H.length := by
      rcases Nat.lt_or_ge j H.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj; cases hj
    refine ⟨hh, es, k, by rw [List.getElem?_append_left hjl]; exact hj, hk, ?_⟩
    rw [hI, List.take_append_of_le_length hjH]

theorem crashTo_snoc {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (o : WalOpG WalEnt) (h : CrashTo C Mr d lay m' fo) :
    CrashTo C Mr { d with H := d.H ++ [o] } lay m' fo := by
  rcases h with h | ⟨q, I, h1, h2, h3, hI, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, I, h1, h2, h3, walImg_snoc o hI, h5⟩

/-- **`Save`'s commit keeps the crash condition** (with any alternative layout). -/
theorem crashOkA_snoc {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} (o : WalOpG WalEnt)
    (h : CrashOkA C Mr d lay alt cl n) : CrashOkA C Mr { d with H := d.H ++ [o] } lay alt cl n := by
  intro m' fo hr hf hn hw
  rcases h m' fo hr hf hn hw with h | ⟨lay0, ha, h⟩
  · exact Or.inl (crashTo_snoc o h)
  · exact Or.inr ⟨lay0, ha, crashTo_snoc o h⟩

theorem crashOk_snoc {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {cl : List Claim} {n : Nat} (o : WalOpG WalEnt)
    (h : CrashOk C Mr d lay cl n) : CrashOk C Mr { d with H := d.H ++ [o] } lay cl n := by
  rw [← crashOkA_none_iff] at h ⊢; exact crashOkA_snoc o h

/-! ## The segments' records -/

theorem histM_snoc (d : WalDur) (o : WalOpG WalEnt) :
    histM { d with H := d.H ++ [o] } = histM d ++ [o.toM] := by simp [histM]

/-- **The segments' records after an appended operation**: the same but the last, which gains the
operation's records `X` (as many as its (type, data) pairs), which the WAL's records gain too. -/
theorem segRecs_snoc_op (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat)
    (o : WalOpG WalEnt) (hc : ∀ b ∈ cuts, b ≤ d.H.length) :
    ∃ (A : List (List WalRec)) (L X : List WalRec), A.length = cuts.length ∧
      segRecs C Mr d cuts = A ++ [L] ∧ segRecs C Mr { d with H := d.H ++ [o] } cuts = A ++ [L ++ X] ∧
      recsOfSegs C Mr d.metadata (segsOf (histM { d with H := d.H ++ [o] }) cuts) =
        recsOfSegs C Mr d.metadata (segsOf (histM d) cuts) ++ X ∧
      X.length = (opDs Mr o.toM).length := by
  have hc' : ∀ b ∈ cuts, b ≤ (histM d).length := by simpa [histM] using hc
  let S0 := segsInit (histM d) cuts
  let Ds := segsDs Mr d.metadata true [] S0
  let hd := segHdrDs Mr d.metadata (if S0 = [] then true else false) S0.flatten
  let B := List.flatMap (opDs Mr) ((histM d).drop (segStart cuts cuts.length))
  let c0 := crcAfter C 0#32 Ds.flatten
  refine ⟨chainSegs C 0#32 Ds, chainRecs C c0 (hd ++ B),
    chainRecs C (crcAfter C c0 (hd ++ B)) (opDs Mr o.toM), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ds, length_chainSegs, length_segsDs, S0, length_segsInit]
  · unfold segRecs
    rw [segsOf_split, segsDs_snoc, chainSegs_snoc]
  · unfold segRecs
    rw [histM_snoc, segsOf_snoc_op _ _ _ hc', segsDs_snoc, chainSegs_snoc]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      ← List.append_assoc]
    rw [chainRecs_append]
  · unfold recsOfSegs
    rw [histM_snoc, segsOf_snoc_op _ _ _ hc', segsOf_split, segsDs_snoc, segsDs_snoc,
      List.flatten_append, List.flatten_append]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.flatten_cons, List.flatten_nil, ← List.append_assoc]
    rw [chainRecs_append]
    simp only [c0, hd, B, Ds, S0, crcAfter_append]
  · exact length_chainRecs _ _ _

/-! ## The static relation -/

theorem walCutPos_le {H : WalHist} {b : Nat} (h : walCutPos H b) : b ≤ H.length := by
  rcases h with rfl | ⟨hh, es, hb, -⟩
  · exact Nat.zero_le _
  · rcases Nat.lt_or_ge (b - 1) H.length with h | h
    · omega
    · rw [List.getElem?_eq_none h] at hb; cases hb

theorem walCutPos_snoc {H : WalHist} {b : Nat} (x : WalOp) (h : walCutPos H b) :
    walCutPos (H ++ [x]) b := by
  rcases h with rfl | ⟨hh, es, hb, hne⟩
  · exact Or.inl rfl
  · have hl : b - 1 < H.length := by
      rcases Nat.lt_or_ge (b - 1) H.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hb; cases hb
    exact Or.inr ⟨hh, es, by rw [List.getElem?_append_left hl]; exact hb, hne⟩

theorem recFrames_eq_nil {C : WalCodec} {X : List WalRec} (h : recFrames C X = []) : X = [] := by
  cases X with
  | nil => rfl
  | cons r X =>
    have := congrArg List.length h
    simp [recFrames, frames] at this

/-- **`Save`'s commit keeps the static relation**, the layout unchanged: given that, if the
operation adds a record, the bytes under the tail's stream from the start's frames on are zeros
(`hZ`), and that the new records fit a frame (`hfit`). -/
theorem walAbsD_snoc {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (o : WalOpG WalEnt) (h : WalAbsD C Mr d lay ents)
    (hZ : opDs Mr o.toM ≠ [] → ∀ b, lay.z0 ≤ b → b < lay.old.length → lay.old.getD b 0 = 0)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata
      (segsOf (histM { d with H := d.H ++ [o] }) lay.cuts))) :
    WalAbsD C Mr { d with H := d.H ++ [o] } lay ents := by
  have hc : ∀ b ∈ lay.cuts, b ≤ d.H.length := fun b hb => by
    have := walCutPos_le (h.cuts.1 b hb); simpa [histM] using this
  have hc' : ∀ b ∈ lay.cuts, b ≤ (histM d).length := by simpa [histM] using hc
  obtain ⟨A, L, X, hA, hd, hd', hall, hX⟩ := segRecs_snoc_op C Mr d lay.cuts o hc
  have hsegLt : ∀ k, k < lay.cuts.length →
      segStream C Mr { d with H := d.H ++ [o] } lay.cuts k = segStream C Mr d lay.cuts k := by
    intro k hk
    unfold segStream
    rw [hd, hd', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  have hS : segStream C Mr { d with H := d.H ++ [o] } lay.cuts lay.cuts.length =
      segStream C Mr d lay.cuts lay.cuts.length ++ recFrames C X := by
    unfold segStream
    rw [hd, hd', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp [hA, recFrames_append]
  have htake : ∀ c, c ≤ d.H.length → (histM { d with H := d.H ++ [o] }).take c = (histM d).take c := by
    intro c hcl
    rw [histM_snoc, List.take_append_of_le_length (by simpa [histM] using hcl)]
  obtain ⟨hn, hcs, hnb, hcut, hmeta, hint, hlast, hsyn, hls, -, hstop, hne⟩ := h
  refine ⟨hn, ⟨fun b hb => ?_, hcs.2⟩, ?_, hcut, hmeta, ?_, ?_, ?_, hls, hfit, ?_, hne⟩
  · rw [histM_snoc]; exact walCutPos_snoc _ (hcs.1 b hb)
  · intro k g hk
    obtain ⟨sq, ix, hnm, hb⟩ := hnb k g hk
    refine ⟨sq, ix, hnm, fun hpos => ?_⟩
    rw [htake _ (segStart_le hc _)]
    exact hb hpos
  · intro k g hk hg
    rw [hsegLt _ (by have := hcs.2.2; have := List.getElem?_eq_some_iff.1 hg; omega)]
    exact hint k g hk hg
  · intro g hg
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hlast g hg
    simp only at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    rw [hS]
    refine ⟨h1, by simp; omega, h3, h4, fun b x hb => ?_, h6, ?_, fun hz b hb1 hb2 => ?_⟩
    · exact (h5 b x hb).snoc (fun hw => by simp at hw; omega) (fun hs => by simp at hs; omega)
    · rw [List.take_append_of_le_length (by omega)]; exact h7
    · rcases Nat.lt_or_ge lay.z0 (segStream C Mr d lay.cuts lay.cuts.length).length with hlt | hge
      · exact h8 hlt b hb1 hb2
      · apply hZ _ b hb1 hb2
        intro hnil
        rw [hnil, List.length_nil, List.length_eq_zero_iff] at hX
        subst hX
        simp [recFrames, frames] at hz; omega
  · refine ⟨by simp; omega, ?_⟩
    have h2 := hsyn.2
    simp only [List.take_append_of_le_length hsyn.1]
    exact h2
  · intro hz r len c'
    have hz' : recFrames C X = [] := by
      have hwr := (hlast _ (List.getLast?_eq_some_getLast hne)).2.1
      have hz0 := (hlast _ (List.getLast?_eq_some_getLast hne)).2.2.2.2.2.1
      rw [hS, List.length_append] at hz
      apply List.eq_nil_of_length_eq_zero; omega
    have hX0 := recFrames_eq_nil hz'
    subst hX0
    have hz2 : lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length := by
      rw [hS] at hz; simpa [recFrames, frames] using hz
    simp only at hall ⊢
    rw [hall, List.append_nil]
    exact hstop hz2 r len c'

/-! ## The sync's commit -/

/-- A byte after a successful fdatasync of the tail, every written byte now synced: durable at its
value. -/
theorem byteOk_sync {x y : w8} {a w s : Bool} {g : ByteG} (h : ByteOk x y a w s g)
    (hsw : s = true → w = true) : ByteOk x y a w w (durB g.1) := by
  cases w with
  | true =>
    have hv := h.val_w
    simp only [ByteOk, ite_true]
    rw [hv]
  | false =>
    have hs : s = false := by cases s; rfl; exact absurd (hsw rfl) (by simp)
    subst hs
    rw [h.val_unw]
    exact byteOk_durB rfl rfl

/-- A segment after a successful fdatasync: every byte durable at its value. -/
def syncSeg (g : SegG) : SegG := { g with bs := g.bs.map (fun y => durB y.1) }

/-- The layout after `sync`'s fdatasync of the tail (every byte written, flushed): every byte
durable, the tail synced up to what is written. -/
def syncLay (lay : WalLay) : WalLay := { lay with segs := lay.segs.map syncSeg, so := lay.wr }

/-- **`sync`'s commit keeps the static relation**, the history synced (`d.m := |H|`): every record
flushed (`wr` the tail's stream's length), the fdatasync made every byte durable. -/
theorem walAbsD_sync {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents)
    (htail : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) :
    WalAbsD C Mr { d with m := d.H.length } (syncLay lay) ents := by
  have hc : ∀ b ∈ lay.cuts, b ≤ d.H.length := fun b hb => by
    have := walCutPos_le (h.cuts.1 b hb); simpa [histM] using this
  obtain ⟨hn, hcs, hnb, hcut, hmeta, hint, hlast, hsyn, hls, hfit, hstop, hne⟩ := h
  refine ⟨?_, ⟨fun b hb => hcs.1 b hb, hcs.2.1, by simpa [syncLay] using hcs.2.2⟩, ?_, hcut, ?_, ?_, ?_, ?_, ?_, hfit, hstop, ?_⟩
  · simp only [syncLay, List.map_map]
    exact ⟨hn.1, hn.2⟩
  · intro k g hk
    simp only [syncLay, List.getElem?_map] at hk
    cases hk0 : lay.segs[k]? with
    | none => rw [hk0] at hk; cases hk
    | some g0 =>
      rw [hk0] at hk; simp only [Option.map_some, Option.some.injEq] at hk; subst hk
      exact hnb k g0 hk0
  · intro g hg
    simp only [syncLay, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hmeta g0 hg0
    simpa [syncSeg] using this
  · intro k g hk hg
    simp only [syncLay, List.length_map, List.getElem?_map] at hk hg
    cases hk0 : lay.segs[k]? with
    | none => rw [hk0] at hg; cases hg
    | some g0 =>
      rw [hk0] at hg; simp only [Option.map_some, Option.some.injEq] at hg; subst hg
      simp only [syncSeg, hint k g0 hk hk0, List.map_map]
      rfl
  · intro g hg
    simp only [syncLay, List.getLast?_map] at hg
    cases hl0 : lay.segs.getLast? with
    | none => rw [hl0] at hg; cases hg
    | some g0 =>
      rw [hl0] at hg; simp only [Option.map_some, Option.some.injEq] at hg; subst hg
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hlast g0 hl0
      simp only [syncLay] at h1 h2 h3 h4 h5 h6 h7 h8 ⊢
      refine ⟨Nat.le_refl _, h2, by simp [syncSeg, h3], h4, fun b x hb => ?_, h6, h7, h8⟩
      simp only [syncSeg, List.getElem?_map] at hb
      cases hb0 : g0.bs[b]? with
      | none => rw [hb0] at hb; cases hb
      | some y =>
        rw [hb0] at hb; simp only [Option.map_some, Option.some.injEq] at hb; subst hb
        exact byteOk_sync (h5 b y hb0)
          (fun hs => decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hs) h1))
  · refine ⟨Nat.le_refl _, ?_⟩
    simp only [syncLay, List.take_length]
    rw [htail]; exact Nat.le_refl _
  · exact segStart_le hc _
  · simp [syncLay, hne]

end snoc

end WalFs
end EtcdGrove
end Perennial

end
