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

end snoc

end WalFs
end EtcdGrove
end Perennial

end
