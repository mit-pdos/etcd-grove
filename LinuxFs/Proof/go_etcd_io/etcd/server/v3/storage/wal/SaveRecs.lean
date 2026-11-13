/- Lean-first (no Rocq counterpart).

# An appended operation's records (W6 of `notes/wal-fsext-plan.md`; "W6 implementation log")

Pure. When `Save`/`SaveSnapshot`'s update appends an operation `o` to a history `H` whose cuts are
all at most `|H|`, the tail's records grow by `o`'s records, chained from the CRC after every
record of the WAL (`tailRecs_snoc`), and so do the WAL's records (`allRecs_snoc`): the tail's
stream only grows (`tailStream_snoc`), which is what lets the invariant's update commit before the
records are written.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open WalEnc

section recs
variable [GooseExts]

theorem segStart_le {cuts : List Nat} {N : Nat} (hc : ∀ b ∈ cuts, b ≤ N) (k : Nat) :
    segStart cuts k ≤ N := by
  unfold segStart
  rw [List.getD_eq_getElem?_getD]
  cases hk : (0 :: cuts)[k]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    rcases List.mem_cons.1 (List.mem_of_getElem? hk) with rfl | hx
    · exact Nat.zero_le _
    · exact hc x hx

/-- **The segments after an appended operation**: the last one gains it. -/
theorem segsOf_snoc_op (HM : WalHist) (x : WalOp) (cuts : List Nat)
    (hc : ∀ b ∈ cuts, b ≤ HM.length) :
    segsOf (HM ++ [x]) cuts = segsInit HM cuts ++ [HM.drop (segStart cuts cuts.length) ++ [x]] := by
  rw [segsOf_split, segsInit_congr (P := HM ++ [x]) (Q := HM) (c := HM.length) hc (by simp),
    List.drop_append_of_le_length (segStart_le hc _)]

theorem histMap_snoc (H : List (WalOpG WalEnt)) (o : WalOpG WalEnt) :
    (H ++ [o]).map WalOpG.toM = H.map WalOpG.toM ++ [o.toM] := by simp

/-- The CRC after every record of the WAL is the chain's over its records' (type, data). -/
theorem chainEnd_allRecs (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) :
    chainEnd walCodec 0#32 (allRecs Mr H md cuts) =
      crcAfter walCodec 0#32 (segsDs Mr md true [] (segsOf (H.map WalOpG.toM) cuts)).flatten := by
  unfold allRecs recsOfSegs; exact chainEnd_chainRecs _ _ _

/-- **The tail's records after an appended operation**: the old ones, then the operation's,
chained from the CRC after every record of the WAL. -/
theorem tailRecs_snoc (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o : WalOpG WalEnt) (hc : ∀ b ∈ cuts, b ≤ H.length) :
    tailRecs Mr (H ++ [o]) md cuts = tailRecs Mr H md cuts ++
      chainRecs walCodec (chainEnd walCodec 0#32 (allRecs Mr H md cuts)) (opDs Mr o.toM) := by
  have hc' : ∀ b ∈ cuts, b ≤ (H.map WalOpG.toM).length := by simpa using hc
  have hlen : (segsInit (H.map WalOpG.toM) cuts).length = cuts.length := length_segsInit _ _
  unfold tailRecs
  rw [chainEnd_allRecs, histMap_snoc, segsOf_snoc_op _ _ _ hc', segsOf_split, segsDs_snoc,
    segsDs_snoc, List.flatten_append, chainSegs_snoc, chainSegs_snoc]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ← List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_chainSegs, length_segsDs]; omega),
    List.getElem?_append_right (by rw [length_chainSegs, length_segsDs]; omega)]
  simp only [length_chainSegs, length_segsDs, hlen, Nat.sub_self, List.getElem?_cons_zero,
    Option.getD_some, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [chainRecs_append]
  simp only [crcAfter_append]

/-- **The WAL's records after an appended operation.** -/
theorem allRecs_snoc (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o : WalOpG WalEnt) (hc : ∀ b ∈ cuts, b ≤ H.length) :
    allRecs Mr (H ++ [o]) md cuts = allRecs Mr H md cuts ++
      chainRecs walCodec (chainEnd walCodec 0#32 (allRecs Mr H md cuts)) (opDs Mr o.toM) := by
  have hc' : ∀ b ∈ cuts, b ≤ (H.map WalOpG.toM).length := by simpa using hc
  rw [chainEnd_allRecs]
  unfold allRecs recsOfSegs
  rw [histMap_snoc, segsOf_snoc_op _ _ _ hc', segsOf_split, segsDs_snoc, segsDs_snoc,
    List.flatten_append, List.flatten_append]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.flatten_cons, List.flatten_nil, ← List.append_assoc]
  rw [chainRecs_append]

/-- **The tail's stream only grows** when an operation is appended. -/
theorem tailStream_snoc (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8)
    (cuts : List Nat) (o : WalOpG WalEnt) (hc : ∀ b ∈ cuts, b ≤ H.length) :
    tailStream Mr (H ++ [o]) md cuts = tailStream Mr H md cuts ++
      recFrames walCodec (chainRecs walCodec (chainEnd walCodec 0#32 (allRecs Mr H md cuts))
        (opDs Mr o.toM)) := by
  rw [tailStream_recs, tailStream_recs, tailRecs_snoc Mr H md cuts o hc]
  simp [recFrames, frames]

end recs

end WalFs
end EtcdGrove
end Perennial

end
