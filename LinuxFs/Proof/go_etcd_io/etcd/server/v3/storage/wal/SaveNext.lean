/- Lean-first (no Rocq counterpart).

# The next record a handle encodes (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log")

`saveEntry` and `saveState` encode the next record of the tail not yet encoded (`rest > 0`): its type and
data are the history's (`saveEntry.spec`/`saveState.spec`'s premise), its CRC the chain's after the records
encoded so far, the handle's `h.crc`. Pure:

* `chainRecs_getElem?`: a chained record's CRC is the chain's after the records before it;
* `allRecs_tail`: every record of the WAL is the earlier segments' records, then the tail's;
* `WalHS.next_guard`: everything the encoder holds, then the next record's frame, is a prefix of the
  tail's intended stream past `o0` (`encode.specTail`'s premise);
* `WalHS.split_next`: the handle with that record encoded (`rest - 1`, its writer's and page writer's bytes
  any split of the frame appended): the stream split, and the CRC after it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SavePure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open WalEnc

section pure
variable [GooseExts]

/-- **A chained record's CRC is the chain's after the records before it.** -/
theorem chainRecs_getElem? (C : WalCodec) (c : w32) (F : List (w64 × List w8)) (j : Nat)
    (hj : j < F.length) :
    (chainRecs C c F)[j]? =
      some ⟨F[j].1, C.crc32c (chainEnd C c ((chainRecs C c F).take j)) F[j].2, F[j].2⟩ := by
  have e : F = F.take j ++ F.drop j := (List.take_append_drop j F).symm
  have hd : F.drop j = F[j] :: F.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj]
  rw [← chainRecs_take, chainEnd_chainRecs]
  conv => lhs; rw [e, chainRecs_append, hd]
  rw [List.getElem?_append_right (by rw [length_chainRecs, List.length_take]; omega)]
  rw [length_chainRecs, List.length_take, show j - min j F.length = 0 by omega]
  obtain ⟨t, d⟩ := F[j]
  rfl

/-- **Every record of the WAL: the earlier segments' records, then the tail's.** -/
theorem allRecs_tail (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) :
    ∃ X, allRecs Mr H md cuts = X ++ tailRecs Mr H md cuts := by
  let Ds := segsDs Mr md true [] (segsOf (H.map WalOpG.toM) cuts)
  have hl : (chainSegs walCodec 0#32 Ds).length = cuts.length + 1 := by
    rw [length_chainSegs, length_segsDs]; simp [segsOf]
  refine ⟨((chainSegs walCodec 0#32 Ds).take cuts.length).flatten, ?_⟩
  have e1 : allRecs Mr H md cuts = (chainSegs walCodec 0#32 Ds).flatten := by
    unfold allRecs recsOfSegs; rw [flatten_chainSegs]
  have e2 : tailRecs Mr H md cuts = (chainSegs walCodec 0#32 Ds).getD cuts.length [] := rfl
  rw [e1, e2]
  conv => lhs; rw [← List.take_append_drop cuts.length (chainSegs walCodec 0#32 Ds)]
  rw [List.flatten_append]
  congr 1
  have hn : (chainSegs walCodec 0#32 Ds).drop (cuts.length + 1) = [] :=
    List.drop_eq_nil_of_le (by omega)
  rw [List.drop_eq_getElem_cons (by omega), hn,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

/-- The next record (`rest > 0`) at the chain's position. -/
theorem WalHS.next_rec (Mr : WalMarshal) (h : WalHS) (hs : h.Split Mr) (hr : 0 < h.rest)
    (t : w64) (d : List w8)
    (hx : ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (t, d)) :
    (tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]? =
        some ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩ ∧
      (allRecs Mr h.H h.md h.cuts)[(allRecs Mr h.H h.md h.cuts).length - h.rest]? =
        some ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩ := by
  obtain ⟨-, -, hrl⟩ := hs
  obtain ⟨X, hX⟩ := allRecs_tail Mr h.H h.md h.cuts
  have hA : (allRecs Mr h.H h.md h.cuts)[(allRecs Mr h.H h.md h.cuts).length - h.rest]? =
      (tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]? := by
    rw [hX, List.length_append, List.getElem?_append_right (by omega)]
    congr 1; omega
  -- the WAL's records are a chain
  let F := (segsDs Mr h.md true [] (segsOf (h.H.map WalOpG.toM) h.cuts)).flatten
  have hAF : allRecs Mr h.H h.md h.cuts = chainRecs walCodec 0#32 F := rfl
  have hlen : (allRecs Mr h.H h.md h.cuts).length = F.length := by rw [hAF, length_chainRecs]
  have hjF : (allRecs Mr h.H h.md h.cuts).length - h.rest < F.length := by
    rw [← hlen, hX, List.length_append]; omega
  have hc := chainRecs_getElem? walCodec 0#32 F _ hjF
  rw [← hAF] at hc
  have hcrc : chainEnd walCodec 0#32 ((allRecs Mr h.H h.md h.cuts).take
      ((allRecs Mr h.H h.md h.cuts).length - h.rest)) = h.crc Mr := rfl
  rw [hcrc] at hc
  rw [hA] at hc
  rw [hc] at hx
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [h1, h2] at hc
  refine ⟨hc, ?_⟩
  rw [hA]; exact hc

/-- The records encoded after the next one. -/
theorem WalHS.encRecs_next (Mr : WalMarshal) (h h' : WalHS) (hs : h.Split Mr) (hr : 0 < h.rest)
    (x : WalRec) (hx : (tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]? = some x)
    (hH : h'.H = h.H) (hmd : h'.md = h.md) (hcuts : h'.cuts = h.cuts) (hrest : h'.rest = h.rest - 1) :
    h'.encRecs Mr = h.encRecs Mr ++ [x] := by
  obtain ⟨-, -, hrl⟩ := hs
  unfold WalHS.encRecs
  rw [hH, hmd, hcuts, hrest]
  rw [show (tailRecs Mr h.H h.md h.cuts).length - (h.rest - 1) =
      ((tailRecs Mr h.H h.md h.cuts).length - h.rest) + 1 by omega, List.take_succ, hx]
  rfl

/-- **The encode's guard** (`encode.specTail`'s premise): everything the encoder holds, then the next
record's frame, is a prefix of the tail's intended stream past `o0`. -/
theorem WalHS.next_guard (Mr : WalMarshal) (h : WalHS) (hs : h.Split Mr) (hr : 0 < h.rest)
    (t : w64) (d : List w8)
    (hx : ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (t, d)) :
    h.out ++ h.pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩) <+:
      (tailStream Mr h.H h.md h.cuts).drop h.o0 := by
  have hx' := (WalHS.next_rec Mr h hs hr t d hx).1
  have hs' := hs
  obtain ⟨h1, h2, hrl⟩ := hs'
  have hE : (tailRecs Mr h.H h.md h.cuts).take ((tailRecs Mr h.H h.md h.cuts).length - h.rest + 1) =
      h.encRecs Mr ++ [⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩] := by
    rw [List.take_succ, hx']; rfl
  have hpre : recFrames walCodec (h.encRecs Mr ++ [⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩]) <+:
      tailStream Mr h.H h.md h.cuts := by
    rw [← hE, tailStream_recs]
    exact ⟨recFrames walCodec ((tailRecs Mr h.H h.md h.cuts).drop
      ((tailRecs Mr h.H h.md h.cuts).length - h.rest + 1)), by
        rw [← recFrames_append, List.take_append_drop]⟩
  have hf : recFrames walCodec [⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩] =
      frame (walRecEnc ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩) := by
    simp [recFrames, frames]; rfl
  rw [recFrames_append, hf] at hpre
  have hl : ((recFrames walCodec (h.encRecs Mr)).take h.o0).length = h.o0 := by
    rw [List.length_take]; omega
  obtain ⟨u, hu⟩ := hpre
  refine ⟨u, ?_⟩
  rw [← hu]
  conv => rhs; rw [← h1]
  simp only [List.append_assoc]
  rw [List.drop_left' hl]

/-- **The handle with the next record encoded** (see the file header): the split, and the CRC. -/
theorem WalHS.split_next (Mr : WalMarshal) (h h' : WalHS) (hs : h.Split Mr) (hr : 0 < h.rest)
    (t : w64) (d : List w8)
    (hx : ((tailRecs Mr h.H h.md h.cuts)[(tailRecs Mr h.H h.md h.cuts).length - h.rest]?).map
      (fun x => (x.typ, x.data)) = some (t, d))
    (hH : h'.H = h.H) (hmd : h'.md = h.md) (hcuts : h'.cuts = h.cuts) (hrest : h'.rest = h.rest - 1)
    (ho0 : h'.o0 = h.o0)
    (he : h'.out ++ h'.pend = h.out ++ h.pend ++ frame (walRecEnc ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩)) :
    h'.Split Mr ∧ h'.crc Mr = hash.crc32.crc32c (h.crc Mr) d := by
  obtain ⟨hxT, hxA⟩ := WalHS.next_rec Mr h hs hr t d hx
  have hE := WalHS.encRecs_next Mr h h' hs hr _ hxT hH hmd hcuts hrest
  have hs' := hs
  obtain ⟨h1, h2, hrl⟩ := hs'
  have hf : recFrames walCodec [⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩] =
      frame (walRecEnc ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩) := by
    simp [recFrames, frames]; rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hE, recFrames_append, hf, ho0, List.take_append_of_le_length h2, List.append_assoc, he]
    conv => rhs; rw [← h1]
    simp only [List.append_assoc]
  · rw [hE, recFrames_append, List.length_append, ho0]; omega
  · rw [hrest, hH, hmd, hcuts]; omega
  · -- the CRC: the chain's after one more record
    obtain ⟨X, hX⟩ := allRecs_tail Mr h.H h.md h.cuts
    have hlA : h.rest ≤ (allRecs Mr h.H h.md h.cuts).length := by
      rw [hX, List.length_append]; omega
    unfold WalHS.crc
    rw [hH, hmd, hcuts, hrest]
    rw [show (allRecs Mr h.H h.md h.cuts).length - (h.rest - 1) =
      ((allRecs Mr h.H h.md h.cuts).length - h.rest) + 1 by omega, List.take_succ, hxA,
      Option.toList_some, chainEnd_append]
    show crcNext walCodec (h.crc Mr) ⟨t, hash.crc32.crc32c (h.crc Mr) d, d⟩ = _
    unfold crcNext
    split <;> rfl

end pure

end WalFs
end EtcdGrove
end Perennial

end
