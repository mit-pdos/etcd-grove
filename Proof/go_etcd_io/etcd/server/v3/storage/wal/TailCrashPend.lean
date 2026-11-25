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
(P6 item 2: `TailPend` is now `RepOld`, a pending run of entry records allowed at `wr`; the crash steps of
a pending tail are `TailCrashRep.lean`'s, `crashOkA_tailRep`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashW

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

/-- **A zero length word at `off` (or fewer than 8 bytes left) is a `PendStop`** (the empty run). -/
theorem pendStop_zeroWord {C : WalCodec} {Mr : WalMarshal} {img : List w8} {off : Nat} {c : w32}
    (hz : ∀ j, j < 8 → img.getD (off + j) 0 = 0) : PendStop C Mr img off c :=
  pendStop_nil (decStep_zeroWord C true hz)


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
  have hI0H : I0.length ≤ d.H.length := walImg_length_le (walImgS_walImg hI0)
  have hiI0 : initSegs { d with H := I0 } lay.cuts = initSegs d lay.cuts :=
    initSegs_of_take hsorted (walImgS_take hI0 hm0)
  have hpur' := Nat.le_min.1 hpur
  refine Or.inr ⟨q, d.H, hent, hq, hinos, walImgS_refl hmH,
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
    change segStream C Mr d lay.cuts lay.cuts.length <+: imgOf (fo g.ino) ∧ PendStop C Mr
      (imgOf (fo g.ino)) (segStream C Mr d lay.cuts lay.cuts.length).length _
    simp only [imgOf, hf, Option.map_some, Option.getD_some]
    generalize segStream C Mr d lay.cuts lay.cuts.length = S at hlen hval ⊢
    refine ⟨prefix_of_getD (by rw [contents_length]; exact hlen) (fun b hb => ?_),
      pendStop_nil fun r len c' => decStep_zeroWord C true (fun j hj => ?_) r len c'⟩
    · rw [contents_getD f b (by omega)]; exact hval b (by omega) (by omega)
    · by_cases hb : S.length + j < f.size
      · rw [contents_getD f _ hb, hval _ hb (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega)]; rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [contents_length]; omega)]; rfl

end crash

end WalFs
end EtcdGrove
end Perennial

end
