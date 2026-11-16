/-
**The WAL's reader over several files** (pure; W1 of `notes/wal-fsext-plan.md`, §2.2). The Go
reference is the WAL at the pin (fork commit `0b50f04262d9`): `decodeRecord` (decoder.go:88-103)
reads `d.brs[0]`; at its end of file or a zero length word it drops that file and, if one is left,
goes on in the next from offset 0 (`d.lastValidOff = 0`) with the same CRC; `isTornEntry` is
`false` unless the reader is in its last file (:171-173).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecode

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace WalEnc

/-- **The reader over the files `fs`, in name order, from CRC `c`** (`NewDecoder(rs...)` then the
readers' loop; the CRC is `crc.New(0, …)` for a fresh decoder). No file: `io.EOF` at once
(decoder.go:89-91). -/
def walDecodeFiles (C : WalCodec) : List (List w8) → w32 → DecOut
  | [], c => ⟨[], .eof, 0, c⟩
  | [f], c => walDecodeFrom C true f 0 c
  | f :: g :: fs, c =>
    let o := walDecodeFrom C false f 0 c
    if o.stop = .eof then
      let o' := walDecodeFiles C (g :: fs) o.crc
      { o' with recs := o.recs ++ o'.recs }
    else o

/-- A file holding the frames of `rs` then `z` preallocated zeros. -/
def segFile (C : WalCodec) (rs : List WalRec) (z : Nat) : List w8 :=
  recFrames C rs ++ List.replicate z (0#8)

/-- The reader on one file the encoder wrote: its records, then the end, at the chain's CRC. -/
theorem walDecodeFrom_segFile {C : WalCodec} (hC : C.Ok) (last : Bool) {rs : List WalRec}
    {z : Nat} {c : w32} (hfit : RecsFit C rs) (hch : ChainOk C c rs) (hz : z = 0 ∨ 8 ≤ z) :
    walDecodeFrom C last (segFile C rs z) 0 c =
      ⟨rs, .eof, (recFrames C rs).length, chainEnd C c rs⟩ := by
  have h := walDecodeFrom_frames hC (last := last) (bs := segFile C rs z) rs (off := 0) (c := c)
    (rest := List.replicate z (0#8)) hfit hch (by rw [List.drop_zero]; rfl)
  have hz' := walDecodeFrom_zeros C (last := last) (bs := segFile C rs z)
    (off := (recFrames C rs).length) (c := chainEnd C c rs) hz
    (by unfold segFile; exact List.drop_left' rfl)
  rw [h, Nat.zero_add, hz']
  simp

/-- **(a) over files: what the encoder wrote, file by file, decodes to its records**, the CRC
chained across the files, then the end. Each segment is its records and its zeros. -/
theorem walDecodeFiles_segs {C : WalCodec} (hC : C.Ok) :
    ∀ (segs : List (List WalRec × Nat)) (c : w32),
    RecsFit C (segs.flatMap Prod.fst) → ChainOk C c (segs.flatMap Prod.fst) →
    (∀ s ∈ segs, s.2 = 0 ∨ 8 ≤ s.2) →
    (walDecodeFiles C (segs.map (fun s => segFile C s.1 s.2)) c).recs = segs.flatMap Prod.fst ∧
    (walDecodeFiles C (segs.map (fun s => segFile C s.1 s.2)) c).stop = .eof
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | [s], c, hfit, hch, hz => by
    have hfit' : RecsFit C s.1 := fun r hr => hfit r (by simpa using hr)
    have hch' : ChainOk C c s.1 := by simpa using hch
    simp only [List.map_cons, List.map_nil, walDecodeFiles,
      walDecodeFrom_segFile hC true hfit' hch' (hz s (by simp)), List.flatMap_cons,
      List.flatMap_nil, List.append_nil, and_self]
  | s :: t :: segs, c, hfit, hch, hz => by
    have hfs : (s :: t :: segs).flatMap Prod.fst = s.1 ++ (t :: segs).flatMap Prod.fst := by
      simp [List.flatMap_cons]
    rw [hfs] at hfit hch
    have hfit1 : RecsFit C s.1 := fun r hr => hfit r (List.mem_append_left _ hr)
    have hfit2 : RecsFit C ((t :: segs).flatMap Prod.fst) :=
      fun r hr => hfit r (List.mem_append_right _ hr)
    have hch' := (chainOk_append C c _ _).mp hch
    have ih := walDecodeFiles_segs hC (t :: segs) (chainEnd C c s.1) hfit2 hch'.2
      (fun s' hs' => hz s' (List.mem_cons_of_mem _ hs'))
    simp only [List.map_cons] at ih ⊢
    simp only [walDecodeFiles, walDecodeFrom_segFile hC false hfit1 hch'.1 (hz s (by simp)),
      ite_true] at ih ⊢
    exact ⟨by rw [ih.1, hfs], ih.2⟩

end WalEnc
end EtcdGrove
end Perennial
