/- Lean-first (no Rocq counterpart).

# The append's commit on the handle (W6; `Append.lean`'s `walTail_append` through the sealed handle)

`walHandleIn_append`: a quiescent handle (`rest = 0`) commits the client's update appending `o`, at an
update of mask `⊤` (`wp_notCrashed_acc` before any step of the call): the handle's history is
`H ++ [o]` with `o`'s records not yet encoded (`rest := |opDs o|`); nothing else of it moves (the
encoder's CRC and the stream split are the same: the records encoded so far are the same, `o`'s come
after them). The index facts of the new history follow from the old ones (`hidx`; for a `Save`,
`saveOp_idx`); `o`'s records must fit a frame whatever the CRC (`hfit`; the WAL's do, the static
relation's `fit`). Also out: the client's `Q d` (`d.H` the
handle's history), `walLenLb` at the new length, the cuts' facts (`cut.spec`'s premises).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Append
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutHdrStream
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The handle after an append, `rest` raised by the operation's records**: the records encoded so
far are the same. -/
theorem WalHS.encRecs_snoc (Mr : WalMarshal) (h : WalHS) (o : WalOpG WalEnt)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) :
    WalHS.encRecs Mr { h with H := h.H ++ [o], rest := h.rest + (opDs Mr o.toM).length } =
      WalHS.encRecs Mr h := by
  unfold WalHS.encRecs
  simp only
  rw [tailRecs_snoc Mr h.H h.md h.cuts o hc, List.length_append, length_chainRecs]
  rw [show (tailRecs Mr h.H h.md h.cuts).length + (opDs Mr o.toM).length -
      (h.rest + (opDs Mr o.toM).length) = (tailRecs Mr h.H h.md h.cuts).length - h.rest by omega]
  exact List.take_append_of_le_length (by omega)

theorem WalHS.crc_snoc (Mr : WalMarshal) (h : WalHS) (o : WalOpG WalEnt)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) :
    WalHS.crc Mr { h with H := h.H ++ [o], rest := h.rest + (opDs Mr o.toM).length } =
      WalHS.crc Mr h := by
  unfold WalHS.crc
  simp only
  rw [allRecs_snoc Mr h.H h.md h.cuts o hc, List.length_append, length_chainRecs]
  rw [show (allRecs Mr h.H h.md h.cuts).length + (opDs Mr o.toM).length -
      (h.rest + (opDs Mr o.toM).length) = (allRecs Mr h.H h.md h.cuts).length - h.rest by omega]
  rw [List.take_append_of_le_length (by omega)]

theorem WalHS.split_snoc (Mr : WalMarshal) (h : WalHS) (o : WalOpG WalEnt)
    (hc : ∀ b ∈ h.cuts, b ≤ h.H.length) (hs : WalHS.Split Mr h) :
    WalHS.Split Mr { h with H := h.H ++ [o], rest := h.rest + (opDs Mr o.toM).length } := by
  unfold WalHS.Split
  rw [WalHS.encRecs_snoc Mr h o hc]
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨h1, h2, ?_⟩
  simp only
  rw [tailRecs_snoc Mr h.H h.md h.cuts o hc, List.length_append, length_chainRecs]
  omega

/-- **A `Save`'s index facts**: an empty one (no record) leaves the last index; none moves the
snapshot records' maximum. -/
theorem saveOp_idx (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (hs : HardStateM) (es : List EntryM)
    (x y : Nat) (hH : walLastIdx (H.map WalOpG.toM) ≤ x) (hS : walMaxSnapIdx (H.map WalOpG.toM) ≤ y) :
    ((opDs Mr (WalOpG.save hs es).toRaw.toM).length = 0 →
      walLastIdx ((H ++ [(WalOpG.save hs es).toRaw]).map WalOpG.toM) ≤ x) ∧
    walMaxSnapIdx ((H ++ [(WalOpG.save hs es).toRaw]).map WalOpG.toM) ≤ y := by
  rw [WalOpG.toM_toRaw, List.map_append, List.map_singleton, WalOpG.toM_toRaw]
  refine ⟨fun h0 => ?_, ?_⟩
  · have hes : es = [] := by
      simp only [opDs, List.length_append, List.length_map] at h0; exact List.eq_nil_of_length_eq_zero (by omega)
    subst hes
    simpa [walLastIdx, List.foldl_append] using hH
  · simpa [walMaxSnapIdx, List.foldl_append] using hS

/-- **A `Save`'s operation has no maximal index** (`Save.spec`'s index premise; `WalsBounded`). -/
theorem saveOp_noMax (hs : HardStateM) (es : List EntryM)
    (h : ∀ e ∈ es, uint.nat e.Index' < 2 ^ 64 - 1) :
    ¬ walHasMaxIdx [(WalOpG.save hs es).toRaw.toM] := by
  rw [WalOpG.toM_toRaw]
  rintro ⟨o, ho, hm⟩
  simp only [List.mem_singleton] at ho
  subst ho
  obtain ⟨e, he, he'⟩ := hm
  have := h e he
  omega

/-- **A `SaveSnapshot`'s operation has no maximal index** (its index premise; `WalsBounded`). -/
theorem snapOp_noMax (m : SnapshotMetadataM) (h : uint.nat m.Index' < 2 ^ 64 - 1) :
    ¬ walHasMaxIdx [(WalOpG.snap m : WalOpG WalEnt).toM] := by
  rintro ⟨o, ho, hm⟩
  simp only [List.mem_singleton] at ho
  subst ho
  have hm' : uint.nat m.Index' = 2 ^ 64 - 1 := hm
  omega

/-- **Records of small types and data below `2^40` bytes fit a frame**, whatever the CRC. -/
theorem recsFit_chainRecs_small (c : w32) (ds : List (w64 × List w8))
    (h : ∀ p ∈ ds, uint.nat p.1 < 2 ^ 8 ∧ p.2.length < 2 ^ 40) :
    RecsFit walCodec (chainRecs walCodec c ds) := by
  induction ds generalizing c with
  | nil => intro r hr; simp [chainRecs] at hr
  | cons p ds ih =>
    obtain ⟨t, d⟩ := p
    intro r hr
    simp only [chainRecs, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨ht, hd⟩ := h (t, d) List.mem_cons_self
      simp only at ht hd
      have := recSize_le t (walCodec.crc32c c d) d ht
      show (walRecEnc _).length < 2 ^ 56
      rw [walRecEnc, recEnc_length]; omega
    · exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)) r hr

/-- **A `Save`'s records fit a frame** (the entries' encodings below `2^40` bytes, `Save`'s premise; the
hard state's below `2^32`, `walAreaOk`'s law). -/
theorem saveOp_fit (Mr : WalMarshal) (hs : HardStateM) (es : List EntryM)
    (hS : (Mr.encState hs).length < 2 ^ 32) (hE : ∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40) (c : w32) :
    RecsFit walCodec (chainRecs walCodec c (opDs Mr (WalOpG.save hs es).toRaw.toM)) := by
  rw [WalOpG.toM_toRaw]
  apply recsFit_chainRecs_small
  intro p hp
  simp only [opDs, List.mem_append, List.mem_map] at hp
  rcases hp with ⟨e, he, rfl⟩ | hp
  · exact ⟨by show uint.nat entryType < 2 ^ 8; decide, hE e he⟩
  · split at hp
    · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨by show uint.nat stateType < 2 ^ 8; decide,
        by show (Mr.encState hs).length < 2 ^ 40; omega⟩

end pure

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The append's commit on a quiescent handle** (see the file header). -/
theorem walHandleIn_append (P : WalPbIn GF) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (h : WalHS) (o : WalOpG WalEnt) (sized : Bool) (Q : WalDur → IProp GF)
    (hr : h.rest = 0)
    (hfit : ∀ c, RecsFit walCodec (chainRecs walCodec c (opDs Mr o.toM)))
    (hidx : walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi) →
      walMaxSnapIdx (h.H.map WalOpG.toM) ≤ uint.nat h.snapi →
      ((opDs Mr o.toM).length = 0 → walLastIdx ((h.H ++ [o]).map WalOpG.toM) ≤
        max (uint.nat h.enti) (uint.nat h.snapi)) ∧
      walMaxSnapIdx ((h.H ++ [o]).map WalOpG.toM) ≤ uint.nat h.snapi)
    (hox : ¬ walHasMaxIdx [o.toM])
    (tm : Fs.OsMeta → List Fs.ByteG → Prop := TailMeta) :
    ⊢ walAreaOk walCodec Mr R jr r -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗
      walHandleIn (W := W) P Mr w dir h tm -∗
      (AU <{ ∃∃ d : WalDur, walDiskAt (W := W) dir d ∗ ⌜d.sized = sized⌝ }> @ walAuMask, ∅
        <{ walDiskAt (W := W) dir { d with H := d.H ++ [o] }, COMM Q d }>) -∗
      |={⊤}=> notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
        walHandleIn (W := W) P Mr w dir { h with H := h.H ++ [o], rest := (opDs Mr o.toM).length } tm ∗
        walLenLb (W := W) w dir (h.H.length + 1) ∗ (∃ d : WalDur, Q d ∗ ⌜d.H = h.H⌝) ∗
        ⌜(∀ b ∈ h.cuts, walCutPos (h.H.map WalOpG.toM) b) ∧ h.cuts.Pairwise (· < ·)⌝ := by
  letI := walAllG (W := W)
  iintro #Harea Hnc Hh Hau
  unfold walAreaOk
  icases Harea with ⟨#Hinv, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, Ht, Hrest⟩
  icases Hrest with ⟨R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, Hw, %hp⟩
  unfold walTailW
  icases Ht with ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hb, %hm, Hv⟩
  have hfit' : (∀ b ∈ ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1,
        b ≤ ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1.length) →
      RecsFit walCodec (recsOfSegs walCodec Mr
        ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.1
        (segsOf (((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1.map WalOpG.toM)
          ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1)) →
      RecsFit walCodec (recsOfSegs walCodec Mr
        ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.1
        (segsOf ((((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).1 ++ [o]).map
          WalOpG.toM) ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG).2.2.1)) := by
    intro hc hold
    show RecsFit walCodec (allRecs Mr (h.H ++ [o]) h.md h.cuts)
    rw [allRecs_snoc Mr h.H h.md h.cuts o hc]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hold x hx
    · exact hfit _ x hx
  imod walTail_append walCodec Mr R jr r w dir h.γ
    ((h.H, h.md, h.cuts, h.o0 + h.out.length, h.ino, none) : TailG) o sized Q hfit' hox
    $$ Hinv Hnc Hk [Hv] Hw Hau with ⟨Hnc, Hk, Hv, Hw, Hlb, HQ, %hcp⟩
  · unfold tailVar; iexact Hv
  have hc : ∀ b ∈ h.cuts, b ≤ h.H.length := fun b hb => by
    simpa using walCutPos_le (hcp.1 b hb)
  have eh : ({ h with H := h.H ++ [o], rest := (opDs Mr o.toM).length } : WalHS) =
      { h with H := h.H ++ [o], rest := h.rest + (opDs Mr o.toM).length } := by
    rw [hr, Nat.zero_add]
  rw [eh]
  have ecrc := WalHS.crc_snoc Mr h o hc
  unfold tailVar
  imodintro
  iframe Hnc
  isplitl [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 Hf Hfd Hoff Hk Hm Hb Hv
    R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 Hw]
  · iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    rw [ecrc]
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18
    iframe R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 Hw
    isplitl [Hf Hfd Hoff Hk Hm Hb Hv]
    · iframe Hf Hfd Hoff Hk
      iexists m, bs
      iframe Hm Hb Hv
      ipureintro; exact hm
    ipureintro
    obtain ⟨p1, p2, p3, p4, ⟨p6a, p6⟩, p7⟩ := hp
    have hidx' := hidx (p6a hr) p6
    refine ⟨WalHS.split_snoc Mr h o hc p1, p2, p3, p4, ⟨fun h0 => ?_, hidx'.2⟩, p7⟩
    exact hidx'.1 (by simpa [hr] using h0)
  isplitl [Hlb]
  · iexact Hlb
  isplitl [HQ]
  · iexact HQ
  ipureintro; exact hcp

end handle

end WalFs
end EtcdGrove
end Perennial

end
