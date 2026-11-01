/-
Lean-first (no Rocq counterpart).

# The image's changes keep what `dmu` records of it (2026-11-01, stage II (h))

`kdDmuInv` records of the image's contents `M` its shape (`KdFileOk`) and, in the pending batch's
phase, that it holds a durable state (`StorageHolds S (kdContents (some M))`). The snapshotter's two
changes keep both:

* `create_ok`: a snapshot at `i` (not refused: past the image's snapshot) at most the image's commit
  index;
* `compact_ok`: a compaction to `x` (not refused: past the log's start) at most the image's snapshot
  and commit indices (and below `2^61`).

`kdPhaseInv_transport` carries the phase over a change that keeps every `StorageHolds`, and
`ownCSM_confWf` gives a configuration's lists' bounds (what a snapshot's encoding needs, `StorWf`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunFrozen

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A snapshot at `i`, past the image's and at most its commit index, keeps its shape and the
durable state it holds.** -/
theorem create_ok (M : StorFile) (i : w64) (co : Option ConfStateM) (bs : List w8)
    (Hok : KdFileOk M) (Hns : ¬ imgCreateStale M i)
    (Hc : uint.nat i ≤ uint.nat M.hs.Commit')
    (Hcw : ConfWf (co.getD M.snap.Metadata'.ConfState')) (Hbs : (bs.length : Int) < 2 ^ 63) :
    KdFileOk (imgCreateSnapshot M i co bs) ∧ ∀ S, StorageHolds S (kdContents (some M)) →
      StorageHolds S (kdContents (some (imgCreateSnapshot M i co bs))) := by
  unfold imgCreateStale at Hns
  obtain ⟨⟨Hsw, Hew, Hel⟩, Hp61, Hlen, Hidx, Hps, Hsl, Hpc, Hcl, Htie⟩ := Hok
  have Hi0 : i ≠ W64 0 := by intro h; subst h; word
  have Hpi : uint.nat M.prev ≤ uint.nat i := by word
  refine ⟨⟨⟨⟨Hcw, Hbs⟩, Hew, Hel⟩, Hp61, Hlen, Hidx, ?_, ?_, Hpc, Hcl, ?_⟩, ?_⟩
  · simp only [imgCreateSnapshot, memSnapMade]; word
  · simp only [imgCreateSnapshot, memSnapMade]; omega
  · exact ⟨Htie.1, rfl⟩
  · intro S Hh
    obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := Hh
    simp only [kdContents, imgCreateSnapshot, memSnapMade, StorContents.b, StorContents.commit] at H1 H2 H3 H4 H5 H6 H7 ⊢
    refine ⟨H1, H2, H3, H4, H5, H6, H7, ?_, ?_⟩
    · intro sv hsv
      simp only [Hi0, ↓reduceIte, Option.some.injEq] at hsv
      rw [← hsv]
      exact ⟨Hpi, Hc⟩
    · intro _; simp only [Hi0, ↓reduceIte, Option.isSome_some]

/-- The term `imgTermAt` reads past the log's start is the entry's there. -/
theorem imgTermAt_ent (M : StorFile) (x : w64) (k : Nat) (e : EntryM)
    (hx : uint.nat M.prev < uint.nat x) (hk : k = uint.nat x - uint.nat M.prev - 1)
    (he : M.ents[k]? = some e) : imgTermAt M x = e.Term' := by
  unfold imgTermAt
  rw [if_neg (by omega), ← hk, he]; rfl

/-- **A compaction to `x`, past the log's start and at most the image's snapshot index, keeps its
shape and the durable state it holds.** -/
theorem compact_ok (M : StorFile) (x : w64)
    (Hok : KdFileOk M) (Hns : ¬ imgCompactStale M x)
    (Hx : uint.nat x ≤ uint.nat M.snap.Metadata'.Index') (Hx61 : uint.nat x < 2 ^ 61)
    (Hxc : uint.nat x ≤ uint.nat M.hs.Commit') :
    KdFileOk (imgCompact M x) ∧ ∀ S, StorageHolds S (kdContents (some M)) →
      StorageHolds S (kdContents (some (imgCompact M x))) := by
  unfold imgCompactStale at Hns
  obtain ⟨⟨Hsw, Hew, Hel⟩, Hp61, Hlen, Hidx, Hps, Hsl, Hpc, Hcl, Htie⟩ := Hok
  have Hs0 : M.snap.Metadata'.Index' ≠ W64 0 := by intro h; rw [h] at Hx; word
  have Hpx : uint.nat M.prev < uint.nat x := by word
  have Hxl : uint.nat x ≤ uint.nat M.prev + M.ents.length := by omega
  refine ⟨⟨⟨Hsw, fun e he => Hew e (List.mem_of_mem_drop he), ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [imgCompact, List.length_drop]; omega
  · simp only [imgCompact]; word
  · simp only [imgCompact, List.length_drop]; word
  · intro j e he
    simp only [imgCompact, List.getElem?_drop] at he
    have := Hidx _ e he
    simp only [imgCompact]; omega
  · simp only [imgCompact]; word
  · simp only [imgCompact, List.length_drop]; omega
  · simp only [imgCompact]; word
  · simp only [imgCompact, List.length_drop]; omega
  · refine ⟨fun h => by simp only [imgCompact] at h; rw [h] at Hpx; word, ?_⟩
    simp only [imgCompact]
    rw [← Htie.2]
    unfold imgTermAt
    by_cases hsx : uint.nat M.snap.Metadata'.Index' ≤ uint.nat x
    · have hsx' : uint.nat M.snap.Metadata'.Index' = uint.nat x := by omega
      rw [if_pos hsx, if_neg (by omega), if_neg (by omega), hsx']
    · rw [if_neg hsx, List.getElem?_drop]
      simp only
      rw [if_neg (by omega)]
      congr 3; omega
  · intro S Hh
    obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := Hh
    simp only [kdContents, StorContents.b, StorContents.commit, Hs0, ↓reduceIte] at H1 H2 H3 H4 H5 H6 H7 H8 H9
    obtain ⟨H8a, H8b⟩ := H8 _ rfl
    simp only [kdContents, imgCompact, Hs0, ↓reduceIte]
    refine ⟨by word, ?_, ?_, H4, H5, Hxc, H7, ?_, ?_⟩
    · -- the term at `x`: `S`'s entry there, which the image's entries are
      have HSb : uint.Z S.base.index' ≤ uint.Z M.prev := H1
      obtain ⟨e, he⟩ : ∃ e, M.ents[uint.nat x - uint.nat M.prev - 1]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [imgTermAt_ent M x _ e Hpx rfl he]
      unfold plogTermAt
      rw [if_neg (by word), if_neg (by word)]
      unfold RaftState.entsFrom at H3
      simp only at H3
      have Hj : (uint.Z x - uint.Z S.base.index' - 1).toNat =
          (uint.Z M.prev - uint.Z S.base.index').toNat + (uint.nat x - uint.nat M.prev - 1) := by
        word
      rw [Hj, ← List.getElem?_drop, ← H3, he]; rfl
    · unfold RaftState.entsFrom at H3 ⊢
      simp only at H3 ⊢
      rw [H3, List.drop_drop]
      congr 1; word
    · intro sv hsv
      simp only [Option.some.injEq] at hsv
      rw [← hsv]
      exact ⟨Hx, H8b⟩
    · intro _; rfl

/-- A stored snapshot is at most the stored commit index. -/
theorem holds_snap_commit (S : RaftState) (M : StorFile) (Hh : StorageHolds S (kdContents (some M)))
    (h0 : M.snap.Metadata'.Index' ≠ W64 0) :
    uint.nat M.snap.Metadata'.Index' ≤ uint.nat M.hs.Commit' := by
  have H8 := Hh.2.2.2.2.2.2.2.1
  simp only [kdContents, h0, ↓reduceIte] at H8
  exact (H8 _ rfl).2

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- **The phase over a change of the image** that keeps every durable state it holds. -/
theorem kdPhaseInv_transport (γ : KdNames) (id : w64) (n : Loc) (ph : GName) (S : RaftState)
    (M M' : StorFile) (pz : KdPhase)
    (H : ∀ S, StorageHolds S (kdContents (some M)) → StorageHolds S (kdContents (some M'))) :
    kdPhaseInv (GF := GF) γ id n ph S M pz ⊢ kdPhaseInv γ id n ph S M' pz := by
  cases pz with
  | idle =>
    simp only [kdPhaseInv]
    iintro ⟨Hph, %Hh⟩
    iframe Hph
    ipureintro; exact H _ Hh
  | waiting st st' ms γb =>
    simp only [kdPhaseInv]
    iintro ⟨Hph, Hsv, Hen, %Hh⟩
    iframe Hph Hsv Hen
    ipureintro; exact ⟨Hh.1, H _ Hh.2⟩
  | fired γb =>
    simp only [kdPhaseInv]
    iintro ⟨Hph, HR, %Hh⟩
    iframe Hph
    isplitl [HR]
    · iexact HR
    ipureintro; exact H _ Hh

/-- **The phase holds some durable state** in the image. -/
theorem kdPhaseInv_holds (γ : KdNames) (id : w64) (n : Loc) (ph : GName) (S : RaftState)
    (M : StorFile) (pz : KdPhase) :
    kdPhaseInv (GF := GF) γ id n ph S M pz ⊢
      ⌜∃ S', StorageHolds S' (kdContents (some M))⌝ ∗ kdPhaseInv γ id n ph S M pz := by
  cases pz with
  | idle =>
    simp only [kdPhaseInv]
    iintro ⟨Hph, %Hh⟩
    iframe Hph
    ipureintro; exact ⟨⟨_, Hh⟩, Hh⟩
  | waiting st st' ms γb =>
    simp only [kdPhaseInv]
    iintro ⟨Hph, Hsv, Hen, %Hh⟩
    iframe Hph Hsv Hen
    ipureintro; exact ⟨⟨_, Hh.2⟩, Hh⟩
  | fired γb =>
    simp only [kdPhaseInv]
    iintro ⟨Hph, HR, %Hh⟩
    iframe Hph
    isplitr
    · ipureintro; exact ⟨_, Hh⟩
    isplitl [HR]
    · iexact HR
    ipureintro; exact Hh

/-- **The image's term at a frozen index** (2026-11-01, stage II (h)): past the log's start, at most
the frozen bound `fz` and the last index, the image's entry is the `MemoryStorage`'s frozen one. -/
theorem frozen_term (γs : MemStorNames) (M : StorFile) (fz : Nat) (i : w64) (e : EntryM)
    (hp : uint.nat M.prev < uint.nat i) (hf : uint.nat i ≤ fz)
    (hl : uint.nat i ≤ uint.nat M.prev + M.ents.length) :
    memLog (GF := GF) γs (uint.nat M.prev + 1) DFrac.discard (M.ents.take (fz - uint.nat M.prev)) ∗
      memLog γs (uint.nat i) DFrac.discard [e] ⊢ ⌜imgTermAt M i = e.Term'⌝ := by
  iintro ⟨Hf, He⟩
  have hj : uint.nat i - uint.nat M.prev - 1 < M.ents.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, M.ents[uint.nat i - uint.nat M.prev - 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  have hx' : (M.ents.take (fz - uint.nat M.prev))[uint.nat i - uint.nat M.prev - 1]? = some x := by
    rw [List.getElem?_take, if_pos (by omega), hx]
  ihave Hx := kvreconf.memLog_elem γs _ _ _ _ x hx' $$ Hf
  rw [show uint.nat M.prev + 1 + (uint.nat i - uint.nat M.prev - 1) = uint.nat i by omega]
  unfold memLog
  icases Hx with ⟨Hx, -⟩
  icases He with ⟨He, -⟩
  ihave %Hag := kdLogL_agree γs.log _ _ _ _ [x] [e] $$ [$Hx $He]
  have hxe : x = e := Hag (uint.nat i) x e (Nat.le_refl _) (Nat.le_refl _) (by simp) (by simp)
  subst hxe
  ipureintro
  exact imgTermAt_ent M i _ x hp rfl hx

/-- **The frozen record after a compaction to `x`** (past the log's start, within it). -/
theorem frozen_compact (γs : MemStorNames) (M : StorFile) (fz : Nat) (x : w64)
    (hp : uint.nat M.prev < uint.nat x) (hl : uint.nat x ≤ uint.nat M.prev + M.ents.length) :
    memLog (GF := GF) γs (uint.nat M.prev + 1) DFrac.discard (M.ents.take (fz - uint.nat M.prev)) ⊢
      memLog γs (uint.nat x + 1) DFrac.discard
        ((M.ents.drop (uint.nat x - uint.nat M.prev)).take (fz - uint.nat x)) := by
  by_cases hfx : fz ≤ uint.nat x
  · iintro -
    rw [show fz - uint.nat x = 0 by omega, List.take_zero]
    iapply memLog_nil
  · have hsplit : M.ents.take (fz - uint.nat M.prev) =
        M.ents.take (uint.nat x - uint.nat M.prev) ++
          (M.ents.drop (uint.nat x - uint.nat M.prev)).take (fz - uint.nat x) := by
      rw [show fz - uint.nat M.prev = (uint.nat x - uint.nat M.prev) + (fz - uint.nat x) by omega,
        List.take_add]
    rw [hsplit]
    iintro H
    icases (memLog_app γs _ _ _ _).1 $$ H with ⟨-, H⟩
    rw [List.length_take_of_le (by omega),
      show uint.nat M.prev + 1 + (uint.nat x - uint.nat M.prev) = uint.nat x + 1 by omega]
    iexact H

/-- A configuration's lists are of Go slices' lengths. -/
theorem ownCSM_confWf (p : Loc) (dq : DFrac) (c : ConfStateM) :
    ownCSM (GF := GF) p dq c ⊢ ⌜ConfWf c⌝ := by
  iintro Hc
  simp only [ownCSM, csPts]
  iNamed Hc
  ihave %H1 := ownSlice_len $$ Hv
  ihave %H2 := ownSlice_len $$ Hl
  ihave %H3 := ownSlice_len $$ Ho
  ihave %H4 := ownSlice_len $$ Hn
  ipureintro
  unfold ConfWf
  refine ⟨?_, ?_, ?_, ?_⟩ <;> word

end ghost

end kvdurable
end EtcdGrove
end Perennial
