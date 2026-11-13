/-
Shared definitions of `fileutil`'s split specs (I3b of `notes/wal-fsext-plan.md`: a file whose
resources are split between the caller and atomic updates, as the WAL's tail between its handle and
`walInv`): `preGrownH`, the caller's half of `preGrown` (`Defs.lean`), and how the resizes' halves
outcomes (`os.ftDoneH`, `os.ftUndoneH`, `fallocOutH`) give it. Lean-first. Untrusted.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Defs
public import LinuxFs.Spec.os.File__TruncateAu
public import LinuxFs.Proof.syscall.FallocateAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The caller's half of `preGrown`**: the file `i`, of `OsMeta` `m` before, grown to the size `w`:
its `OsMeta`'s half (of that size, `m`'s mappings, the page cache known zero past the size at least
as far) and its half of the new bytes, zeros. -/
def preGrownH (i : Ino) (m : OsMeta) (w : Nat) : IProp GF :=
  iprop(∃ m' : OsMeta, ⌜m'.size = w ∧ m'.maps = m.maps ∧ m.cz ≤ m'.cz⌝ ∗
    osMeta i (DFrac.own (1 : Qp).half) m' ∗ osZerosA i m.size (w - m.size) (DFrac.own (1 : Qp).half))

theorem osZerosA_nil (i : Ino) (lo : Nat) (dq : DFrac) : ⊢ osZerosA (GF := GF) i lo 0 dq := by
  iapply (osZerosA_unfold i lo 0 _).2
  iexists []
  isplitr
  · ipureintro; rfl
  rw [List.map_nil]; unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro

theorem rsPost_maps (tr : Bool) (m : OsMeta) (tg sz' : Nat) : (rsPost tr m tg sz').maps = m.maps := by
  simp [rsPost, OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

theorem announce_maps' (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).maps = m.maps := by
  simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

theorem announce_size' (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).size = m.size := by
  simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

theorem announce_cz' (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).cz = m.cz := by
  simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

/-- Not grown. -/
theorem preGrownH_same (i : Ino) (m : OsMeta) :
    osMeta (GF := GF) i (DFrac.own (1 : Qp).half) m ⊢ preGrownH i m m.size := by
  iintro Hm
  unfold preGrownH
  iexists m
  iframe Hm
  isplitr
  · ipureintro; exact ⟨rfl, rfl, Nat.le_refl _⟩
  rw [Nat.sub_self]
  iapply osZerosA_nil

/-- Two growths in a row are one. -/
theorem preGrownH_trans (i : Ino) (m m1 : OsMeta) (w : Nat) (h1 : m.size ≤ m1.size)
    (h2 : m1.size ≤ w) (hmaps : m1.maps = m.maps) (hcz : m.cz ≤ m1.cz) :
    osZerosA (GF := GF) i m.size (m1.size - m.size) (DFrac.own (1 : Qp).half) ∗ preGrownH i m1 w ⊢
      preGrownH i m w := by
  iintro ⟨Hz, Hg⟩
  unfold preGrownH
  icases Hg with ⟨%m', %hm', Hm, Hz'⟩
  iexists m'
  iframe Hm
  isplitr
  · ipureintro; exact ⟨hm'.1, hm'.2.1.trans hmaps, Nat.le_trans hcz hm'.2.2⟩
  have hw : w - m.size = (m1.size - m.size) + (w - m1.size) := by omega
  rw [hw]
  iapply (osZerosA_add i m.size _ _ _).2
  rw [show m.size + (m1.size - m.size) = m1.size by omega]
  iframe

/-- A growth that landed with the size `w`: grown. -/
theorem fallocDoneH_preGrownH (i : Ino) (m : OsMeta) (tg w : Nat) :
    fallocDoneH (GF := GF) i m tg w ⊢ preGrownH i m w := by
  unfold fallocDoneH preGrownH
  iintro ⟨%tc, Hm, Hz⟩
  iexists (rsPost false m tg w).withTc tc
  iframe
  ipureintro
  exact ⟨rfl, rsPost_maps false m tg w, os.le_rsPost_cz false m tg w⟩

/-- A growth's outcome: grown to some `w` between the size and the target, all of it on success. -/
theorem fallocOutH_preGrownH (i : Ino) (m : OsMeta) (tg : Nat) (e : w64) (hle : m.size ≤ tg) :
    fallocOutH (GF := GF) i tg m e ⊢ ∃ w, ⌜m.size ≤ w ∧ w ≤ tg ∧ (e = 0 → w = tg)⌝ ∗
      preGrownH i m w := by
  unfold fallocOutH
  iintro H
  icases H with (⟨%he, Hd⟩ | ⟨%he, (Hm | ⟨%w, %hw, Hd⟩)⟩)
  · iexists tg
    isplitr
    · ipureintro; exact ⟨hle, Nat.le_refl _, fun _ => rfl⟩
    iapply fallocDoneH_preGrownH $$ Hd
  · iexists m.size
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, hle, fun h => absurd h he⟩
    unfold preGrownH
    iexists _
    iframe Hm
    isplitr
    · ipureintro; exact ⟨announce_size' .., announce_maps' .., Nat.le_of_eq (announce_cz' ..).symm⟩
    rw [Nat.sub_self]
    iapply osZerosA_nil
  · iexists w
    isplitr
    · ipureintro; exact ⟨hw.1, hw.2, fun h => absurd h he⟩
    iapply fallocDoneH_preGrownH $$ Hd

/-- A truncate that landed, growing the file (`os.ftDoneH`): grown. -/
theorem ftDoneH_preGrownH (p : Ino) (m : OsMeta) (tg : Nat) (zs : List Cands) :
    os.ftDoneH (GF := GF) p m tg zs ⊢ preGrownH p m tg := by
  unfold os.ftDoneH preGrownH
  iintro ⟨%hzs, ⟨%tc, Hm⟩, Hb⟩
  iexists (rsPost true m tg tg).withTc tc
  iframe Hm
  isplitr
  · ipureintro
    exact ⟨rfl, rsPost_maps true m tg tg, by simp only [OsMeta.withTc_cz, rsPost, rsCz, ite_true]; omega⟩
  iapply (osZerosA_unfold p m.size _ _).2
  iexists zs
  iframe Hb
  ipureintro; exact hzs

/-- A truncate that did not land, with nothing to cut off (`os.ftUndoneH`): not grown. -/
theorem ftUndoneH_preGrownH (p : Ino) (m : OsMeta) (tg : Nat) :
    os.ftUndoneH (GF := GF) p m tg [] ⊢ preGrownH p m m.size := by
  unfold os.ftUndoneH preGrownH
  iintro ⟨Hm, -⟩
  iexists _
  iframe Hm
  isplitr
  · ipureintro; exact ⟨announce_size' .., announce_maps' .., Nat.le_of_eq (announce_cz' ..).symm⟩
  rw [Nat.sub_self]
  iapply osZerosA_nil

end defs

end EtcdGrove
end Perennial
