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
public import LinuxFs.Proof.os.PcKeep

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
as far, knowing the candidates past both sizes `m` knew, `PcKeep`, the zeros known from the page cache
known zero on if `Z`, `OsMeta.ZeroPg`) and its half of the new bytes, zeros. -/
def preGrownH (i : Ino) (m : OsMeta) (w : Nat) (Z : Prop) : IProp GF :=
  iprop(∃ m' : OsMeta, ⌜m'.size = w ∧ m'.maps = m.maps ∧ m.cz ≤ m'.cz ∧ GrowMeta m m' ∧ PcKeep m m' ∧
      (Z → m'.ZeroPg)⌝ ∗
    osMeta i (DFrac.own (1 : Qp).half) m' ∗ osZerosA i m.size (w - m.size) (DFrac.own (1 : Qp).half))

/-- **What `ZeroToEnd`'s split form keeps of the `OsMeta` `m`** (`ZeroToEnd.specAu`'s success post, `m'`
of the same size): the candidates known past the size (`PcKeep`), and, if `m` knew zeros from at least
its size, zeros known from the page cache known zero on (`OsMeta.ZeroPg`). With the WAL's `TailZ m` it
gives `TailZ m'`. -/
def ZteMeta (m m' : OsMeta) : Prop := PcKeep m m' ∧ (m.ZfGe → m'.ZeroPg)

/-- A weaker condition. -/
theorem preGrownH_mono (i : Ino) (m : OsMeta) (w : Nat) {Z Z' : Prop} (h : Z' → Z) :
    preGrownH (GF := GF) i m w Z ⊢ preGrownH i m w Z' := by
  unfold preGrownH
  iintro ⟨%m', %hm', Hm, Hz⟩
  iexists m'
  iframe Hm Hz
  ipureintro
  exact ⟨hm'.1, hm'.2.1, hm'.2.2.1, hm'.2.2.2.1, hm'.2.2.2.2.1, fun hz => hm'.2.2.2.2.2 (h hz)⟩

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
theorem preGrownH_same (i : Ino) (m : OsMeta) (Z : Prop) (hZ : Z → m.ZeroPg) :
    osMeta (GF := GF) i (DFrac.own (1 : Qp).half) m ⊢ preGrownH i m m.size Z := by
  iintro Hm
  unfold preGrownH
  iexists m
  iframe Hm
  isplitr
  · ipureintro; exact ⟨rfl, rfl, Nat.le_refl _, GrowMeta.refl m, PcKeep.refl m, hZ⟩
  rw [Nat.sub_self]
  iapply osZerosA_nil

/-- Two growths in a row are one. -/
theorem preGrownH_trans (i : Ino) (m m1 : OsMeta) (w : Nat) (Z : Prop) (h1 : m.size ≤ m1.size)
    (h2 : m1.size ≤ w) (hmaps : m1.maps = m.maps) (hcz : m.cz ≤ m1.cz) (hg : GrowMeta m m1)
    (hpc : PcKeep m m1) :
    osZerosA (GF := GF) i m.size (m1.size - m.size) (DFrac.own (1 : Qp).half) ∗ preGrownH i m1 w Z ⊢
      preGrownH i m w Z := by
  iintro ⟨Hz, Hg⟩
  unfold preGrownH
  icases Hg with ⟨%m', %hm', Hm, Hz'⟩
  iexists m'
  iframe Hm
  isplitr
  · ipureintro
    exact ⟨hm'.1, hm'.2.1.trans hmaps, Nat.le_trans hcz hm'.2.2.1, hg.trans hm'.2.2.2.1,
      hpc.trans hm'.2.2.2.2.1 (by omega), hm'.2.2.2.2.2⟩
  have hw : w - m.size = (m1.size - m.size) + (w - m1.size) := by omega
  rw [hw]
  iapply (osZerosA_add i m.size _ _ _).2
  rw [show m.size + (m1.size - m.size) = m1.size by omega]
  iframe

/-- A growth that landed with the size `w`: grown. -/
theorem fallocDoneH_preGrownH (i : Ino) (m : OsMeta) (tg w : Nat) (Z : Prop) (hw : m.size ≤ w)
    (hle : w ≤ tg) (hZ : Z → m.ZeroPg) :
    fallocDoneH (GF := GF) i m tg w ⊢ preGrownH i m w Z := by
  unfold fallocDoneH preGrownH
  iintro ⟨%tc, %rz, %htc, Hm, Hz⟩
  iexists (rsPost false m tg w).withTc tc rz
  iframe
  ipureintro
  exact ⟨rfl, rsPost_maps false m tg w, os.le_rsPost_cz false m tg w,
    growMeta_rsPost false m tg w (.inl hw) (by omega), PcKeep.of_tc (tr := false) rfl rfl htc,
    fun hz => OsMeta.zeroPg_rsPost_false (hZ hz) tg w hw hle⟩

/-- A growth's outcome: grown to some `w` between the size and the target, all of it on success. -/
theorem fallocOutH_preGrownH (i : Ino) (m : OsMeta) (tg : Nat) (e : w64) (hle : m.size ≤ tg) :
    fallocOutH (GF := GF) i tg m e ⊢ ∃ w, ⌜m.size ≤ w ∧ w ≤ tg ∧ (e = 0 → w = tg)⌝ ∗
      preGrownH i m w (e = 0 ∧ m.ZeroPg) := by
  unfold fallocOutH
  iintro H
  icases H with (⟨%he, Hd⟩ | ⟨%he, (⟨%tc, %rz, %htc, Hm⟩ | ⟨%w, %hw, Hd⟩)⟩)
  · iexists tg
    isplitr
    · ipureintro; exact ⟨hle, Nat.le_refl _, fun _ => rfl⟩
    iapply fallocDoneH_preGrownH (hw := hle) (hle := Nat.le_refl _) (hZ := fun h => h.2) $$ Hd
  · iexists m.size
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, hle, fun h => absurd h he⟩
    unfold preGrownH
    iexists _
    iframe Hm
    isplitr
    · ipureintro
      exact ⟨announce_size' m (min m.size tg) (rsHi false m.size tg) tg,
        announce_maps' m (min m.size tg) (rsHi false m.size tg) tg,
        Nat.le_of_eq (announce_cz' m (min m.size tg) (rsHi false m.size tg) tg).symm,
        growMeta_announce m (min m.size tg) (rsHi false m.size tg) tg,
        PcKeep.of_tc (tr := false) (announce_size' m (min m.size tg) (rsHi false m.size tg) tg) rfl htc, fun h => absurd h.1 he⟩
    rw [Nat.sub_self]
    iapply osZerosA_nil
  · iexists w
    isplitr
    · ipureintro; exact ⟨hw.1, hw.2, fun h => absurd h he⟩
    iapply fallocDoneH_preGrownH (hw := hw.1) (hle := hw.2) (hZ := fun h => h.2) $$ Hd

/-- A truncate that landed, growing the file (`os.ftDoneH`): grown. -/
theorem ftDoneH_preGrownH (p : Ino) (m : OsMeta) (tg : Nat) (zs : List Cands) (Z : Prop)
    (hZ : Z → m.ZfGe) :
    os.ftDoneH (GF := GF) p m tg zs ⊢ preGrownH p m tg Z := by
  unfold os.ftDoneH preGrownH
  iintro ⟨%hzs, ⟨%tc, %rz, %htc, Hm⟩, Hb⟩
  iexists (rsPost true m tg tg).withTc tc rz
  iframe Hm
  isplitr
  · ipureintro
    exact ⟨rfl, rsPost_maps true m tg tg, by simp only [OsMeta.withTc_cz]; exact le_rsCz true m tg,
      growMeta_rsPost true m tg tg (Or.inr rfl) (Nat.le_max_right _ _),
      PcKeep.of_tc (tr := true) rfl rfl htc, fun hz => OsMeta.zeroPg_rsPost_true (hZ hz) tg⟩
  iapply (osZerosA_unfold p m.size _ _).2
  iexists zs
  iframe Hb
  ipureintro; exact hzs

/-- A truncate that did not land, with nothing to cut off (`os.ftUndoneH`): not grown. -/
theorem ftUndoneH_preGrownH (p : Ino) (m : OsMeta) (tg : Nat) :
    os.ftUndoneH (GF := GF) p m tg [] ⊢ preGrownH p m m.size False := by
  unfold os.ftUndoneH preGrownH
  iintro ⟨⟨%tc, %rz, %htc, Hm⟩, -⟩
  iexists _
  iframe Hm
  isplitr
  · ipureintro
    exact ⟨announce_size' m (min m.size tg) (rsHi true m.size tg) tg,
      announce_maps' m (min m.size tg) (rsHi true m.size tg) tg,
      Nat.le_of_eq (announce_cz' m (min m.size tg) (rsHi true m.size tg) tg).symm,
      growMeta_announce m (min m.size tg) (rsHi true m.size tg) tg,
      PcKeep.of_tc (tr := true) (announce_size' m (min m.size tg) (rsHi true m.size tg) tg) rfl htc, False.elim⟩
  rw [Nat.sub_self]
  iapply osZerosA_nil

end defs

end EtcdGrove
end Perennial
