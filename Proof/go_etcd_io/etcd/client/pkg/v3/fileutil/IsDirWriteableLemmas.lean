/-
The lemmas of `IsDirWriteable.lean`'s proof (`touch_nameOk`, `abs_child`, `os.rmFileOut_join`, ...), in a
module of their own so that the function's other proofs import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable
public import Proof.os.WriteFileLemmas
public import Spec.os.File__Close
public import Proof.os.OffLong
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import Spec.path.filepath.Join
public import Spec.path.filepath.Abs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions]

theorem touch_nameOk : NameOk go!".touch" := by decide

/-- `filepath.Abs` of `d/b` for a clean absolute `d` and a name `b`: itself. -/
theorem abs_child {d b : GoString} (hd : filepath.CleanAbs d) (hb : NameOk b) :
    path.cleanModel (child d b) = child d b := by
  rw [← join_child hd hb, filepath.joinModel_name d b hd (cleanSeg_of_nameOk hb)]
  exact filepath.cleanModel_cleanAbs _ (filepath.cleanAbs_append d b hd (cleanSeg_of_nameOk hb))

theorem child_head {d b : GoString} (hd : filepath.CleanAbs d) : (child d b).head? = some (W8 47) := by
  obtain ⟨segs, hne, -, rfl⟩ := hd
  cases segs with
  | nil => exact absurd rfl hne
  | cons s segs => simp [child, path.segsPath]

/-- A spine's path is a clean absolute path; the spine kept. -/
theorem osPathS_cleanAbs_keep (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) :
    osPathS (GF := GF) R d dq j ⊢ osPathS R d dq j ∗ ⌜filepath.CleanAbs d⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %h, Hs⟩
  obtain ⟨hR, hr, hcs, rfl⟩ := h
  isplitl [Hs]
  · iexists r, j0, cs; iframe; ipureintro; exact ⟨hR, hr, hcs, rfl⟩
  · ipureintro; exact cleanAbs_joinPath hR hr hcs

/-- An unlink's outcome on a whole claim, as two halves. -/
theorem os.rmFileOut_join (j : Ino) (b : GoString) (i : Ino) (h : NamesH) (o : Option (Nat × Nat)) :
    rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half) o ∗
      rmFileOut (GF := GF) j b i h (DFrac.own (1 : Qp).half) o ⊢
      ∃ h', osNames (GF := GF) j (.only [b]) (DFrac.own 1) h' ∗
        ⌜(o.isSome → h'.cur !! b = none) ∧ (h'.cur !! b = none ∨ h'.cur !! b = h.cur !! b)⌝ := by
  unfold rmFileOut
  cases o with
  | none =>
    simp only [claimOut]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
    iexists h
    isplitl [H1 H2]
    · iapply (osNames_join j _ _ _ h (Qp.half_add_half 1)).1 $$ [$H1 $H2]
    ipureintro; exact ⟨fun hc => (by cases hc), Or.inr rfl⟩
  | some xs =>
    obtain ⟨x, s⟩ := xs
    simp only [claimOut]
    iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
    iexists _
    isplitl [H1 H2]
    · iapply (osNames_join j _ _ _ _ (Qp.half_add_half 1)).1 $$ [$H1 $H2]
    ipureintro
    have hn : (restrictN (.only [b]) (GMap.delete b h.cur)) !! b = none := by
      rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem]), GMap.lookup_delete]
    simp only [NamesH.log]
    exact ⟨fun _ => hn, Or.inl hn⟩

end proof

end EtcdGrove
end Perennial
