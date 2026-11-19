/-
The definitions and lemmas of `DB__Close.lean`'s proof, in a module of their own so that the
crash proofs (`DB__CloseCrash.lean`) import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__Close
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__close
public import Perennial.Proof.sync.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.MapInv

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

theorem ownFile_join (f : Loc) (fd : w64) (p : GoString) :
    os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ⊢ os.ownFile (GF := GF) f fd p (DFrac.own 1) := by
  conv => rhs; rw [← Qp.half_add_half 1]
  exact ((ownFile_fractional f fd p).fractional _ _).2

theorem osFd_join (fd : w64) (d : OsFd) :
    osFd (GF := GF) fd (DFrac.own (1 : Qp).half) d ∗ osFd (GF := GF) fd (DFrac.own (1 : Qp).half) d ⊢
      osFd (GF := GF) fd (DFrac.own 1) d := by
  conv => rhs; rw [← Qp.half_add_half 1]
  exact ((osFd_fractional fd d).fractional _ _).2

theorem errnoErr_ne_nil' (e : w64) (h : e ≠ 0) : errnoErr e ≠ interface.nil := by
  unfold errnoErr; rw [if_neg h]; simp

/-- After `close`'s successful `Munmap` of the whole mapping: the file's `OsMeta`, of the same
size, with no mapping. -/
theorem close_unmapped (p : Ino) (m : OsMeta) (base : Loc) (len : Nat) (err : GoInterface)
    (hm : m.maps = {[base := len]}) (hb : 0 < base.addr) (herr : err = interface.nil) :
    unmappedRes (GF := GF) p m ⟨base, W64 len, W64 len⟩ err ⊢
      ∃ m', osMeta (GF := GF) p (DFrac.own 1) m' ∗
        ⌜m'.size = m.size ∧ (m'.dhi = m.dhi ∧ m'.dlo = m.dlo) ∧ m'.maps = ∅⌝ := by
  unfold unmappedRes
  iintro (%Hnil | ⟨%b, %l, %vf, %e, %Heq, Hu⟩)
  · exfalso
    have := congrArg GoSlice.ptr Hnil.1; simp [slice.nil] at this; subst this
    simp [null] at hb
  · obtain ⟨Hsl, rfl⟩ := Heq
    cases Hsl
    by_cases he : e = 0
    · icases Hu with (⟨-, Hm⟩ | ⟨%He, -⟩)
      · iexists _; iframe
        ipureintro; refine ⟨rfl, ⟨rfl, rfl⟩, ?_⟩; simp only [hm]; exact GMap.delete_singleton _ _
      · exact absurd he He
    · exact absurd herr (errnoErr_ne_nil' e he)

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
