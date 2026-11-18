/-
The definitions and lemmas of `DB__mmap.lean`'s proof, in a module of their own so that the
crash proofs (`DB__mmapCrash.lean`) import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__munmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.mmapSize
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.pageAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Page__meta
public import Spec.os.File__Fd
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Madvise
public import Spec.golang_org.x.sys.unix.Munmap
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

/-- What `munmap` leaves the writer besides `mappingRes`, in the state `st`. -/
def unmapRest (p : Ino) (m : OsMeta) : MapSt → IProp GF
  | some (base, len, _) => iprop(⌜m.maps = {[base := len]} ∧ 0 < base.addr⌝)
  | none => iprop(osMeta (GF := GF) p (DFrac.own 1) m ∗ ⌜m.maps = ∅⌝)

/-- Before `munmap`: with a mapping, close its invariant and gather its cells; without one, the
writer has what the precondition gives. Either way, the writer then has `writerExtra`, the
invariant's half of `out`, and the committed pages. -/
theorem mmap_prep (γ : DBNames) (f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) (m : OsMeta) (st : MapSt) (h2 : 2 ≤ hwm) (hsz : 4096 * hwm ≤ m.size) :
    osInv (GF := GF) ∗ ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ osMeta (GF := GF) γ.ino (DFrac.own 1) m ∗
      mmapPre (GF := GF) γ f fd p mp fl hwm m st ∗ mapRest (GF := GF) γ f fd p 1 st ⊢
    |={⊤}=> ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half false ∗ writerExtra (GF := GF) γ f fd p mp fl hwm ∗
      ghostVar γ.out (1 : Qp).half false ∗
      ([∗list] r ∈ List.range' 2 (hwm - 2), ∃ B, pageIs (GF := GF) γ.ino r B) ∗
      mappingRes (GF := GF) γ.ino m (mapSlice st) ∗ unmapRest (GF := GF) γ.ino m st ∗
      ⌜∀ base len γm, st = some (base, len, γm) → 0 < base.addr⌝ := by
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only [mmapPre, mapRest, mapSlice, unmapRest]
    iintro ⟨#Hos, Hcur, Hout, Hm, ⟨%Hmaps, Hx, Ho, Hps⟩, -⟩
    imodintro
    iframe
    unfold mappingRes
    isplitl []
    · ileft; ipureintro; rfl
    isplitl
    · iframe; ipureintro; exact Hmaps
    · ipureintro; intro _ _ _ h; cases h
  · dsimp only [mmapPre, mapRest, mapSlice, unmapRest]
    iintro ⟨#Hos, Hcur, Hout, Hm, ⟨%Hf, Htok, Hwc⟩, ⟨-, Htok2, #Hinv, Hf2, Hfd2⟩⟩
    obtain ⟨Hmaps, Hlen, Hbase, Hlen41⟩ := Hf
    icombine Htok Htok2 as Htok
    ihave Hc := mapInv_close γ γ.ino base len γm $$ [Htok]
    · iframe; iframe #
    imod Hc
    icases Hc with >Hc
    iunfold _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.mapCells at Hc
    icases Hc with ⟨%mp', %fl', %hwm', Hcur2, %Hl, Hpc, Hmc⟩
    icombine Hcur Hcur2 gives % ⟨_, Heq⟩
    simp only [Prod.mk.injEq] at Heq
    obtain ⟨rfl, rfl, rfl⟩ := Heq
    icases Hmc with (Hout2 | ⟨Hout2, %mc, Hm0, Hm1, %Hmc⟩)
    · icombine Hout Hout2 gives % ⟨_, Heq⟩
      cases Heq
    icases pagesCells_split γ.ino base (hwm - 2) 2 $$ Hpc with ⟨Hps, Hpc⟩
    rw [show 4096 * 2 = 8192 by rfl]
    ihave Hall := mapCells_gather base hwm len h2 Hl mc Hmc.1 $$ [Hwc Hm0 Hm1 Hpc]
    · iframe
    iunfold cellsAny at Hall
    icases Hall with ⟨%vf, Hall⟩
    imodintro
    iframe
    unfold writerExtra mappingRes
    iframe
    isplitl [Hall Hm]
    · iright
      iexists base, W64 len, vf
      have hl : (W64 (len : Int)).toNat = len := by
        rw [BitVec.toNat_ofInt]; omega
      rw [hl]
      iframe; iframe #
      ipureintro
      refine ⟨rfl, Hbase, ?_, ?_⟩
      · have := sint_Z_W64_nat len (by omega); simp only [sint.Z] at this; omega
      · rw [Hmaps]; simp
    · isplit
      · ipureintro; exact ⟨Hmaps, Hbase⟩
      · ipureintro; intro b l g h; cases h; exact Hbase

theorem errnoErr_ne_nil (e : w64) (h : e ≠ 0) : errnoErr e ≠ interface.nil := by
  unfold errnoErr; rw [if_neg h]; simp

/-- After `munmap`: the file's `OsMeta`, of the same size, with no mapping if it succeeded. -/
theorem mmap_unmapped (p : Ino) (m : OsMeta) (st : MapSt) (err : GoInterface) :
    unmappedRes (GF := GF) p m (mapSlice st) err ∗ unmapRest (GF := GF) p m st ⊢
      ∃ m', osMeta (GF := GF) p (DFrac.own 1) m' ∗
        ⌜m'.size = m.size ∧ (m'.dhi = m.dhi ∧ m'.dlo = m.dlo) ∧ (err = interface.nil → m'.maps = ∅)⌝ := by
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only [unmapRest]
    iintro ⟨-, Hm, %Hmaps⟩
    iexists m; iframe; ipureintro; exact ⟨rfl, ⟨rfl, rfl⟩, fun _ => Hmaps⟩
  · dsimp only [unmapRest, mapSlice]
    iintro ⟨Hu, %Hr⟩
    obtain ⟨Hmaps, Hbase⟩ := Hr
    unfold unmappedRes
    icases Hu with (%Hnil | ⟨%b, %l, %vf, %e, %Heq, Hu⟩)
    · exfalso
      have := congrArg GoSlice.ptr Hnil.1; simp [slice.nil] at this; subst this
      simp [null] at Hbase
    · obtain ⟨Hsl, rfl⟩ := Heq
      have hb : b = base := (congrArg GoSlice.ptr Hsl).symm
      subst hb
      icases Hu with (⟨%He, Hm⟩ | ⟨%He, (Hm | ⟨Hm, -⟩)⟩)
      · iexists _; iframe; ipureintro
        refine ⟨rfl, ⟨rfl, rfl⟩, fun _ => ?_⟩
        simp only [Hmaps]; exact GMap.delete_singleton _ _
      · iexists _; iframe; ipureintro
        exact ⟨rfl, ⟨rfl, rfl⟩, fun h => absurd h (errnoErr_ne_nil e He)⟩
      · iexists _; iframe; ipureintro
        exact ⟨rfl, ⟨rfl, rfl⟩, fun h => absurd h (errnoErr_ne_nil e He)⟩

theorem mapSlice_ite {α : Type} (st : MapSt)
    (h : ∀ base len γm, st = some (base, len, γm) → 0 < base.addr) (a : MapSt → α) (z : α)
    (ha : a none = z) : (if mapSlice st = slice.nil then a st else z) = z := by
  by_cases hs : mapSlice st = slice.nil
  · rw [if_pos hs, (mapSlice_nil_iff st h).1 hs, ha]
  · rw [if_neg hs]

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
