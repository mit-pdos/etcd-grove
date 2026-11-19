/-
The proof of `Spec/golang_org/x/sys/unix/Madvise.lean`: an arbitrary errno.
-/
module

public import Spec.golang_org.x.sys.unix.Madvise
public import GooseLang.Ext.Fs.Madvise
public import Perennial.Golang.Theory.Unsafe
public import GooseLang.Ext.Fs.NoMapLockErrSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

/-- `Madvise.spec` with no mapping named (session S6: a helper of the proof below). -/
private abbrev golang_org.x.sys.unix.Madvise.tripleOld : Prop :=
  ∀ (sl : GoSlice) (advice : w64), advice.toNat ≤ 3 → 0 ≤ sl.len.toInt →
  {{ osInv (GF := GF) }}
    (App (App (Val (@! golang_org.x.sys.unix.Madvise)) (Val #sl)) (Val #advice))
  {{ (e : w64), RET #(errnoErr e); emp }}

/-- `Madvise.spec` of a mapping over a semantics with no `madvise` error (the former `specNoErr`). -/
private abbrev golang_org.x.sys.unix.Madvise.tripleNE : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (base : Loc) (len cap advice : w64) (p : Ino) (dq : DFrac) (m : OsMeta) (n : Nat),
  advice.toNat ≤ 3 → 0 < base.addr → 0 < len.toInt → m.maps !! base = some n →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p dq m }}
    (App (App (Val (@! golang_org.x.sys.unix.Madvise)) (Val #(⟨base, len, cap⟩ : GoSlice)))
      (Val #advice))
  {{ RET #(errnoErr 0); osMeta p dq m }}

private theorem golang_org.x.sys.unix.Madvise.wp_old :
    golang_org.x.sys.unix.Madvise.tripleOld (GF := GF) (hG := hG) := by
  intro sl advice hadv hlen
  wp_start as #Hinv
  have h : uint.Z advice ≤ uint.Z (W64 3) := by
    simp only [uint.Z]; have : (W64 3).toNat = 3 := rfl; omega
  rw [decide_eq_true h]
  wp_auto
  by_cases hl0 : sl.len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    wp_apply wp_ArbitraryInt as %x _
    iapply wp_errno
    iapply HΦ
    iempintro
  · rw [decide_eq_false hl0]
    wp_auto
    by_cases h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len
    · rw [if_pos h0]
      wp_auto
      wp_apply wp_osMadvise _ _ advice hadv CoPset.subseteq_top $$ Hinv
      iintro %e
      iapply wp_errno
      iapply HΦ
      iempintro
    · exfalso; apply h0
      have : sl.len.toInt ≠ 0 := fun h => hl0 (BitVec.eq_of_toInt_eq (by simpa using h))
      simp only [sint.Z]; exact ⟨by decide, by have := hlen; simp at *; omega⟩

private theorem golang_org.x.sys.unix.Madvise.wp_NE :
    golang_org.x.sys.unix.Madvise.tripleNE (GF := GF) (hG := hG) := by
  intro Sio _ hS base len cap advice p dq m n hadv hbase hpos hb
  wp_start as ⟨#Hinv, Hm⟩
  have h : uint.Z advice ≤ uint.Z (W64 3) := by
    simp only [uint.Z]; have : (W64 3).toNat = 3 := rfl; omega
  rw [decide_eq_true h]
  wp_auto
  have hl0 : len ≠ W64 0 := by rintro rfl; exact absurd hpos (by decide)
  rw [decide_eq_false hl0]
  wp_auto
  have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
    simp only [sint.Z]; exact ⟨by decide, hpos⟩
  rw [if_pos h0]
  rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, cap⟩ 0 hbase (Int.le_refl _)]
  have hb0 : (base +ₗ (0 : Int)) = base := by simp
  rw [hb0]
  wp_auto
  wp_apply wp_osMadviseNE hS base len advice p dq m n hadv hb CoPset.subseteq_top
    $$ Hinv Hm as Hm
  iapply wp_errno
  iapply HΦ
  iexact Hm

/-- **`Madvise.spec`**: with no mapping named, the triple with no witness; of a mapping, by cases on
`FsNoErr`, the error-free triple or that one (an error then has `¬ FsNoErr`). -/
theorem golang_org.x.sys.unix.Madvise.wp_proof : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG) := by
  intro sl advice M hadv hlen hM
  iintro %Φ ⟨#Hos, HM⟩ HΦ
  rcases M with _ | ⟨p, dq, m⟩
  · iapply golang_org.x.sys.unix.Madvise.wp_old sl advice hadv hlen $$ [Hos]
    · iexact Hos
    inext
    iintro %e -
    iapply HΦ
    iframe HM
    ipureintro; exact Or.inl rfl
  · obtain ⟨hb, hpos, n, hmap⟩ := hM p dq m rfl
    by_cases hne : FsNoErr
    · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
      haveI := hs2
      obtain ⟨base, len, cap⟩ := sl
      iapply golang_org.x.sys.unix.Madvise.wp_NE Sio hSio base len cap advice p dq m n hadv hb hpos
        hmap $$ [HM]
      · iframe; iframe #
      inext
      iintro Hm
      iapply HΦ
      iframe Hm
      ipureintro; exact Or.inr (Or.inl rfl)
    · iapply golang_org.x.sys.unix.Madvise.wp_old sl advice hadv hlen $$ [Hos]
      · iexact Hos
      inext
      iintro %e -
      iapply HΦ
      iframe HM
      ipureintro; exact Or.inr (Or.inr hne)

end proof

end EtcdGrove
end Perennial
