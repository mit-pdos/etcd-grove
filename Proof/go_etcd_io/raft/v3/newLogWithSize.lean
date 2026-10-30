/-
Port of `election_proof/proof_newLogWithSize.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.newLogWithSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem newLogWithSize.wp_proof : newLogWithSize.spec (GF := GF) (hG := hG) := by
  intro si lg maxSize sn lok R Hlg Hmax
  subst Hlg
  wp_start as ⟨HR, #HFirstIndex, #HLastIndex, #Hlg⟩
  wp_auto
  -- (U8 v2 step 4) the boot bundle's reads: a fresh storage
  wp_apply_raw HFirstIndex $$ [$HR]
  inext
  iintro HR
  wp_auto
  wp_apply_raw HLastIndex $$ [$HR]
  inext
  iintro HR
  wp_auto
  irename «$r0» => Hl
  generalize «$r0_ptr» = l at *
  iapply HΦ $$ %l %(W64 0 + W64 1)
  iframe HR
  isplitr
  · ipureintro; rfl
  · iintro #Hsto2 HStorage
    unfold ownRaftLog
    iexists _, ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } : StorState)
    simp only [named, List.append_nil]
    iframe Hl Hsto2
    isplitr
    · ipureintro; apply BitVec.eq_of_toNat_eq; word
    isplitr
    · ipureintro; apply BitVec.eq_of_toNat_eq; word
    isplitr
    · ipureintro; apply BitVec.eq_of_toNat_eq; word
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; intro _; first | rfl | trivial
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; intro _ _ h; simp at h
    isplitr
    · ipureintro; simp only [List.length_nil]; word
    -- (D22 S-d1b) the storage, not lent
    isplitl [HStorage]
    · iapply lentStor_close (b := false) rfl; iexact HStorage
    isplitr
    · ipureintro; exact ⟨rfl, List.prefix_refl _, fun _ => rfl⟩
    isplitr
    · iapply (ownSnap_None _).2; ipureintro; rfl
    isplitr
    · iapply pendKsn_none
    isplitr
    · iapply ksnCerts_nil
    isplitr
    · ipureintro; simp only [List.length_nil]; rfl
    isplitr
    · iapply entsPts_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
    isplitr
    · ipureintro; intro _; exact Int.le_refl _
    isplitr
    · ipureintro; simp
    isplitr
    · unfold isLoggerVal; iexists lok; iframe Hlg; ipureintro; rfl
    isplitr
    · unfold isLoggerVal; iexists lok; iframe Hlg; ipureintro; rfl
    isplitr
    · ipureintro; simp only [List.length_nil]; word
    isplitr
    · ipureintro; intro _
      refine ⟨?_, ?_, fun _ => rfl, rfl⟩
      · simp [storApp]
      · intro _; simp [storApp]
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
    isplitr
    · ipureintro; intro _; word
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨rfl, fun _ e0 He0 => by simp at He0⟩
    isplitr
    · ipureintro
      refine ⟨rfl, by simp, by word, fun e0 He0 => by simp at He0, fun h => absurd rfl h,
        fun h => absurd rfl h⟩
    isplitr
    · ipureintro
      exact ⟨fun _ => ⟨by simp, by simp, fun _ h => by cases h⟩, rfl, DtOk.empty _⟩
    -- (D22 S-d1b) not lent, no window, no snapshot in progress
    isplitr
    · ipureintro; first | exact trivial | (intro h; cases h)
    isplitr
    · ipureintro; first | exact trivial | exact ⟨rfl, rfl⟩ | exact ⟨rfl, trivial⟩ | exact ⟨trivial, rfl⟩ | exact ⟨trivial, trivial⟩
    isplitr
    · ipureintro; first | exact trivial | (intro h; cases h) | exact ⟨(fun h => by cases h), (fun h => absurd rfl h)⟩
    ipureintro; first | exact trivial | (intro h; cases h)

end proof

end EtcdGrove
end Perennial
