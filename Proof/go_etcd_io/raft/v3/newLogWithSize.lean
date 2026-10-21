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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem newLogWithSize.wp_proof : newLogWithSize.spec (GF := GF) (hG := hG) := by
  intro st lg maxSize σ lok Hidx Hss Hpe Hlg Hmax Hfl0
  subst Hlg
  wp_start as ⟨#Hsto, HStorage, #Hlg, #Hic⟩
  ihave #Hsto2 : isStorage st $$ [Hsto]
  · iexact Hsto
  iNamed Hsto
  subst Hstok
  icases Hbounded $$ HStorage with ⟨%Hbnd, HStorage⟩
  wp_auto
  wp_apply HFirstIndex $$ HStorage as %fi ⟨%Hfi0, -, HStorage⟩
  -- (D19i part 1) the floor is not raised: the storage's boundary is the view's
  have Hfi : uint.Z fi = uint.Z σ.prev.index' + 1 := by
    rw [Hfl0, show uint.Z (W64 0) = 0 from rfl,
      Int.max_eq_left (show (0 : Int) ≤ uint.Z σ.prev.index' by word)] at Hfi0
    omega
  wp_apply HLastIndex $$ [$HStorage] as %li ⟨%Hli, HStorage⟩
  · ipureintro; exact Hpe
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  isplitr
  rotate_left
  · iframe HStorage
    iintro HStorage
    unfold ownRaftLog
    iexists _, σ
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
    · ipureintro; exact Hidx
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
    · ipureintro; exact initKsn_mem σ
    isplitr
    · iapply pendKsn_none
    isplitr
    · iunfold initKsnCert at Hic; iexact Hic
    isplitr
    · ipureintro; word
    isplitr
    · iapply entsPts_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; constructor <;> word
    isplitr
    · ipureintro; intro _; word
    isplitr
    · ipureintro; word
    isplitr
    · ipureintro; intro _
      rcases Hss with Hss | Hss
      · exact .inl Hss
      · exact .inr ⟨by rw [Hss]; word, by rw [Hss]; exact plogTermAt_base _ _⟩
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
    · ipureintro; word
    isplitr
    · ipureintro; intro _; word
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨Hpe, fun _ e0 He0 => by simp at He0⟩
    isplitr
    · ipureintro
      refine ⟨Hfl0, by simp, by word, fun e0 He0 => by simp [Hpe] at He0, fun h => absurd rfl h⟩
    -- (D22 S-d1b) not lent, no window, no snapshot in progress
    isplitr
    · ipureintro; first | exact trivial | (intro h; cases h)
    isplitr
    · ipureintro; first | exact trivial | exact ⟨rfl, rfl⟩ | exact ⟨rfl, trivial⟩ | exact ⟨trivial, rfl⟩ | exact ⟨trivial, trivial⟩
    isplitr
    · ipureintro; first | exact trivial | (intro h; cases h) | exact ⟨(fun h => by cases h), (fun h => absurd rfl h)⟩
    ipureintro; first | exact trivial | (intro h; cases h)
  · ipureintro; word

end proof

end EtcdGrove
end Perennial
