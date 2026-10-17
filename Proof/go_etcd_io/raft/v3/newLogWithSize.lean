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
  intro st lg maxSize σ lok Hidx Hss Hpe Hlg Hmax
  subst Hlg
  wp_start as ⟨#Hsto, HStorage, #Hlg⟩
  ihave #Hsto2 : isStorage st $$ [Hsto]
  · iexact Hsto
  iNamed Hsto
  subst Hstok
  icases Hbounded $$ HStorage with ⟨%Hbnd, HStorage⟩
  wp_auto
  wp_apply HFirstIndex $$ HStorage as %fi ⟨%Hfi, HStorage⟩
  wp_apply HLastIndex $$ [$HStorage] as %li ⟨%Hli, HStorage⟩
  · ipureintro; exact Hpe
  -- (raft#139) the last stored entry's term
  wp_apply HTerm $$ %σ %li [$HStorage] as %t ⟨%Ht, HStorage⟩
  · iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    intro e0 He0; rw [Hpe] at He0; cases He0
  have Hlast : t = (plogLast σ.prev σ.ents).term' := by
    have H1 := plogTermAt_last σ.prev σ.ents Hidx
    have H2 := plogLast_index σ.prev σ.ents Hidx
    have Hli' : (plogLast σ.prev σ.ents).index' = li := by
      apply uint_Z_inj.1; rw [H2]; unfold plogLastIndexZ; omega
    rw [Hli'] at H1
    have H3 : plogTermAt σ.prev σ.ents li = termAt σ.prev σ.ents li := by
      unfold plogTermAt termAt
      rw [if_neg (by omega)]
      try (split <;> simp_all)
    rw [H3, Ht] at H1
    exact Option.some.inj H1
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
    iframe Hl Hsto2 HStorage
    isplitr
    · ipureintro; apply BitVec.eq_of_toNat_eq; word
    isplitr
    · ipureintro; apply BitVec.eq_of_toNat_eq; word
    isplitr
    · ipureintro; exact Hlast
    isplitr
    · ipureintro; apply BitVec.eq_of_toNat_eq; word
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact Hidx
    isplitr
    · ipureintro; simp only [List.length_nil]; word
    isplitr
    · ipureintro; exact ⟨rfl, List.prefix_refl _, fun _ => rfl⟩
    isplitr
    · iapply (ownSnap_None _).2; ipureintro; rfl
    isplitr
    · ipureintro; exact initKsn_mem σ
    isplitr
    · iapply pendKsn_none
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
    ipureintro; exact ⟨Hpe, fun _ e0 He0 => by simp at He0⟩
  · ipureintro; word

end proof

end EtcdGrove
end Perennial
