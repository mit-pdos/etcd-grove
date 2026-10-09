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
  intro st lg maxSize prev ents ss lok Hidx Hnocc Hss Hlg Hmax
  subst Hlg
  wp_start as ⟨#Hsto, HStorage, #Hlg⟩
  ihave #Hsto2 : isStorage st $$ [Hsto]
  · iexact Hsto
  iNamed Hsto
  subst Hstok
  icases Hbounded $$ HStorage with ⟨%Hbnd, HStorage⟩
  wp_auto
  wp_apply HFirstIndex $$ HStorage as %fi ⟨%Hfi, HStorage⟩
  wp_apply HLastIndex $$ HStorage as %li ⟨%Hli, HStorage⟩
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  iframe Hl
  isplitr
  · ipureintro
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;> first | (simp only []; apply BitVec.eq_of_toNat_eq; word) | (simp only []; word)
  unfold ownRaftLogCore
  iexists prev, ents, ss
  simp only [named, List.append_nil]
  iframe Hsto2 HStorage
  isplitr
  · ipureintro; exact Hidx
  isplitr
  · ipureintro; simp only [List.length_nil]; word
  isplitr
  · ipureintro; exact ⟨rfl, List.prefix_refl _, fun _ => rfl⟩
  isplitr
  · iapply (ownSnap_None _).2; ipureintro; rfl
  isplitr
  · ipureintro; word
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  isplitr
  · ipureintro; exact Hnocc
  isplitr
  · ipureintro; constructor <;> word
  isplitr
  · ipureintro; intro _; word
  isplitr
  · ipureintro; word
  isplitr
  · ipureintro; intro _
    rcases Hss with Hss | rfl
    · exact .inl Hss
    · exact .inr ⟨by word, plogTermAt_base _ _⟩
  isplitr
  · unfold isLoggerVal; iexists lok; iframe Hlg; ipureintro; rfl
  isplitr
  · unfold isLoggerVal; iexists lok; iframe Hlg; ipureintro; rfl
  isplitr
  · ipureintro; simp only [List.length_nil]; word
  isplitr
  · ipureintro; intro _
    refine ⟨?_, ?_, fun _ => rfl⟩
    · simp [storApp]
    · intro _; simp [storApp]
  isplitr
  · ipureintro; word
  ipureintro; intro _; word

end proof

end EtcdGrove
end Perennial
