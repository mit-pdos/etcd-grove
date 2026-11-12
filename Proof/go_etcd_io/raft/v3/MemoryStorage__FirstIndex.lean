/-
Port of election_proof/proof_MemoryStorage__FirstIndex.v. U8 v2 step 3 (2026-10-29): over the lock's
invariant; the caller's compaction bound is below the compaction point (`Hcp`), which is
justified (`Hcj`).
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__firstIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.FirstIndex.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG) := by
  intro ms γs c
  wp_start as ⟨#Hlock, #Hc⟩
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the caller's bound is at most the compaction point
  ihave %Hcle : ⌜c ≤ uint.nat p.index'⌝ $$ [Hcp_inv]
  · iunfold memCompacted at Hc
    icases Hc with (%H | ⟨#Hlb, -⟩)
    · ipureintro; omega
    icases monoNatLbOwn_valid _ _ _ _ $$ Hcp_inv Hlb with ⟨-, %H⟩
    ipureintro; exact H
  -- the compaction point itself is compacted
  ihave #Hcomp : memCompacted γs (uint.nat p.index') $$ [Hcp_inv]
  · ihave #Hlb := monoNatLbOwn_get _ _ _ $$ Hcp_inv
    iunfold memCompJust at Hcj_inv
    icases Hcj_inv with ⟨%L, #HL, %HcL⟩
    iunfold memCompacted
    iright
    iframe Hlb
    iexists L
    iframe HL
    ipureintro; exact ⟨_, HcL, Nat.le_refl _⟩
  have Hb := Hok_inv.1
  have Hpb : uint.Z (memPhys p ents).prev.index' + ((memPhys p ents).ents.length : Int) < 2^61 := by
    simp only [memPhys]; word
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  ihave Hf : memstorageFields ms (memPhys p ents) $$ [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, _, _, _, _, _
    simp only [named]
    iframe
    ipureintro; exact Hdummy
  wp_apply wp_MemoryStorage_firstIndex _ _ Hpb $$ [$Hf] as %fi ⟨%Hfi, Hfields_inv⟩
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hfields_inv Hlog_inv Hen_inv Hcp_inv Hsx_inv Hsl_inv Hlk_inv]
  · unfold memstorageInv
    iexists p, ents, M, sv
    simp only [named]
    iframe # ∗
    ipureintro; exact Hok_inv
  iapply HΦ
  simp only [memPhys] at Hfi
  have Hfi' : uint.nat fi = uint.nat p.index' + 1 := by word
  isplitl []
  · ipureintro; omega
  rw [Hfi', Nat.add_sub_cancel]
  iexact Hcomp

end proof

end EtcdGrove
end Perennial
