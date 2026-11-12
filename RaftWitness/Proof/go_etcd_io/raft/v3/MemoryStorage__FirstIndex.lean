/-
Port of election_proof/proof_MemoryStorage__FirstIndex.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.MemoryStorage__firstIndex

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

theorem MemoryStorage.FirstIndex.wp_proof
    (wp_MemoryStorage_firstIndex : MemoryStorage.firstIndex.spec (GF := GF) (hG := hG)) :
    MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG) := by
  intro ms γs σ
  wp_start as Hpre
  iNamed Hpre
  iunfold ownMemoryStorage at Hms
  iNamed Hms
  wp_auto
  wp_apply wp_with_defer as %defer defer
  -- `ms.Lock()`: the method of the embedded `sync.Mutex`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σ0, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the contents agree with the view on the boundary (2026-10-10); (D19i part 1) the fields are
  -- cut at `c`, the view's boundary or within the floor
  icases memCut_view γs σ σ0 c $$ Hview Hgs_inv Hcut_inv
    with ⟨%Hvc, #Hcutlb, Hview, Hgs_inv, Hcut_inv⟩
  obtain ⟨Hvw, Hcok, Hcfl⟩ := Hvc
  have Hpb' : uint.Z (memCut σ0 c).prev.index' + ((memCut σ0 c).ents.length : Int) < 2^61 := by
    have := memCut_stLast Hcok
    unfold EtcdGrove.stLast at this
    omega
  iNamed Hfields_inv
  wp_auto
  ihave Hf : memstorageFields ms (memCut σ0 c) $$ [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
  · unfold memstorageFields
    iexists hp, es, dummy, _, nli, nen, nte, nsn
    iframe
    ipureintro; exact Hdummy
  wp_apply wp_MemoryStorage_firstIndex ms (memCut σ0 c) Hpb' $$ [$Hf] as %fi ⟨%Hfi, Hf⟩
  -- the deferred `ms.Unlock()`
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv Hf Hcut_inv]
  · unfold memstorageInv
    iexists σ0, c
    iframe
    ipureintro; exact Hpb_inv
  iapply HΦ
  simp only [memCut] at Hfi
  obtain ⟨Hc1, -, -⟩ := Hcok
  rw [Hvw.1] at Hc1 Hcfl
  isplitr
  · ipureintro
    constructor
    · omega
    · rcases Hcfl with Hcfl | Hcfl
      · rw [Hcfl] at Hfi; omega
      · omega
  isplitr
  · by_cases Hce : uint.Z c.index' = uint.Z σ.prev.index'
    · ileft; ipureintro; omega
    · iright
      rw [show uint.Z fi - 1 = uint.Z c.index' by omega]
      iexact Hcutlb
  unfold ownMemoryStorage
  iframe # ∗
  ipureintro
  exact Hbounded

end proof

end EtcdGrove
end Perennial
