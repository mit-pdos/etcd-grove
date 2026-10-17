/-
Proof of `Spec/.../mvcc/hashByRevKeep.lean` (pr-verify/etcd-22515). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashByRevKeep
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Keep

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.hashByRevKeep.wp_proof
    (hKeep : mvcc.treeIndex.Keep.spec (GF := GF) (hG := hG)) :
    mvcc.hashByRevKeep.spec (GF := GF) (hG := hG) := by
  intro ti γ kn rev crev q c
  wp_start as ⟨#Hti, Hrd, Hkn, Hcu, %Hpre⟩
  obtain ⟨hc0, hcc, hcr, hr0, hrl⟩ := Hpre
  -- (`wp_auto` does not take the first allocation here, as in `kvHashIncludes`: done by hand)
  wp_bind (GoInstruction (GoAlloc _) _)
  wp_alloc crev_ptr as Hcrev
  wp_auto
  wp_apply (hKeep ti γ kn rev q c) $$ [$Hti $Hrd $Hkn $Hcu] as %m ⟨Hrd, Hkn, Hcu, %A, Hm, %HA⟩
  · ipureintro; exact ⟨hc0, by omega, hr0, hrl⟩
  wp_apply wp_map_len_lt $$ Hm as ⟨Hm, %Hsz⟩
  have hsz : sint.Z (W64 (GMap.size A : Int)) = GMap.size A := by word
  have hemp : (∀ r, ¬ mvcc.keepRevOf kn.log rev r) ↔ GMap.size A = 0 := by
    have := mvcc.keptBy_size A
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos (GMap.size A) with h0 | hpos
      · exact h0
      obtain ⟨r, hr⟩ := this.1 hpos
      exact absurd ((mvcc.keptBy_keepOfIs HA r).1 hr) (h r)
    · intro h r hr
      have := this.2 ⟨r, (mvcc.keptBy_keepOfIs HA r).2 hr⟩
      omega
  have hz : sint.Z (W64 0) = 0 := by decide
  by_cases H0 : GMap.size A = 0
  · have : W64 (GMap.size A : Int) = W64 0 := by rw [H0]; rfl
    rw [this]
    wp_auto
    rw [hz]
    by_cases Hc : 0 < sint.Z crev
    · rw [decide_eq_true Hc]
      wp_auto
      wp_apply (hKeep ti γ kn crev q c) $$ [$Hti $Hrd $Hkn $Hcu] as %m' ⟨Hrd, Hkn, Hcu, %A', Hm', %HA'⟩
      · ipureintro; exact ⟨hc0, hcc, by omega, by omega⟩
      iapply HΦ
      iframe
      ipureintro
      exact ⟨by simp [hemp.2 H0, Hc] , by simpa using HA'⟩
    · rw [decide_eq_false Hc]
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      exact ⟨by simp [Hc], by simpa using HA⟩
  · have : decide (W64 (GMap.size A : Int) = W64 0) = false := by
      rw [decide_eq_false_iff_not]; intro h
      have := congrArg sint.Z h
      rw [hsz, hz] at this; omega
    rw [this]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    have hn : ¬ ∀ r, ¬ mvcc.keepRevOf kn.log rev r := fun h => H0 (hemp.1 h)
    exact ⟨by simp [hn], by simpa using HA⟩

end proof

end EtcdGrove
end Perennial
