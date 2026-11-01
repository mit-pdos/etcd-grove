/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__replica.lean`. Lean-first
(no Rocq counterpart).

Under `c.mu`, `c.replicas[id]`: a replica's `isRep` from the lock; `nil` for an id not in the map,
which is not a started one (`repKnown`'s bound against the lock's `γ.r.nid` authority: the map's keys
are `1 … nextID-1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__replica
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.replica.wp_proof : Cluster.replica.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c id known
  wp_start as ⟨Hc, Hk⟩
  iunfold isClusterC at Hc
  iNamed Hc
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold clusterLockInv at HL
  iNamed HL
  ihave #Hreps' := Hreps
  try wp_auto
  wp_apply wp_map_lookup1 go.uint64 _ mR R id (DFrac.own 1) $$ HR as HR
  ihave Hk : iprop(⌜known = true → id ≠ W64 0 ∧ uint.nat id + 1 ≤ uint.nat nid⌝ ∗
      monoNatAuthOwn γ.r.nid 1 (uint.nat nid)) $$ [Hk HnidA]
  · cases known with
    | false => iframe HnidA; ipureintro; intro h; cases h
    | true =>
      simp only [↓reduceIte]
      iunfold repKnown at Hk
      icases Hk with ⟨%Hid0, #Hlb⟩
      ihave %Hle := monoNatLbOwn_valid $$ HnidA Hlb
      iframe HnidA
      ipureintro; intro _; exact ⟨Hid0, Hle.2⟩
  icases Hk with ⟨%Hkn, HnidA⟩
  -- the answer, while the lock's `γ.r.nid` authority is at hand
  ihave Hans : iprop(⌜(R !! id).getD null = null ∧ known = false⌝ ∨
      isRep γ vs dir id ((R !! id).getD null)) $$ []
  · cases HRid : R !! id with
    | some r =>
      iright
      simp only [Option.getD_some]
      iapply BigSepM.bigSepM_lookup (Φ := fun id r => isRep (GF := GF) γ vs dir id r) HRid $$ Hreps'
    | none =>
      ileft
      simp only [Option.getD_none]
      ipureintro
      refine ⟨by simp, ?_⟩
      cases known with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨Hid0, Hle⟩ := Hkn rfl
        have := (Hdom.1 id).2 ⟨by word, by omega⟩
        rw [HRid] at this
        exact absurd this (by simp)
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hfiles]
  · inext
    unfold clusterLockInv
    iexists mR, R, nid, nop, U
    iframe
    iframe Hreps'
    ipureintro; exact Hdom
  try wp_auto
  iapply HΦ
  iexact Hans

end proof

end kvdurable
end EtcdGrove
end Perennial
