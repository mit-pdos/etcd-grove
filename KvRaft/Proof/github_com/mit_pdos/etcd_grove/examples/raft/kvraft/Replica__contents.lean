/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/Replica__contents.lean`. Lean-first
(no Rocq counterpart). Under `mu` (released by the `defer`), the lock's half of the store's map
(`repShared`) is copied into a fresh map by the range loop, each value carried over with its bound
(`MapFits`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Replica__contents
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Replica.contents.wp_proof : Replica.contents.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r
  wp_start as #HisRep
  iunfold isRep at HisRep
  icases HisRep with ⟨%n, %st, %sts, %sq, %ρ, #HR⟩
  iunfold isReplicaR at HR
  iNamed HR
  ihave #Hrep' := Hrep
  iclear Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  try wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iNamed HL
  iNamed Hrep
  try wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %m0 HM
  try wp_auto
  try wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun _ (_ : Int) => iprop(∃ (v0 k0 : GoString) (M : GMap (List w8) (List w8)),
      "v" ∷ v_ptr ↦ v0 ∗ "k" ∷ k_ptr ↦ k0 ∗ "HM" ∷ m0 ↦$ M ∗ "m" ∷ m_ptr ↦ m0 ∗
      "%HMf" ∷ ⌜MapFits M⌝)) _ _ _ mK K (DFrac.own (1 : Qp).half) $$ HK
  iintro %keys %Hkeys
  isplitl [v k HM m]
  · iexists _, _, ∅
    iframe
    ipureintro; intro k v h; simp at h
  isplitr
  · imodintro
    iintro %i %key %val ⟨%Hki, %Hkv⟩ HP
    iNamed HP
    try wp_auto
    wp_apply wp_mapInsert go.string m0 M key val $$ [$HM] as HM
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists _, _, _
    iframe
    ipureintro; exact HMf.insert key val (HKsfit key val Hkv)
  iintro HP HK
  iNamed HP
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmW HW Hwaiters HmR HRd Hreads HmA HA Hcs Hidx
    HmK HK]
  · inext
    unfold lockInv
    iexists mW, W, mR, Rd
    iframe
    unfold repShared
    iexists mA, A, csp, c, idx, ap, mK, K
    iframe
    iframe HcsO Hap
    ipureintro; exact ⟨HA, HAfit, HKsfit⟩
  try wp_auto
  iapply HΦ
  iexists M, c
  iframe HM HcsO
  ipureintro; exact HMf

end proof

end kvraft
end EtcdGrove
end Perennial
