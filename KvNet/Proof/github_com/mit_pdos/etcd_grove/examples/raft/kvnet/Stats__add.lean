/-
The proof of `KvNet/Spec/.../kvnet/Stats__add.lean`: lock, increment the counter (the array's
element, `array_acc`), unlock.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Stats.add.wp_proof : Stats.add.spec (GF := GF) (hG := hG) := by
  intro s i Hi0 Hi
  wp_start as #Hs
  unfold isStats
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hs] as ⟨Hlocked, HL⟩
  unfold statsInv
  icases HL with ⟨%a, Ha⟩
  try wp_auto
  rw [if_pos ⟨Hi0, Hi⟩]
  obtain ⟨vs⟩ := a
  ihave %Hlen := array_len _ _ _ _ $$ Ha
  have hlt : (sint.Z i).toNat < vs.length := by omega
  obtain ⟨v, hv⟩ : ∃ v, vs[(sint.Z i).toNat]? = some v := ⟨_, List.getElem?_eq_getElem hlt⟩
  icases array_acc (GF := GF) _ (sint.Z i) _ _ (array.mk 24 vs) v Hi0 hv $$ Ha with ⟨Hv, Ha⟩
  try simp only [show (0 ≤ sint.Z i ∧ sint.Z i < 24) = True from eq_true ⟨Hi0, Hi⟩, ite_true]
  try wp_auto
  try simp only [show (0 ≤ sint.Z i ∧ sint.Z i < 24) = True from eq_true ⟨Hi0, Hi⟩, ite_true]
  try wp_auto
  ihave Ha := Ha $$ Hv
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hs $Hlocked Ha]
  · inext; iexists _; iexact Ha
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
