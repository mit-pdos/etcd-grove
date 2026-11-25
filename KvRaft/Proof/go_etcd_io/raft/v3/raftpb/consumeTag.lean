-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/consumeTag.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeTag
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint

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

theorem raftpb.consumeTag.wp_proof
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.consumeTag.spec (GF := GF) (hG := hG) := by
  intro b dq bs i Hi0 Hilen
  wp_start as Hb
  wp_auto
  wp_apply wp_consumeVarint b dq bs i Hi0 Hilen $$ [$Hb] as %v %j %ok ⟨Hb, %Hr⟩
  cases hv : ccVarintL bs (sint.nat i) with
  | none =>
    rw [hv] at Hr
    subst Hr
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    simp [ccTagL, hv]
  | some p =>
    obtain ⟨v', j'⟩ := p
    rw [hv] at Hr
    obtain ⟨rfl, rfl, hj⟩ := Hr
    have hs : uint.Z (v >>> W64 3) = ((uint.nat v / 8 : Nat) : Int) := by
      change ((v >>> W64 3).toNat : Int) = _
      rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rfl
    have h1 : uint.Z (W64 1) = 1 := rfl
    have hmax : uint.Z (W64 536870911) = 536870911 := rfl
    wp_auto
    wp_if_destruct
    · wp_if_destruct
      · iapply HΦ
        iframe
        ipureintro
        simp [ccTagL, hv, show 1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^29 - 1 by omega, hj]
      · iapply HΦ
        iframe
        ipureintro
        simp [ccTagL, hv, show ¬ (1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^29 - 1) by omega]
    · iapply HΦ
      iframe
      ipureintro
      simp [ccTagL, hv, show ¬ (1 ≤ uint.nat v / 8 ∧ uint.nat v / 8 ≤ 2^29 - 1) by omega]

end proof

end EtcdGrove
end Perennial
