/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeEnum.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeEnum
public import RaftNoAx.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint

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

theorem raftpb.consumeEnum.wp_proof
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.consumeEnum.spec (GF := GF) (hG := hG) := by
  intro b dq bs i Hi0 Hilen
  wp_start as Hb
  wp_auto
  wp_apply wp_consumeVarint b dq bs i Hi0 Hilen $$ [$Hb] as %v %j %ok ⟨Hb, %Hr⟩
  have hE : ccEnumL bs (sint.nat i) = match ccVarintL bs (sint.nat i) with
      | none => none
      | some (v, j) => if 2 ^ 31 ≤ uint.Z v ∧ uint.Z v < 0xffffffff80000000 then none
        else some (W32 (uint.Z v), j) := rfl
  have h1 : uint.Z (W64 2147483648) = 2 ^ 31 := rfl
  have h2 : uint.Z (W64 18446744071562067968) = 0xffffffff80000000 := rfl
  cases hv : ccVarintL bs (sint.nat i) with
  | none =>
    rw [hv] at Hr hE
    subst Hr
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    rw [hE]
  | some p =>
    rw [hv] at Hr hE
    obtain ⟨v', j'⟩ := p
    simp only at hE Hr
    obtain ⟨rfl, rfl, hj⟩ := Hr
    (try wp_auto)
    wp_if_destruct
    · wp_if_destruct
      · (try wp_auto)
        iapply HΦ
        iframe
        ipureintro
        rw [hE, ite_eq_left ⟨by omega, by omega⟩]
      · (try wp_auto)
        iapply HΦ
        iframe
        ipureintro
        rw [hE, ite_eq_right (by omega)]
        exact ⟨rfl, rfl, hj⟩
    · (try wp_auto)
      iapply HΦ
      iframe
      ipureintro
      rw [hE, ite_eq_right (by omega)]
      exact ⟨rfl, rfl, hj⟩

end proof

end EtcdGrove
end Perennial
