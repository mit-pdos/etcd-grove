-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/skipScalar.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.skipScalar
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeField
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeVarint

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

theorem raftpb.skipScalar.wp_proof
    (wp_consumeField : raftpb.consumeField.spec (GF := GF) (hG := hG))
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.skipScalar.spec (GF := GF) (hG := hG) := by
  intro b dq bs i typ Hi Hlen
  wp_start as Hb
  ihave %Hsize := ownSlice_len $$ Hb
  have hsize : (bs.length : Int) = sint.Z b.len := by word
  have hdiff : sint.Z (b.len - i) = (bs.length : Int) - sint.Z i := by word
  have hiInt : 0 ≤ i.toInt := Hi
  have hiNat : ((sint.nat i : Nat) : Int) = i.toInt := by change (i.toInt.toNat : Int) = i.toInt; omega
  have hmax : (bs.length : Int) < 2^63 := by rw [hsize]; word
  wp_auto
  wp_if_destruct
  · wp_apply wp_consumeVarint b dq bs i Hi Hlen $$ [$Hb] as %v %j %ok ⟨Hb, %Hr⟩
    iapply HΦ
    iframe
    ipureintro
    cases hv : ccVarintL bs (sint.nat i) with
    | none => simpa [ccSkipScalar, hv] using Hr
    | some p =>
      rw [hv] at Hr
      simp only [show uint.nat (W64 0) = 0 from rfl, ccSkipScalar, hv, Option.map_some]
      exact ⟨Hr.1, Hr.2.2⟩
  · wp_if_destruct
    · wp_if_destruct
      · iapply HΦ
        iframe
        ipureintro
        have h : sint.nat i + 8 ≤ bs.length := by word
        simp [ccSkipScalar, h]
        have bound : i.toInt + 8 ≤ (bs.length : Int) := by omega
        rw [Int.bmod_eq_of_le] <;> omega
      · iapply HΦ
        iframe
        ipureintro
        have h : ¬ sint.nat i + 8 ≤ bs.length := by word
        simp [ccSkipScalar, h]
    · wp_if_destruct
      · wp_apply wp_consumeField b dq bs i Hi Hlen $$ [$Hb] as %v %j %ok Hr
        cases hv : ccFieldL bs (sint.nat i) with
        | none =>
          icases Hr with ⟨%Hok, Hb⟩
          iapply HΦ
          iframe
          ipureintro
          simpa [ccSkipScalar, hv] using Hok
        | some p =>
          icases Hr with ⟨%Hok, Hv, Hback⟩
          ihave Hb := Hback $$ Hv
          iapply HΦ
          iframe
          ipureintro
          simpa [ccSkipScalar, hv] using Hok
      · wp_if_destruct
        · wp_if_destruct
          · iapply HΦ
            iframe
            ipureintro
            have h : sint.nat i + 4 ≤ bs.length := by word
            simp [ccSkipScalar, h]
            have bound : i.toInt + 4 ≤ (bs.length : Int) := by omega
            rw [Int.bmod_eq_of_le] <;> omega
          · iapply HΦ
            iframe
            ipureintro
            have h : ¬ sint.nat i + 4 ≤ bs.length := by word
            simp [ccSkipScalar, h]
        · iapply HΦ
          iframe
          ipureintro
          have h0 : uint.nat typ ≠ 0 := by word
          have h1 : uint.nat typ ≠ 1 := by word
          have h2 : uint.nat typ ≠ 2 := by word
          have h5 : uint.nat typ ≠ 5 := by word
          simp [ccSkipScalar, h0, h1, h2, h5]

end proof

end EtcdGrove
end Perennial
