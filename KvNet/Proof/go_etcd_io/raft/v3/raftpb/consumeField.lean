-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/consumeField.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeField.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

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

theorem raftpb.consumeField.wp_proof
    (wp_consumeVarint : raftpb.consumeVarint.spec (GF := GF) (hG := hG)) :
    raftpb.consumeField.spec (GF := GF) (hG := hG) := by
  intro b dq bs i Hi0 Hilen
  wp_start as Hb
  ihave %Hlen := ownSlice_len $$ Hb
  ihave %Hwf := ownSlice_wf $$ Hb
  wp_auto
  wp_apply wp_consumeVarint b dq bs i Hi0 Hilen $$ [$Hb] as %v %j %ok ⟨Hb, %Hr⟩
  have hF : ccFieldL bs (sint.nat i) = match ccVarintL bs (sint.nat i) with
      | none => none
      | some (l, j) => if (bs.length : Int) - j < uint.Z l then none
        else some ((bs.drop j).take (uint.nat l), j + uint.nat l) := rfl
  cases hv : ccVarintL bs (sint.nat i) with
  | none =>
    rw [hv] at Hr hF
    subst Hr
    wp_auto
    iapply HΦ
    rw [hF]
    simp only
    iframe
  | some p =>
    rw [hv] at Hr hF
    obtain ⟨l, j'⟩ := p
    simp only at hF Hr
    obtain ⟨rfl, rfl, hj⟩ := Hr
    have hb := ccVarintL_bound hv
    wp_auto
    have hjz : sint.Z j = (j' : Int) := hj
    have hd : uint.Z (b.len - j) = (bs.length : Int) - j' := by word
    have hvn : (uint.nat v : Int) = uint.Z v := by word
    wp_if_destruct
    · iapply HΦ
      rw [hF, ite_eq_left (by omega)]
      simp only
      iframe
    · have hk : sint.Z (j + v) = (j' : Int) + uint.Z v := by word
      have hlenZ : sint.Z b.len = (bs.length : Int) := by word
      have e1 : sint.nat j = j' := by word
      have e2 : sint.nat (j + v) = j' + uint.nat v := by word
      have Hrng : 0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z (j + v) ∧ sint.Z (j + v) ≤ sint.Z b.len := by
        omega
      rw [ite_eq_left ⟨Hrng.1, Hrng.2.1, by omega⟩]
      wp_auto
      icases (ownSlice_slice j (j + v) b dq bs Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
      have hsub : subslice (sint.nat j) (sint.nat (j + v)) bs = (bs.drop j').take (uint.nat v) := by
        rw [e1, e2]
        simp only [subslice, List.drop_take]
        congr 1; omega
      iapply HΦ
      rw [hF, ite_eq_right (by omega)]
      simp only
      rw [← hsub]
      iframe
      isplitr
      · ipureintro; exact ⟨trivial, by omega⟩
      iintro Hb2
      iapply (ownSlice_slice j (j + v) b dq bs Hrng).2
      iframe

end proof

end EtcdGrove
end Perennial
