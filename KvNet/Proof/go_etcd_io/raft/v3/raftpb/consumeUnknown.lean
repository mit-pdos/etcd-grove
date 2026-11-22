-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/consumeUnknown.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.consumeUnknown
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.skipField
public import KvNet.Spec.go_etcd_io.raft.v3.raftpb.appendVarint
public import KvNet.Proof.go_etcd_io.raft.v3.CCCodecLemmas

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

theorem raftpb.consumeUnknown.wp_proof
    (wp_skip : raftpb.skipField.spec (GF := GF) (hG := hG))
    (wp_append : raftpb.appendVarint.spec (GF := GF) (hG := hG)) :
    raftpb.consumeUnknown.spec (GF := GF) (hG := hG) := by
  intro b dq bs i tag fields uf Hi Hlen
  wp_start as ⟨Hb, Hbuf, Hcap⟩
  ihave %Hsize := ownSlice_len $$ Hb
  ihave %Hwf := ownSlice_wf $$ Hb
  wp_auto
  wp_apply wp_skip b dq bs i tag Hi Hlen $$ [$Hb] as %j %ok ⟨Hb, %Hr⟩
  cases hs : ccSkipField bs (sint.nat i) (uint.nat tag) with
  | none =>
    rw [hs] at Hr
    subst Hr
    wp_auto
    iapply HΦ
    dsimp only
    iframe
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  | some endIdx =>
    rw [hs] at Hr
    obtain ⟨rfl, hj⟩ := Hr
    have he := ccSkipField_bound (show sint.nat i ≤ bs.length by word) hs
    have hiNat : (sint.nat i : Int) = sint.Z i := by word
    have hlenZ : (bs.length : Int) = sint.Z b.len := by word
    have hjNat : sint.nat j = endIdx := by word
    have hrange : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z b.len := by omega
    wp_auto
    wp_apply wp_append fields uf tag $$ [$Hbuf $Hcap] as %mid ⟨Hmid, Hcap⟩
    rw [ite_eq_left ⟨Hi, hrange.2.1, by omega⟩]
    wp_auto
    icases (ownSlice_slice i j b dq bs hrange).1 $$ Hb with ⟨Hlo, Hval, Hhi⟩
    wp_apply wp_slice_append $$ [$Hmid $Hcap $Hval] as %out ⟨Hout, Hcap, Hval⟩
    iapply HΦ
    iframe Hcap
    isplitl [Hlo Hval Hhi]
    · iapply (ownSlice_slice i j b dq bs hrange).2
      iframe
    rw [← hjNat]
    dsimp only
    iframe
    ipureintro; exact ⟨rfl, by omega⟩

end proof
end EtcdGrove
end Perennial
