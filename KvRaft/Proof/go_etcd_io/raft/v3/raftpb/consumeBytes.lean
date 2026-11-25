-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/raftpb/consumeBytes.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeBytes.lean`: the part's own (raft without
hand-written axioms, `notes/raft-noax-codec.md`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeBytes
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.consumeField
public import KvRaft.Proof.go_etcd_io.raft.v3.raftpb.CloneLeaf

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

theorem raftpb.consumeBytes.wp_proof
    (wp_consumeField : raftpb.consumeField.spec (GF := GF) (hG := hG)) :
    raftpb.consumeBytes.spec (GF := GF) (hG := hG) := by
  intro b dq bs i Hi0 Hilen
  wp_start as Hb
  wp_auto
  wp_apply wp_consumeField b dq bs i Hi0 Hilen $$ [$Hb] as %v %j %ok Hr
  cases hv : ccFieldL bs (sint.nat i) with
  | none =>
    simp only
    icases Hr with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  | some p =>
    simp only
    icases Hr with ⟨%Hok, Hv, Hback⟩
    obtain ⟨rfl, hj⟩ := Hok
    wp_auto
    wp_apply wp_slice_literal_nonnull (l := ([] : List w8))
    isplitr
    · ipureintro; rfl
    iintro %lp %Hlp ⟨-, -⟩
    simp only [show go.arrayLiteralSize ([] : List keyed_element) = 0 from rfl]
    wp_auto
    wp_apply wp_append_nonnil lp Hlp v p.1 dq $$ [Hv] as %v' ⟨Hv', Hv, -⟩
    · iexact Hv
    iapply HΦ
    ihave Hb := Hback $$ Hv
    iframe
    ipureintro
    exact ⟨rfl, hj⟩

end proof

end EtcdGrove
end Perennial
