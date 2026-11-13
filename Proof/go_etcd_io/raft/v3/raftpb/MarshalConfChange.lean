/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/MarshalConfChange.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MarshalConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV1
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV1
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
public import Spec.google_golang_org.protobuf.proto.MarshalConfChange
public import Spec.google_golang_org.protobuf.proto.MarshalConfChangeV2

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

theorem raftpb.MarshalConfChange.wp_proof
    (wp_ConfChange_AsV1 : raftpb.ConfChange.AsV1.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV1 : raftpb.ConfChangeV2.AsV1.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_proto_MarshalConfChange : proto.MarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_proto_MarshalConfChangeV2 : proto.MarshalConfChangeV2.spec (GF := GF) (hG := hG)) :
    raftpb.MarshalConfChange.spec (GF := GF) (hG := hG) := by
  intro c oc dq
  wp_start as Hc
  rcases oc with _ | (⟨m, uf⟩ | ⟨t, chs, ctx, uf⟩)
  · simp only [ccPtsCCo, Option.map_none, confChangeEntryType]
    icases Hc with %Hc
    subst Hc
    wp_auto
    simp only [raftpb.EntryConfChangeV2]
    wp_auto
    ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    iapply HΦ $$ %slice.nil %([] : List w8)
    iframe
    isplitr
    · ipureintro; rfl
    ipureintro; intro cc h; cases h
  · simp only [ccPtsCCo, Option.map_some, ConfChangeIC.model, confChangeEntryType]
    iunfold ccPtsCC at Hc
    icases Hc with ⟨%v, %pt, %pn, %pi, %cs, %Hc, Hrest⟩
    obtain ⟨Hc, Hnn⟩ := Hc
    subst Hc
    wp_auto
    wp_apply wp_ConfChange_AsV1
    simp only [raftpb.EntryConfChange]
    wp_auto
    ihave Hcc : ccPtsCC (GF := GF) (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #v) dq
        (.v1 m uf) $$ [Hrest]
    · simp only [ccPtsCC]
      iexists v, pt, pn, pi, cs
      isplitr
      · ipureintro; exact ⟨rfl, Hnn⟩
      iexact Hrest
    wp_apply wp_proto_MarshalConfChange v dq m uf $$ [$Hcc] as %sl %bs ⟨Hcc, Hsl, %Hdec⟩
    iapply HΦ $$ %sl %bs
    iframe
    isplitr
    · ipureintro; exact Hdec.1
    ipureintro; intro cc h; cases h; exact Hdec.2
  · simp only [ccPtsCCo, Option.map_some, ConfChangeIC.model, confChangeEntryType]
    iunfold ccPtsCC at Hc
    icases Hc with ⟨%v, %pt, %sc, %ls, %cs, %Hc, Hrest⟩
    obtain ⟨Hc, Hnn⟩ := Hc
    subst Hc
    wp_auto
    wp_apply wp_ConfChangeV2_AsV1
    wp_apply wp_ConfChangeV2_AsV2
    simp only [raftpb.EntryConfChangeV2]
    wp_auto
    ihave Hcc : ccPtsCC (GF := GF) (interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #v) dq
        (.v2 t chs ctx uf) $$ [Hrest]
    · simp only [ccPtsCC]
      iexists v, pt, sc, ls, cs
      isplitr
      · ipureintro; exact ⟨rfl, Hnn⟩
      iexact Hrest
    wp_apply wp_proto_MarshalConfChangeV2 v dq t chs ctx uf $$ [$Hcc] as %sl %bs ⟨Hcc, Hsl, %Hdec⟩
    iapply HΦ $$ %sl %bs
    iframe
    isplitr
    · ipureintro; exact Hdec.1
    ipureintro; intro cc h; cases h; exact Hdec.2

end proof

end EtcdGrove
end Perennial
