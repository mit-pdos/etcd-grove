/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChange__AsV2.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetNodeId

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.ConfChange.AsV2.wp_proof
    (wp_ConfChange_GetType : raftpb.ConfChange.GetType.spec (GF := GF) (hG := hG))
    (wp_ConfChangeType_Enum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG))
    (wp_ConfChange_GetNodeId : raftpb.ConfChange.GetNodeId.spec (GF := GF) (hG := hG)) :
    raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG) := by
  -- `int32` (`ConfChangeType`'s underlying type) is not an interface: Perennial states
  -- `NotInterface` per type constructor, and `go.int32` is a non-reducible definition.
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  intro c dq m
  wp_start as Hm
  iapply wp_fupd
  wp_auto
  wp_apply wp_ConfChange_GetType.1 $$ [Hm]
  · iframe
  iintro Hm
  wp_apply wp_ConfChangeType_Enum m.type
  iintro %pty Hpt
  wp_auto
  wp_apply wp_ConfChange_GetNodeId.1 $$ [Hm]
  · iframe
  iintro Hm
  set_option goose.wp.unfoldSliceLiterals true in
  wp_auto
  wp_alloc_auto
  set_option goose.wp.unfoldSliceLiterals true in
  wp_auto
  -- the fresh `*ConfChangeSingle` `q`, in the slice's backing array `tmp`
  rename_i q
  irename : (q ↦ ({ state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil, sizeCache' := 0 } : raftpb.ConfChangeSingle) : IProp GF) => Hq
  rw [show go.arrayLiteralSize _ = 1 from rfl]
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 1 - W64 0 = W64 1 from rfl]
  ihave Hsl := slice_array tmp_ptr 1 (array.mk 1 [q]) (by simp) $$ tmp
  iNamed Hm
  wp_auto
  wp_alloc_auto
  rename_i v
  irename : (v ↦ ({ state' := zeroValDef, Transition' := null, Changes' := slice.mk tmp_ptr (W64 1) (W64 1), Context' := cs, unknownFields' := slice.nil, sizeCache' := 0 } : raftpb.ConfChangeV2) : IProp GF) => Hv
  wp_auto
  -- freeze the fresh cells and objects
  imod cellRO_alloc _ _ $$ Hpt with #cty
  imod cellRO_alloc _ _ $$ «$v1» with #cnd
  imod ccsRO_of_struct q
    { state' := zeroValDef, Type' := pty, NodeId' := «$v1_ptr», unknownFields' := slice.nil,
      sizeCache' := 0 }
    (ConfChangeSingleM.mk m.type m.nodeId) ⊤ rfl $$ [Hq] with #Hccs
  · dsimp only
    iframe
    iframe cty cnd
  ihave #cnull := cellRO_null (GF := GF) (V := w32)
  imod ownCCV2_of_struct v
    { state' := zeroValDef, Transition' := null, Changes' := slice.mk tmp_ptr (W64 1) (W64 1),
      Context' := cs, unknownFields' := slice.nil, sizeCache' := 0 }
    m.asV2 [q] ⊤ rfl $$ [Hv Hsl] with Hv2
  · dsimp only
    iframe
    dsimp only [CCV1M.asV2]
    rw [show W32 0 = zero_val w32 from rfl]
    iframe cnull Hcs
    iapply BigSepL2.bigSepL2_singleton.2
    iexact Hccs
  imodintro
  iapply HΦ
  iframe
  iunfold ownCCV1
  iexists pt, pn, pi, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cT cN cI Hcs Hpb

end proof

end EtcdGrove
end Perennial
