-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeUnknown.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvPb
public import KvNet.Proof.go_etcd_io.raft.v3.PbContentOwn
public import KvNet.Proof.go_etcd_io.raft.v3.CCCodecLen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Collect a complete unknown field, retaining its value bytes verbatim and
writing the minimal tag. A decoding error leaves the field buffer untouched. -/
abbrev raftpb.consumeUnknown.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i tag : w64) (fields : GoSlice) (uf : List w8),
  0 ≤ sint.Z i → sint.Z i ≤ bs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ b ↦*{dq} bs ∗
      fields ↦* uf ∗ ownSliceCap w8 fields (DFrac.own 1) }}
    (App (App (App (App (Val #(functions raftpb.consumeUnknown [])) (Val #b)) (Val #i)) (Val #tag)) (Val #fields))
  {{ (out : GoSlice) (j : w64) (ok : Bool), RET (PairV (PairV #out #j) #ok);
      b ↦*{dq} bs ∗ ownSliceCap w8 out (DFrac.own 1) ∗
      match ccSkipField bs (sint.nat i) (uint.nat tag) with
      | some endIdx => ⌜ok = true ∧ sint.Z j = endIdx⌝ ∗
          out ↦* ((uf ++ ccVarint tag) ++ subslice (sint.nat i) endIdx bs)
      | none => ⌜ok = false ∧ out = fields ∧ j = i⌝ ∗ out ↦* uf }}

end spec

end EtcdGrove
end Perennial
