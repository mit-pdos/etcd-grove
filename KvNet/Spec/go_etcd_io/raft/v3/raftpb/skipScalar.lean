-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/skipScalar.lean` (etc/copy-part.py; rerun it, do not edit).
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

/-- Skip a scalar protobuf field and return its ending position. -/
abbrev raftpb.skipScalar.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i typ : w64),
  0 ≤ sint.Z i → sint.Z i ≤ bs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ b ↦*{dq} bs }}
    (App (App (App (Val #(functions raftpb.skipScalar [])) (Val #b)) (Val #i)) (Val #typ))
  {{ (j : w64) (ok : Bool), RET (PairV #j #ok); b ↦*{dq} bs ∗
      ⌜match ccSkipScalar bs (sint.nat i) (uint.nat typ) with
       | some p => ok = true ∧ sint.Z j = p
       | none => ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
