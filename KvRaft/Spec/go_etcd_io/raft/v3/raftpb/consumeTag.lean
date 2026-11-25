-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeTag.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb
public import KvRaft.Proof.go_etcd_io.raft.v3.PbContentOwn
public import KvRaft.Proof.go_etcd_io.raft.v3.CCCodecLen

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

/-- Read a protobuf message field tag and check its field number. -/
abbrev raftpb.consumeTag.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64),
  0 ≤ sint.Z i → sint.Z i ≤ bs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ b ↦*{dq} bs }}
    (App (App (Val #(functions raftpb.consumeTag [])) (Val #b)) (Val #i))
  {{ (v j : w64) (ok : Bool), RET (PairV (PairV #v #j) #ok); b ↦*{dq} bs ∗
      ⌜match ccTagL bs (sint.nat i) (2^29 - 1) with
       | some p => ok = true ∧ uint.nat v = p.1 ∧ sint.Z j = p.2
       | none => ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
