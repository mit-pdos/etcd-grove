-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeBytes.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.consumeBytes` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-codec.md`). A helper of the conf change codecs.
-/
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

/-- `consumeBytes(b, i)` (`raftpb/noax.go`), at an index within `b`: `ccFieldL`'s answer, the value a fresh slice, or `ok = false`. -/
abbrev raftpb.consumeBytes.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64),
  0 ≤ sint.Z i → sint.Z i ≤ bs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ b ↦*{dq} bs }}
    (App (App (Val #(functions raftpb.consumeBytes [])) (Val #b)) (Val #i))
  {{ (v : GoSlice) (j : w64) (ok : Bool), RET (PairV (PairV #v #j) #ok); b ↦*{dq} bs ∗
      match ccFieldL bs (sint.nat i) with
      | some p => ⌜ok = true ∧ sint.Z j = p.2⌝ ∗ v ↦* p.1
      | none => ⌜ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
