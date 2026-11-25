-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/consumeEnum.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.consumeEnum` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-codec.md`). A helper of the conf change codecs.
-/
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

/-- `consumeEnum(b, i)` (`raftpb/noax.go`), at an index within `b`: `ccEnumL`'s answer, or `ok = false`. -/
abbrev raftpb.consumeEnum.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64),
  0 ≤ sint.Z i → sint.Z i ≤ bs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ b ↦*{dq} bs }}
    (App (App (Val #(functions raftpb.consumeEnum [])) (Val #b)) (Val #i))
  {{ (v : w32) (j : w64) (ok : Bool), RET (PairV (PairV #v #j) #ok); b ↦*{dq} bs ∗
      ⌜match ccEnumL bs (sint.nat i) with
       | some p => ok = true ∧ v = p.1 ∧ sint.Z j = p.2
       | none => ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
