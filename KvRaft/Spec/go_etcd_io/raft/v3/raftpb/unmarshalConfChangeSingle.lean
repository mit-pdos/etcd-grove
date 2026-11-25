-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/unmarshalConfChangeSingle.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.unmarshalConfChangeSingle` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
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

/-- `unmarshalConfChangeSingle(data)` (`raftpb/noax.go`): `ccWireSingle`'s answer, a fresh frozen change holding it (`ccsRO`) and `true`, or `false`. -/
abbrev raftpb.unmarshalConfChangeSingle.spec : Prop :=
  ∀ (d : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ d ↦*{dq} bs }}
    (App (Val #(functions raftpb.unmarshalConfChangeSingle [])) (Val #d))
  {{ (s : Loc) (ok : Bool), RET (PairV #s #ok); d ↦*{dq} bs ∗
      match ccWireSingle bs with
      | some c => ⌜ok = true⌝ ∗ ccsRO s c
      | none => ⌜ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
