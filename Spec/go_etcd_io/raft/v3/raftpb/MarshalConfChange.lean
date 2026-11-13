/-
`MarshalConfChange` (`raftpb/confchange.go:35`). Port of the old spec to raft v3.7 (a
`ConfChangeI` holds a pointer; `proto.Marshal` instead of gogoproto's generated `Marshal`; stage
R1).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.raft.v3.PbContentOwn

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

/-- `MarshalConfChange(c)` for `c` holding `o` (`ownConfChangeI`: `nil`, a `*ConfChange` or a
`*ConfChangeV2`): the entry type `confChangeEntryType o`, a fresh slice of bytes carrying the change
(`MarshalsConfChange`: bytes that decode back to it; the `nil` slice for `nil`) and a `nil` error
(`proto.Marshal` does not fail on these messages, `proto.MarshalConfChange.spec`). (out_size C3,
P5; freeze-b2 m1) Over the content form (`ccPtsCCo`: `nil`, or the change at its content `cc`), with
the encoding's length bound (`ccLenMax cc`, under the premise keeping every length below `2^63`), what
sizes the entry `confChangeToMsg` builds. -/
abbrev raftpb.MarshalConfChange.spec : Prop :=
  ∀ (c : GoInterface) (oc : Option ConfChangeIC) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ccPtsCCo c dq oc }}
    (App (Val #(functions raftpb.MarshalConfChange [])) (Val #c))
  {{ (data : GoSlice) (bs : List w8),
      RET (PairV (PairV #(confChangeEntryType (oc.map ConfChangeIC.model)) #data) #interface.nil);
      ccPtsCCo c dq oc ∗ data ↦* bs ∗ ⌜MarshalsConfChange (oc.map ConfChangeIC.model) bs⌝ ∗
      ⌜∀ cc, oc = some cc → ccSize cc + 64 < 2 ^ 63 → bs.length ≤ ccLenMax cc⌝ }}

end spec

end EtcdGrove
end Perennial
