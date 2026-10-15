/-
`confChangeToMsg` (`node.go:482`): the proposal of a conf change. Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.

`RawNode.ProposeConfChange` and `node.ProposeConfChange` step this message (since
2026-10-13, reconfiguration stage D, when the log took conf-change entries; see
`notes/STATUS.md`, "Reconfiguration, stage D").
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `confChangeToMsg(c)` for `c` holding `o`: a `MsgProp` (`ccPropMsg`) whose one entry is
`ccEntry o data` (the entry type of `o` and a fresh slice of bytes carrying it, as
`MarshalConfChange` returns them), and a `nil` error. -/
abbrev confChangeToMsg.spec : Prop :=
  ∀ (c : GoInterface) (o : Option CCMsg) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownCCI c dq o }}
    (App (Val #(functions confChangeToMsg [])) (Val #c))
  {{ (ents data : GoSlice) (bs : List w8), RET (PairV #(ccPropMsg ents) #interface.nil);
      ownCCI c dq o ∗ ents ↦* [ccEntry o data] ∗
      -- (2026-10-13) the fresh slice's capacity, which `raft.Step` takes
      ownSliceCap raftpb.Entry ents (DFrac.own 1) ∗
      data ↦* bs ∗ ⌜CCData o bs⌝ }}

end spec

end EtcdGrove
end Perennial
