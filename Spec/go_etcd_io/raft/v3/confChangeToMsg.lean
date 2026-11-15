/-
`confChangeToMsg` (`node.go:482`): the proposal of a conf change. Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.

`RawNode.ProposeConfChange` and `node.ProposeConfChange` step this message (since
2026-10-13, reconfiguration stage D, when the log took conf-change entries; see
`notes/STATUS.md`, "Reconfiguration, stage D").

raft v3.7 (2026-10-16, stage R5; `notes/decisions.md`, "The node layer over pointer messages"):
the message is a fresh `*pb.Message` (`&pb.Message{Type: MsgProp.Enum(), Entries:
[]*pb.Entry{{Type: typ.Enum(), Data: data}}}`), returned owned as `raft.Step` takes a proposal
(`msgIn ml 1`: the struct and the entries' slots at `1`), its record `propMsgM` with the one
entry `ccEntryM o bs` (D6: the entry holds the bytes `MarshalConfChange` returned, frozen;
until then the Goose value `ccPropMsg ents` with the slices `ents`, `data` and the capacity
apart).
-/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.MsgOwnZ

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

/-- `confChangeToMsg(c)` for `c` holding `o`: a `MsgProp` (`propMsgM`) whose one entry is
`ccEntryM o bs` (the entry type of `o` and the bytes carrying it, as `MarshalConfChange`
returns them), and a `nil` error. (2026-10-16, stage R5: the message at `ml`, `msgIn ml 1`.)
(out_size C3, P5) The change at its optional content `oc` (`ccPtsCCo`), and the message at a content
(`msgInC sz`, as `raft.Step` takes it), of bounded size under the flag `sz` when the change's size
measure leaves room for the encoding's framing (`ccSize cc + 64 ≤ entBytesMax`). -/
abbrev confChangeToMsg.spec : Prop :=
  ∀ (c : GoInterface) (oc : Option ConfChangeIC) (dq : DFrac) (sz : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ccPtsCCo c dq oc ∗
      ⌜sz = true → ∀ cc, oc = some cc → ccSize cc + 64 ≤ entBytesMax⌝ }}
    (App (Val #(functions confChangeToMsg [])) (Val #c))
  {{ (ml : Loc) (bs : List w8), RET (PairV #ml #interface.nil);
      ccPtsCCo c dq oc ∗
      msgInC sz ml (DFrac.own 1) ⟨propMsgM, [ccEntryM (oc.map ConfChangeIC.model) bs], none, [], []⟩ ∗
      ⌜MarshalsConfChange (oc.map ConfChangeIC.model) bs⌝ }}

end spec

end EtcdGrove
end Perennial
