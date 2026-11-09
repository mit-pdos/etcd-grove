/-
`MarshalConfChange(c)` (`raftpb/confchange.go:35`).

Users: raft's `node.ProposeConfChange` (`node.go:489`, R1: `confChangeToMsg`), `RawNode.
ProposeConfChange`, the leader's auto-leave proposal (`raft.appliedTo`, `MarshalConfChange(nil)`:
R2), etcd's `EtcdServer.configure` (through `ProposeConfChange`). Snippet:
`examples/specreq/raftpb/confchange.go` (`ReqMarshalDecode`, `ReqAutoLeave`).

Proof sketch: `nil`: the type `EntryConfChangeV2`, the `nil` slice, and `decodeConfChange_empty`.
A `*ConfChange` (`.v1 c`): `c.AsV1()` (`ConfChange.AsV1.spec`) gives the pointer; `confChangeV1Pts_
msgAt` gives `msgAt ConfChange.ty p dq ct` with `confChangeV1Is ct c` (plain, `marshalOk`, depth 1,
`encSize ct ≤ wireBound`), so `ct.fits` by the premise; `proto.Marshal` (2a's `Marshal.spec`) gives
fresh bytes `bs` with `encodes ConfChange.ty ct bs` and no error (`marshalOk`); `decodeConfChange
EntryConfChange bs` picks a content `ct'` with `encodes ... ct' bs ∧ confChangeV1Is ct' _`, which is
`ct` (`Proto.encodes_fun`), so it is `some (.v1 c)`; fold back with the relation law. A
`*ConfChangeV2`: `AsV1` answers `false`, `AsV2` returns the same pointer, and the same argument at
`ConfChangeV2.ty`.

Changes: from `specs-ref/Spec/go_etcd_io/raft/v3/raftpb/MarshalConfChange.lean`: the result decodes
through raftpb's wire model (`decodeConfChange`, defined from protobuf's `encodes`) instead of the
old `MarshalsConfChange` over the refuted `pbEnc`; the size premise is explicit (it was hidden in the
old `proto.MarshalConfChange.spec`, which took no premise: false of protobuf-go above `2 ^ 48`
bytes); `nil` is the same spec (`o = none`).

Margin: the code returns an error where `proto.Marshal` does, which never happens for raftpb
(`marshalOk`); the spec states the `nil` error.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `MarshalConfChange(v)` of `nil` (`none`) or of a change `c` whose encoding fits (`c.wireBound <
2 ^ 48`): the entry type, fresh bytes that decode back to the change (the `nil` slice, decoding to
the empty `ConfChangeV2`, for `nil`), and no error. -/
def MarshalConfChange.spec : Prop :=
  ∀ (v : GoInterface) (dq : DFrac) (o : Option ConfChangeI),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      match o with
      | none => ⌜v = GoInterface.nil⌝
      | some c => confChangePts v dq c ∗ ⌜c.wireBound < Proto.marshalMax⌝ }}
    (App (Val (@! go_etcd_io.raft.v3.raftpb.MarshalConfChange)) (Val #v))
  {{ (t : w32) (b : GoSlice), RET (PairV (PairV #t #b) #GoInterface.nil);
      (match o with
       | none => ⌜v = GoInterface.nil⌝
       | some c => confChangePts v dq c) ∗
      ∃ bs : List w8, b ↦* bs ∗
        ⌜t = (o.getD (.v2 ⟨ConfChangeTransitionAuto, [], []⟩)).entryType ∧
         decodeConfChange t bs = some (o.getD (.v2 ⟨ConfChangeTransitionAuto, [], []⟩))⌝ }}

end spec

end RaftPb
end EtcdGrove
end Perennial
