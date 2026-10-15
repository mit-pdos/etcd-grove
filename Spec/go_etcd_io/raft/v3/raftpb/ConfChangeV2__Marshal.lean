/-
`(*raftpb.ConfChangeV2).Marshal` (`raft.pb.go:1465`, gogoproto; names-only): the trust
boundary. Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.
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

/-- **Trust boundary** (gogoproto's generated encoder, not translated). `p.Marshal()` returns a
fresh byte slice and a `nil` error, and the bytes decode back to the change (`ccDecodeV2`:
what `Unmarshal` makes of them, `ConfChangeV2__Unmarshal.lean`).

Read against `raft.pb.go`: `Marshal` allocates `Size()` bytes and fills them with
`MarshalToSizedBuffer`, which never fails (its error is always `nil`, so is `Marshal`'s, and
so are the per-change `ConfChangeSingle.MarshalToSizedBuffer`s'); it reads `*p`, the elements
of `Changes` and `Context`'s bytes, and writes none of them. It writes `Transition` always
(non-nullable), each change as an embedded message (`Type`, `NodeID`, both always), in order,
and `Context` when non-`nil`; `Unmarshal` into a zero `ConfChangeV2` reads each back, appending
the changes in order (an `int32` enum written as its sign-extended varint is read back
truncated to 32 bits, the same value), so the round trip holds for the content (a `nil` and an
empty `Context`, or `Changes`, are both `[]` in `CCV2M`). No pure encoder is claimed: the
bytes depend on `Context`'s `nil`-ness, which `CCV2M` forgets. -/
abbrev raftpb.ConfChangeV2.Marshal.spec : Prop :=
  ∀ (p : Loc) (v : raftpb.ConfChangeV2) (m : CCV2M) (dq dqc : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      p ↦{dq} v ∗ ownCCV2 v dqc m }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"Marshal")) (Val #()))
  {{ (sl : GoSlice) (bs : List w8), RET (PairV #sl #interface.nil);
      p ↦{dq} v ∗ ownCCV2 v dqc m ∗ sl ↦* bs ∗ ⌜ccDecodeV2 bs = some m⌝ }}

end spec

end EtcdGrove
end Perennial
