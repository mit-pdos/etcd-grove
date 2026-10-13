/-
`(*raftpb.ConfChange).Marshal` (`raft.pb.go:1397`, gogoproto; names-only): the trust
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
fresh byte slice and a `nil` error, and the bytes decode back to the change (`ccDecodeV1`:
what `Unmarshal` makes of them, `ConfChange__Unmarshal.lean`).

Read against `raft.pb.go`: `Marshal` allocates `Size()` bytes and fills them with
`MarshalToSizedBuffer`, which never fails (its error is always `nil`, so is `Marshal`'s); it
reads `*p` and `Context`'s bytes and writes neither. It writes `ID`, `Type`, `NodeID` always
(non-nullable proto2 fields) and `Context` when non-`nil`; `Unmarshal` into a zero
`ConfChange` reads each back (an `int32` enum written as its sign-extended varint is read back
truncated to 32 bits, the same value), so the round trip holds for the content (a `nil` and an
empty `Context` are both `[]` in `CCV1M`). No pure encoder is claimed: the bytes depend on
`Context`'s `nil`-ness, which `CCV1M` forgets. -/
abbrev raftpb.ConfChange.Marshal.spec : Prop :=
  ∀ (p : Loc) (v : raftpb.ConfChange) (m : CCV1M) (dq dqc : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      p ↦{dq} v ∗ ownCCV1 v dqc m }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"Marshal")) (Val #()))
  {{ (sl : GoSlice) (bs : List w8), RET (PairV #sl #interface.nil);
      p ↦{dq} v ∗ ownCCV1 v dqc m ∗ sl ↦* bs ∗ ⌜ccDecodeV1 bs = some m⌝ }}

end spec

end EtcdGrove
end Perennial
