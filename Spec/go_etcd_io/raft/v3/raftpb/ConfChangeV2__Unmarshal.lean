/-
`(*raftpb.ConfChangeV2).Unmarshal` (`raft.pb.go:3169`, gogoproto; names-only): the trust
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

/-- **Trust boundary** (gogoproto's generated decoder, not translated). `p.Unmarshal(d)` into a
zero `ConfChangeV2` computes `ccDecodeV2` (which names what it does): on bytes it decodes it
returns `nil` and `*p` holds the content, its `Changes` and `Context` fresh slices; on any
other bytes it returns a non-`nil` error, leaving `*p` some value. It never panics, and never
retains `d`.

Read against `raft.pb.go`: the decoder checks every index against `len(dAtA)` before reading
(`io.ErrUnexpectedEOF`), every varint's length (`ErrIntOverflowRaft`) and every length
prefix's sign (`ErrInvalidLengthRaft`), and returns an error (`fmt.Errorf`) on a bad tag or wire
type; unknown fields are skipped by `skipRaft`, with the same checks. Each change is appended
(`append(m.Changes, ConfChangeSingle{})`, onto `nil`) and decoded by
`ConfChangeSingle.Unmarshal` from its sub-slice, with the same checks; `Context` is copied out
(`append(m.Context[:0], ...)`, onto `nil`). The decoder does *not* reset `*p` first (it
merges), so the spec asks for a zero `*p`: then the result is a function of the bytes. -/
abbrev raftpb.ConfChangeV2.Unmarshal.spec : Prop :=
  ∀ (p : Loc) (d : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      p ↦ (zero_val raftpb.ConfChangeV2) ∗ d ↦*{dq} bs }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"Unmarshal")) (Val #d))
  {{ (err : GoInterface), RET #err;
      d ↦*{dq} bs ∗ ∃ v : raftpb.ConfChangeV2, p ↦ v ∗
        match ccDecodeV2 bs with
        | some m => ⌜err = interface.nil⌝ ∗ ownCCV2 v (DFrac.own 1) m
        | none => ⌜err ≠ interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
