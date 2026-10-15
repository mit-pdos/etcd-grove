/-
`(*raftpb.ConfChange).Unmarshal` (`raft.pb.go:2940`, gogoproto; names-only): the trust
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
zero `ConfChange` computes `ccDecodeV1` (which names what it does): on bytes it decodes it
returns `nil` and `*p` holds the content, its `Context` a fresh slice; on any other bytes it
returns a non-`nil` error, leaving `*p` some value. It never panics, and never retains `d`.

Read against `raft.pb.go`: the decoder checks every index against `len(dAtA)` before reading
(`io.ErrUnexpectedEOF`), every varint's length (`ErrIntOverflowRaft`) and every length
prefix's sign (`ErrInvalidLengthRaft`), and returns an error (`fmt.Errorf`) on a bad tag or wire
type; unknown fields are skipped by `skipRaft`, with the same checks. `Context` is copied out
(`append(m.Context[:0], ...)`, onto `nil`). The decoder does *not* reset `*p` first (it
merges), so the spec asks for a zero `*p`: then the result is a function of the bytes. -/
abbrev raftpb.ConfChange.Unmarshal.spec : Prop :=
  ∀ (p : Loc) (d : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      p ↦ (zero_val raftpb.ConfChange) ∗ d ↦*{dq} bs }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"Unmarshal")) (Val #d))
  {{ (err : GoInterface), RET #err;
      d ↦*{dq} bs ∗ ∃ v : raftpb.ConfChange, p ↦ v ∗
        match ccDecodeV1 bs with
        | some m => ⌜err = interface.nil⌝ ∗ ownCCV1 v (DFrac.own 1) m
        | none => ⌜err ≠ interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
