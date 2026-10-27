/-
`proto.Unmarshal` into a raft v3.7 `*pb.ConfChange`: the trust boundary, stage R1. `stepLeader` decodes a
proposed conf-change entry with it (`raft.go:1314`, into a fresh `&pb.ConfChange{}`), replacing
gogoproto's generated `ConfChange.Unmarshal` (the old axiom `raftpb.ConfChange.Unmarshal`).
Lean-first; stated over the raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`
(a raft v3.7 statement about `proto.*`, kept apart from the etcd side's `Clone.lean`, `Size.lean`,
`Marshal.lean`, `Unmarshal.lean`, as `MarshalIRR.lean` is from `Marshal.lean`; until stage R6 swapped
the raft trees, 2026-10-16, this file was the only one importing the `Raft37` tree's raftpb).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

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

/-- `proto.Unmarshal(d, cc)` into a `*pb.ConfChange` (any value: `Unmarshal` resets it) computes `ccDecodeV1`
(which names what it does, `CCModel.lean`): on bytes it decodes it returns `nil` and the message
holds the content, owned (its `Context` a fresh slice, read-only from then on, its hidden fields
its own invariant); on any other bytes a non-`nil` error, leaving the message some value. It
never panics and never retains `d`.

Against protobuf-go v1.36.11 (`proto/decode.go`): `Unmarshal` is `UnmarshalOptions{}.unmarshal`
with `Merge` false, so it first resets the message; every read is bounds-checked
(`protowire.Consume*` returns an error, never panics) and unknown fields are kept in the hidden
`unknownFields`; `bytes` fields are copied out of the input (no aliasing: the aliasing option is
internal and off). -/
abbrev proto.UnmarshalConfChange.spec : Prop :=
  ∀ (d : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (x : raftpb.ConfChange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ d ↦*{dq} bs ∗ p ↦ x }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #d)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p)))
  {{ (err : GoInterface), RET #err; d ↦*{dq} bs ∗
      match ccDecodeV1 bs with
      | some m => ⌜err = interface.nil⌝ ∗ ownConfChange p (DFrac.own 1) m
      | none => ⌜err ≠ interface.nil⌝ ∗ ∃ x' : raftpb.ConfChange, p ↦ x' }}

end spec

end EtcdGrove
end Perennial
