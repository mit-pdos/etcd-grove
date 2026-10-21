/-
`proto.Clone` of a raft v3.7 `*pb.Entry`: the trust boundary (`google.golang.org/protobuf` is
names-only), raft v3.7 retarget, stage R1 (`notes/decisions.md`, "The protobuf runtime as raft's
trust boundary"). `appendEntry` clones every entry it appends (`raft.go:817`) and stamps the
clone.
Lean-first; stated over the raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`
(a raft v3.7 statement about `proto.*`, kept apart from the etcd side's `Clone.lean`, `Size.lean`,
`Marshal.lean`, `Unmarshal.lean`, as `MarshalIRR.lean` is from `Marshal.lean`; until stage R6 swapped
the raft trees, 2026-10-16, this file was the only one importing the `Raft37` tree's raftpb).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `proto.Clone(e)` of a `*pb.Entry` holding `e` (passed as a `proto.Message`), at any fraction:
a fresh `*pb.Entry`, owned, holding the same record `e` (D6, raft v3.7 retarget stage R4: the
record's `Data'` is the bytes; the clone's `Data` is a fresh slice holding them, which `entOwn`
hides, read-only, as every entry's bytes are); the original is untouched. (Until D6 the record
held the slice, and the clone was stated as `e` with a fresh `Data' := d'` holding the bytes.)

Against protobuf-go v1.36.11 (`proto/merge.go`: `Clone` is `Merge` into a new message of the
same type; `internal/impl/merge.go`): every populated scalar field is copied into a fresh
pointer, a `bytes` field is copied (`mergeBytes`: `append(emptyBuf[:], src...)`, so the copy's
slice is fresh and holds the same bytes; a nil one stays nil, which holds no bytes either), the
unknown fields are copied (the copy's own hidden fields, its `pbMsg`, with the same bytes;
`entOwn` says some), and the source is only read (its size cache is not written by `Clone`; its
hidden-field invariant is untouched). -/
abbrev proto.CloneEntry.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ entPts l dq e }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.Entry.ty) #l)))
  {{ (l' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.Entry.ty) #l');
      entPts l dq e ∗ entOwn l' e }}

end spec

end EtcdGrove
end Perennial
