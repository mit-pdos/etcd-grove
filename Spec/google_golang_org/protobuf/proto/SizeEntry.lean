/-
`proto.Size` of a raft v3.7 `*pb.Entry`: the trust boundary, stage R1. `entsSize` and `limitSize`
size entries with it (`util.go:277,290,292`), replacing gogoproto's generated `Entry.Size()`, which
the old proof translated.
Lean-first; stated over the raftpb ownership predicates of `Raft37/Proof/go_etcd_io/raft/v3/InvPb.lean`
(this file imports only `Raft37` modules: the old raft's and `EtcdDeps`'s raftpb define the same
names). Until the raft trees are swapped (stage R6) a raft v3.7 statement about `proto.*` is kept
apart from the etcd side's (`Clone.lean`, `Size.lean`, `Marshal.lean`, `Unmarshal.lean`), as
`MarshalIRR.lean` is from `Marshal.lean`.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `proto.Size(e)` of a `*pb.Entry` holding `e` (at any fraction) returns some `int` at least `0`;
no spec fixes a size (the specs of `entsSize`/`limitSize` leave sizes unspecified).

Against protobuf-go v1.36.11 (`proto/size.go`, `internal/impl/encode.go:118-129`): `Size` is the
length of the wire encoding, a non-negative `int`; it reads the message and stores the size cache
atomically (`atomic.StoreInt32`): a write to the hidden fields only, which the hidden-field
invariant (`pbMsg`, inside `entPts`) owns. -/
abbrev proto.SizeEntry.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ entPts l dq e }}
    (App (Val (@! google_golang_org.protobuf.proto.Size)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.Entry.ty) #l)))
  {{ (n : w64), RET #n; entPts l dq e ∗ ⌜0 ≤ sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
