/- Port of election_proof/spec_Entry__Size.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `Entry.Size()` (pointer receiver, `raft.pb.go:1244`, gogoproto): the
protobuf-encoded size of an entry, `1 + sovRaft(…)` per varint field and, when `Data`
is non-nil, `1 + len(Data) + sovRaft(len(Data))`.

**Translated and proved** (2026-10-08; until then an `axiom`, since `raftpb.toml` did
not translate the marshalling code): `Entry.Size` and `sovRaft` are in the translated
set, and `Proof/Entry__Size.lean` proves this triple from the body. The only change to
the triple is the `isPkgInit raftpb` conjunct, which `sovRaft`'s call to `bits.Len64`
needs; every caller holds `isPkgInit raft.v3`, which provides it.

It is reached on the election path: `raftLog.slice` applies `limitSize` to every slice
it returns and `limitSize` calls `ents[0].Size()` on any non-empty input, so
`hasUnappliedConfChanges`'s `scan` hits it whenever `applied < committed`.

The postcondition says **nothing about the value**: `limitSize` and `entsSize` only use
the sizes to decide where to cut a slice, and no caller on this path depends on where
the cut falls -- `scan` pages until `lo` reaches `hi` whatever the page sizes are. It
owns the receiver (the method reads every field through the pointer) and hands it
back. -/
abbrev raftpb.Entry.Size.spec : Prop :=
  ∀ (e : Loc) (dq : DFrac) (ev : raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ e ↦{dq} ev }}
    (App (Val (e @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; e ↦{dq} ev }}

end spec

end EtcdGrove
end Perennial
