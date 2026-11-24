/-
**`pbutil.MustMarshalMessage(m)` of the WAL's metadata** (`bootstrapNewWAL`, `bootstrap.go:718-723` at
the etcd pin `edc800c6f`: `&etcdserverpb.Metadata{NodeID: new(nodeID), ClusterID: new(cid)}`). Claim #34,
stage 4 (2026-11-25). Lean-first.

**Not proved: a hypothesis** (`?` in the server's `Link.lean`) of `bootstrapNewWAL`'s linked result. It
holds of Go: protobuf-go's `Marshal` of a `Metadata` with both optional `uint64` fields set (`NodeID` 1,
`ClusterID` 2, `etcdserver.proto`) and no unknown fields writes the two varint fields in field order,
`walMetaEnc id cid` (`storage/WalRecs.lean`), into a fresh slice, and never fails on it. It becomes the
main tree's generic spec (`MustMarshalMessage.spec`, `pbEncC T c`) once `etcdserverpb.Metadata` is a
registered protobuf type (`pbModelOf`, as `walpb.Snapshot`'s `PbSnapshot.lean`): a trusted schema and
encoder, which is why it is left a hypothesis here. `proto.Marshal` may write the message's hidden
fields (its `sizeCache`, its `MessageState`), so the record is owned and given back with the two
pointers unchanged.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import GeneratedProof.go_etcd_io.etcd.api.v3.etcdserverpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage.specMeta : Prop :=
  ∀ (l : Loc) (m : go_etcd_io.etcd.api.v3.etcdserverpb.Metadata) (id cid : w64) (d1 d2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ l ↦ m ∗
      ⌜m.unknownFields' = slice.nil⌝ ∗ m.NodeID' ↦{d1} id ∗ m.ClusterID' ↦{d2} cid }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.Metadata.ty) #l)))
  {{ (d : GoSlice), RET #d;
      d ↦* walMetaEnc id cid ∗ ownSliceCap w8 d (DFrac.own 1) ∗
      (∃ m' : go_etcd_io.etcd.api.v3.etcdserverpb.Metadata, l ↦ m' ∗
        ⌜m'.NodeID' = m.NodeID' ∧ m'.ClusterID' = m.ClusterID'⌝) ∗
      m.NodeID' ↦{d1} id ∗ m.ClusterID' ↦{d2} cid }}

end spec

end EtcdGrove
end Perennial
