/-
raft v3.7's `raftpb` messages as the server's raft wrapper (`raft.go`) reads them: a
`Message`'s recipient and type, a `HardState`'s three fields, a `Snapshot`'s metadata index.
Lean-first (no Rocq counterpart). As `entryAt` (`InvRaftpb.lean`), a message is described
through its fields only, never a whole-message points-to (whose instances contain the opaque
`state : impl.MessageState`); a nil message reads as its zero value, as the getters do.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A `HardState`'s fields (each absent reads as 0). -/
structure HardStateModel where
  term : w64
  vote : w64
  commit : w64

/-- The empty `HardState` (`raft.IsEmptyHardState`). -/
def HardStateModel.empty : HardStateModel := ⟨W64 0, W64 0, W64 0⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

instance (priority := high) message_typeRepr : TypeRepr raftpb.Message.ty raftpb.Message :=
  go.type_repr_underlying (u := raftpb.Message.underlying)

instance (priority := high) message_typeRepr_u :
    TypeRepr raftpb.Message.underlying raftpb.Message :=
  go.type_repr_underlying (u := raftpb.Message.underlying)

instance (priority := high) hardState_typeRepr : TypeRepr raftpb.HardState.ty raftpb.HardState :=
  go.type_repr_underlying (u := raftpb.HardState.underlying)

instance (priority := high) hardState_typeRepr_u :
    TypeRepr raftpb.HardState.underlying raftpb.HardState :=
  go.type_repr_underlying (u := raftpb.HardState.underlying)

instance (priority := high) snapshot_typeRepr : TypeRepr raftpb.Snapshot.ty raftpb.Snapshot :=
  go.type_repr_underlying (u := raftpb.Snapshot.underlying)

instance (priority := high) snapshot_typeRepr_u :
    TypeRepr raftpb.Snapshot.underlying raftpb.Snapshot :=
  go.type_repr_underlying (u := raftpb.Snapshot.underlying)

instance (priority := high) snapshotMetadata_typeRepr :
    TypeRepr raftpb.SnapshotMetadata.ty raftpb.SnapshotMetadata :=
  go.type_repr_underlying (u := raftpb.SnapshotMetadata.underlying)

instance (priority := high) snapshotMetadata_typeRepr_u :
    TypeRepr raftpb.SnapshotMetadata.underlying raftpb.SnapshotMetadata :=
  go.type_repr_underlying (u := raftpb.SnapshotMetadata.underlying)

/-- `m` is a (non-nil) read-only message to `to` of type `ty` (the fields the raft wrapper
reads). -/
def msgAt (m : Loc) (to : w64) (ty : w32) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗
    ∃ (pto pty : Loc),
      structFieldRef raftpb.Message go!"To" m ↦□ pto ∗ optU64 pto to ∗
      structFieldRef raftpb.Message go!"Type" m ↦□ pty ∗ optU32 pty ty)

instance msgAt_persistent (m : Loc) (to : w64) (ty : w32) :
    Persistent (msgAt (GF := GF) m to ty) := by
  unfold msgAt; infer_instance

/-- `p` is a read-only `*HardState` modelled by `hs`; nil reads as the empty one. -/
def hardStateAt (p : Loc) (hs : HardStateModel) : IProp GF :=
  if p = null then iprop(⌜hs = HardStateModel.empty⌝) else
  iprop(∃ (pt pv pc : Loc),
    structFieldRef raftpb.HardState go!"Term" p ↦□ pt ∗ optU64 pt hs.term ∗
    structFieldRef raftpb.HardState go!"Vote" p ↦□ pv ∗ optU64 pv hs.vote ∗
    structFieldRef raftpb.HardState go!"Commit" p ↦□ pc ∗ optU64 pc hs.commit)

instance hardStateAt_persistent (p : Loc) (hs : HardStateModel) :
    Persistent (hardStateAt (GF := GF) p hs) := by
  unfold hardStateAt; split <;> infer_instance

end defs

end EtcdGrove
end Perennial
