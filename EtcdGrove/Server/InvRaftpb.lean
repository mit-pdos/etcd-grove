/-
raft v3.7's `raftpb` messages as the apply thread reads them: the shared vocabulary of
`Spec/Entry__Get*.lean` and `Spec/ConfChange__GetId.lean`. Lean-first (no Rocq
counterpart).

This is etcd's own raft dependency (`EtcdCache/Code/go_etcd_io/raft/v3/raftpb.lean`, from
etcd's `go.mod`), not the fork `EtcdRaft/` translates: its messages are protobuf-go v2
(optional fields are pointers, nil for absent, read through getters that default to the
zero value). As in `Cache/InvStore.lean`, a message is described through its fields only
(`entryAt`, persistent), never a whole-message points-to (whose instances contain the opaque
`state : impl.MessageState`).
-/
import EtcdGrove.Server.BaseApply

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- A raft entry as the apply thread uses it. -/
structure EntryModel where
  term : w64
  index : w64
  typ : w32
  data : List w8

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `TypeRepr` of the messages the apply thread reads fields of, straight from their
`TypeAssumptions` (as `Cache/InvStore.lean` does for the cache's messages). -/
instance (priority := high) entry_typeRepr : TypeRepr raftpb.Entry.ty raftpb.Entry :=
  go.type_repr_underlying (u := raftpb.Entry.underlying)

instance (priority := high) entry_typeRepr_u : TypeRepr raftpb.Entry.underlying raftpb.Entry :=
  go.type_repr_underlying (u := raftpb.Entry.underlying)

instance (priority := high) confChange_typeRepr : TypeRepr raftpb.ConfChange.ty raftpb.ConfChange :=
  go.type_repr_underlying (u := raftpb.ConfChange.underlying)

instance (priority := high) confChange_typeRepr_u :
    TypeRepr raftpb.ConfChange.underlying raftpb.ConfChange :=
  go.type_repr_underlying (u := raftpb.ConfChange.underlying)

/-- An optional `uint64` field's pointer `p` holds `v` (nil: absent, read as 0). -/
def optU64 (p : Loc) (v : w64) : IProp GF :=
  if p = null then iprop(⌜v = W64 0⌝) else iprop(p ↦□ v)

instance optU64_persistent (p : Loc) (v : w64) : Persistent (optU64 (GF := GF) p v) := by
  unfold optU64; split <;> infer_instance

/-- An optional `int32` (enum) field's pointer `p` holds `v` (nil: absent, read as 0). -/
def optU32 (p : Loc) (v : w32) : IProp GF :=
  if p = null then iprop(⌜v = W32 0⌝) else iprop(p ↦□ v)

instance optU32_persistent (p : Loc) (v : w32) : Persistent (optU32 (GF := GF) p v) := by
  unfold optU32; split <;> infer_instance

/-- `e` is a (non-nil) read-only entry modelled by `m`. -/
def entryAt (e : Loc) (m : EntryModel) : IProp GF :=
  iprop(⌜e ≠ null⌝ ∗
    ∃ (pt pi pty : Loc) (d : GoSlice),
      structFieldRef raftpb.Entry go!"Term" e ↦□ pt ∗ optU64 pt m.term ∗
      structFieldRef raftpb.Entry go!"Index" e ↦□ pi ∗ optU64 pi m.index ∗
      structFieldRef raftpb.Entry go!"Type" e ↦□ pty ∗ optU32 pty m.typ ∗
      structFieldRef raftpb.Entry go!"Data" e ↦□ d ∗ d ↦*□ m.data)

instance entryAt_persistent (e : Loc) (m : EntryModel) : Persistent (entryAt (GF := GF) e m) := by
  unfold entryAt; infer_instance

end defs

end EtcdGrove
end Perennial
