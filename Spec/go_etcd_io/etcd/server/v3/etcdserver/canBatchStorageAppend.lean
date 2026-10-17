/-
`canBatchStorageAppend(entries, next)` (raft.go; etcd-io/etcd#22223, `pr-verify/etcd-22223`):
whether the append worker may coalesce the next `MsgStorageAppend`'s entries with the batch so far.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `canBatchStorageAppend(entries, next)` over read-only entries: `true` exactly when either
slice is empty or `next[0].Index == entries[len-1].Index + 1` (the Go sum wraps: at a last index
of `2^64 - 1` the result is `next[0].Index == 0`, which the spec states as is). -/
abbrev canBatchStorageAppend.spec : Prop :=
  ∀ (s1 s2 : GoSlice) (l1 l2 : List Loc) (ms ns : List EntryModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      s1 ↦*□ l1 ∗ entriesAt l1 ms ∗ s2 ↦*□ l2 ∗ entriesAt l2 ns }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.canBatchStorageAppend)) (Val #s1))
      (Val #s2))
  {{ (b : Bool), RET #b;
      ⌜b = true ↔ (ms = [] ∨ ns = [] ∨
        ∃ a z, ms.getLast? = some a ∧ ns.head? = some z ∧ z.index = a.index + W64 1)⌝ }}

end spec

end EtcdGrove
end Perennial
