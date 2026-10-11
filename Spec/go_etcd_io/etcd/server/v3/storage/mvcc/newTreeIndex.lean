/-
`newTreeIndex` (`index.go`). Lean-first (no Rocq counterpart); see `InvIndex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newTreeIndex(lg)` (a non-nil logger): a fresh tree index (as the `index` interface), with its writer's handle
for the empty log and its reader tokens (one per reader slot of the `RWMutex`). -/
abbrev mvcc.newTreeIndex.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ ⌜lg ≠ null⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex)) (Val #lg))
  {{ (ti : Loc), RET #(interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti);
      ∃ γ : mvcc.IdxNames, mvcc.isTreeIndex ti γ ∗ mvcc.idxWriter γ [] [] ∗
        [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.idxReader ti γ }}

end spec

end EtcdGrove
end Perennial

