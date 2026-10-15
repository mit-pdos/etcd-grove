/-
`store.restore` (`kvstore.go`): the trust boundary (untranslated), on a fresh backend.
Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `s.restore()` on a fresh backend (`NewStore` calls it with `s.mu` held, after creating the
buckets): the identity on the store's verified state, returning `nil`. With an empty `Key`
bucket (`bucketView γ q ∅`), `restore` reads nothing, so the index (`isTreeIndex ti γ.idx`)
is not touched; `restoreIntoIndex` sends `currentRev = 1` through its channel (stored into
`currentRev` under `s.revMu`, the value it holds); no finished or scheduled compaction is
found (`compactMainRev` stays `-1`, no compaction runs: `compactLockfree` is not called) and no lease is attached; `s.revMu`
is locked and unlocked fresh (it is back at its zero value). The store of `1` into
`currentRev` is modelled as no write: `NewStore` holds only half of `currentRev` here (the
batch lock holds the other half since `NewStore`'s first `tx.Unlock()`, as the writers'
resource); in the code the write is protected by `s.mu` held exclusively, which the model's
`s.mu` (holding nothing) does not express. A backend with data is out of scope (the real
`restore` would rebuild the index from it). -/
abbrev mvcc.store.restore.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (b le : GoInterface) (ti lg : Loc) (q : Qp) (P : IProp GF)
    (f : val) (RT WT W Wi Dep : IProp GF) (Cmp : Prop)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"b"] ↦□ b ∗
      mvcc.isKeyBackendG b (mvcc.bucketView γ) RT WT PutOk (mvcc.delKey γ) W Wi Dep Cmp P f ∗
      mvcc.bucketView γ q ∅ ∗
      s.[store, go!"kvindex"] ↦□
        (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.isTreeIndex ti γ.idx ∗ s.[store, go!"le"] ↦□ le ∗ s.[store, go!"lg"] ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #GoInterface.nil; mvcc.bucketView γ q ∅ ∗
      s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half} (W64 1 : w64) ∗
      s.[store, go!"compactMainRev"] ↦ (W64 (-1) : w64) ∗
      s.[store, go!"revMu"] ↦ (zero_val sync.RWMutex) }}

end spec

end EtcdGrove
end Perennial
