/-
`NewStore` (`kvstore.go`), on a fresh backend. Lean-first (no Rocq counterpart); see
`InvStore.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

/-- `NewStore(lg, b, le, cfg)` on a fresh backend `b` returns a store `s` (`isStore`) at the
initial committed log `[[], []]` (revision 0 and `currentRev = 1`, both empty), with its two
views, all the reader slots of its locks (`storeReader`, one per slot) and the revision budget
(`2 ^ 63 - 5` tokens: the batch lock's resource `writerRes` needs `ilog.length + ntok + 3 ≤
2 ^ 63`, with the initial log of length 2).

* The empty bucket view `ghostMapAuth γb 1 ∅` is *given* by the backend's creator (the
  fresh-backend assumption), not allocated by the store; the backend's contract is quantified
  over the store's ghost names and location (with that bucket name), because the batch lock's
  resource `writerRes s γ` is the store's choice. `NewStore` deposits it into the batch lock
  at its first `tx.Unlock()`.
* The lessor's ghost name `γl` (its granted leases) is its own: the lessor exists before the
  store.
* A `nil` logger is replaced by `zap.NewNop()`'s; the configuration `cfg` is not modelled. -/
abbrev mvcc.NewStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (γb γl : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb⌝ →
        mvcc.isKeyBackend b (mvcc.bucketView γ) (mvcc.writerRes s γ)) ∗
      ghostMapAuth γb 1 (∅ : mvcc.Bucket) ∗ mvcc.isLessor le γl }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.leases = γl⌝ ∗
      mvcc.isStore s γ ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦□
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦□
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.storeReader s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) }}

end spec

end EtcdGrove
end Perennial
