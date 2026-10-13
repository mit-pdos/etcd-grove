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
views (owned: `newWatchableStore` overwrites them), all the reader slots of its locks
(`storeReader`, one per slot) and the revision budget (`2 ^ 63 - 5` tokens: the batch lock's
resource `writerRes` needs `ilog.length + ntok + 3 ≤ 2 ^ 63`, with the initial log of length 2),
and the index's certificate of the initial log.

* The backend is of the instance `kb` (2026-10-13, unit 5): `none`, mvcc's assumed contract over
  the store's own ghost map `γb`; `some d`, the real backend (`BackendBridge.lean`). Its contract
  is quantified over the store's ghost names and location (with that instance and bucket name),
  because the batch lock's resource `storeW s γ` is the store's (`writerRes s γ`, or the real
  backend's late-bound `lateW`, which `NewStore` registers at its first `tx.Unlock()` with the
  right `kbRegRight kb`).
* The fresh backend's view of the empty bucket `kbView kb γb 1 ∅` is *given* by the backend's
  creator (the fresh-backend assumption), as are the backend's reader tokens, one per reader
  slot (`kbRT kb`, lent to `NewStore`'s own calls and returned in the `storeReader`s), and two
  write tokens (`kbWT kb`: the first `Unlock` and `ForceCommit`).
* The lessor's ghost name `γl` (its granted leases) is its own: the lessor exists before the
  store.
* The backend's batch lock has invariant `P` and runs the post-lock hook `f` (`P f`, any); the
  store records them (`hookIs`, returned), for its writers.
* A `nil` logger is replaced by `zap.NewNop()`'s; the configuration `cfg` is not modelled.
* The right to close the store once (`storeCloser`: its `stopc` field, owned). -/
abbrev mvcc.NewStore.spec : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb⌝ →
        mvcc.isKeyBackendG b (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
          (mvcc.storePutOk γ) (mvcc.storeW s γ) (mvcc.kbWi γ.kb) P f) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      mvcc.isLessor le γl }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : mvcc.StoreNames, ⌜γ.bucket = γb ∧ γ.leases = γl ∧ γ.kb = kb⌝ ∗
      mvcc.isStore s γ ∗ mvcc.hookIs γ P f ∗
      (∃ rv wv : Loc,
        s.[store, go!"ReadView"] ↦
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv s γ ∗
        s.[store, go!"WriteView"] ↦
          (interface.mkOk (go.GoType.PointerType writeView.ty) #wv : GoInterface) ∗
        mvcc.isWriteView wv s γ) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        mvcc.storeReader s γ) ∗
      ownToks γ.revs (2 ^ 63 - 5) ∗ mvcc.idxCert γ.idx [[], []] ∗ mvcc.storeCloser s }}

end spec

end EtcdGrove
end Perennial
