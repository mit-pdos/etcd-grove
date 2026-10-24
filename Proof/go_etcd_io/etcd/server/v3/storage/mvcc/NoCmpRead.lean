/-
**A backend that records no compaction reads none** (the restore plan's R4c; the trust boundary).
Lean-first.

`kbNoCmp` (`InvStore.lean`, opaque, exclusive) names a fact about a backend's bbolt data: its
`Meta` bucket holds neither compaction key (`schema.ScheduledCompactKeyName`,
`FinishedCompactKeyName`), and only a store over it writes them (its compaction, which needs the
compaction right and, for the real backend, is not even supported: `storeCmp`). The model of
the backend's readers leaves out every bucket but `Key` (`bridgeParams`: `Meta` is the hook's), so
what a read of those keys returns cannot be derived; `store.restore` reads both right after
taking its read transaction's lock, before any store over the backend exists. This states what
`kbNoCmp` means for such a read: a `ReadTx` of the store's backend (`keyReadSnap` over the store's
view, `bucketView γ`, or, for a bucket with data, `keyReadSnapC` over its clean view,
`bucketViewC γ`: the restore plan's R5c) finds nothing at either key (`metaReadSpec rt true`). It
replaced the whole `store.restore` axiom (option 1 of R4).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
open Iris Iris.BI

namespace mvcc

section axioms
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: a backend that records no compaction finds none** (see the file header). -/
axiom kbNoCmp_metaNone (γ : StoreNames) (RT : IProp GF) (Del : GoString → IProp GF)
    (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    kbNoCmp γ.kb γ.bucket ⊢
      (keyReadSnap (bucketView γ) RT Del true rt m L ∨ keyReadSnapC (bucketViewC γ) RT rt m L) -∗
      □ metaReadSpec rt true

end axioms

end mvcc
end EtcdGrove
end Perennial
