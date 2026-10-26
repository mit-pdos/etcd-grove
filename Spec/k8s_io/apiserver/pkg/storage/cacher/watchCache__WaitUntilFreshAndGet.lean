/-
`(*watchCache).WaitUntilFreshAndGet(ctx, resourceVersion, key)` (`watch_cache.go`), the cached
GET (KEP-6404, `notes/kep-6404-plan.md`): the version to read at is `resourceVersion` parsed by the
versioner, or, for `""` (a consistent read), the store's current revision (`getCurrentRV`, with the
caller's fact `curRV` of it, for a linearizable read a lower bound of etcd's revision at the
call's start, `wcGetOk`, on a context with the caller's `ctxPre`); at `0`, the store's latest snapshot, without the lock; otherwise, under
the read lock (a reader's token, given back), the latest snapshot once the cache is at that version
(`waitAndGetLatestSnapshot`). Without an error, the value and existence of `key` in a state `st`
the store published (with the caller's fact `Ψ st`), at that version or later, and `st`'s version;
an error if the version does not parse, `getCurrentRV` fails, or the wait times out. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.DefsWC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev watchCache.WaitUntilFreshAndGet.spec : Prop :=
  ∀ (wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (parseRV : GoString → Option w64)
    (ctxPre : GoInterface → IProp GF) (curRV : w64 → IProp GF) (ctx : GoInterface)
    (rvs key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher ∗ isWC wc γ Ψ ∗ wcGetOk wc parseRV ctxPre curRV ∗ ctxPre ctx ∗
      sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) }}
    (App (App (App (Val (wc @!! go.GoType.PointerType watchCache.ty @!! go!"WaitUntilFreshAndGet")) (Val #ctx)) (Val #rvs)) (Val #key))
  {{ (value : GoInterface) (ex : Bool) (rv : w64) (err : GoInterface),
      RET (PairV (PairV (PairV #value #ex) #rv) #err);
      sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (p : Loc) (st : SnapSt) (m : w64),
        ⌜value = interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.cacher.store.Element.ty)
            #(lookupElem st.1 key) ∧
          ex = (btree.lookup st.1 key).isSome ∧ rv = st.2 ∧ uint.Z m ≤ uint.Z st.2⌝ ∗
        (⌜rvs = go!""⌝ ∗ curRV m ∨ ⌜rvs ≠ go!"" ∧ parseRV rvs = some m⌝) ∗
        isSnap p st.1 st.2 ∗ □ Ψ st) }}

end spec

end cacher
end EtcdGrove
end Perennial
