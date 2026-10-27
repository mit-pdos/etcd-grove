/-
`NewThreadSafeStore(indexers, indices, opts...)` (`thread_safe_store.go:528`): an empty store with
the indexers, without options. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `NewThreadSafeStore(im, ip, opts)` with no options (as `NewIndexer`'s and `NewStore`'s calls
without metrics), the indexers `im` (their functions meeting their contracts for `Fam` at
`fnIds`; the map is the store's from now on) and empty indices `ip` (as `Indices{}`): the store
`c` as a `ThreadSafeStore`, with no items, resource version `""`, the indexers, and all its
lock's reader slots. -/
abbrev NewThreadSafeStore.spec : Prop :=
  ∀ (OK : GoInterface → IProp GF) (Fam : Nat → Fn) (im ip : Loc) (fv : GMap GoString GoFunc)
    (fnIds : GMap GoString Nat) (opts : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      im ↦$ fv ∗ fnsOk OK fv (GMap.fmap Fam fnIds) ∗ ip ↦$ (∅ : GMap GoString Loc) ∗
      opts ↦* ([] : List GoFunc) }}
    (App (App (App (Val (@! NewThreadSafeStore)) (Val #im)) (Val #ip)) (Val #opts))
  {{ (c : Loc), RET #(interface.mkOk (go.GoType.PointerType threadSafeMap.ty) #c);
      ∃ γ : TsNames, isTS c γ OK Fam ∗ storeSt γ ⟨∅, [], fnIds⟩ ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        tsReader c γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
