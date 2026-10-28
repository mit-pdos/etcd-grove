/-
`NewStore(keyFunc, opts...)` (`store.go:413`): a `cache` over a new thread-safe store, without
options. Lean-first; for the controller's expectations (`NewControllerExpectations`, phase 5 of
`notes/k8s-daemonset-plan.md`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs

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

/-- `NewStore(kf, opts)` with no options (`opts` empty, e.g. `nil`): the store `ca`, a `Store`
over a new thread-safe store with key function `kf`, no transformer and no indexers, for any
contract `OK` on its objects and any (unused) family `Fam`; no items, resource version `""`, and
all of the thread-safe store's reader slots. -/
abbrev NewStore.spec : Prop :=
  ∀ (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (kf : GoFunc) (opts : GoSlice) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      opts ↦*{dq} ([] : List GoFunc) }}
    (App (App (Val (@! NewStore)) (Val #kf)) (Val #opts))
  {{ (ca : Loc), RET #(interface.mkOk (go.GoType.PointerType cache.ty) #ca);
      ∃ (ts : Loc) (γ : TsNames), isCache ca ts γ OK Fam kf ∗ storeSt γ ⟨∅, [], ∅⟩ ∗
        [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
