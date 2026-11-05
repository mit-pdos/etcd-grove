/-
Lean-first (no Rocq counterpart).

The proof of `(*store).conditionalDelete`: the first read goes through `rwInv` (D30n), which hands
the caller's token `W` at the first state with the response's pair where the model's step is the
identity; after it, the caller's result at a state with the response's answer, or `W` back
(`rwInv_after`). The loop's invariant is the store's reading `s` of the key's key-value at a state
`σ` the read fired at (`rdFacts`), with that result if `σ` hands, else `W`. A missing key or a
failed `validateDeletion` is the model's answer at `σ` (`delete_none`, `delete_invalid`, so `σ`
hands); `deleteOnce` either answers (an error, or the write) or, on a conflict, gives the next
iteration's reading, its update handed there if the step is the identity.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__conditionalDelete
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getStateFromObject
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__deleteOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.conditionalDelete.wp_proof
    (wp_getCur : store.getCurrentState.spec (GF := GF) (hG := hG))
    (wp_getStateFromObject : store.getStateFromObject.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_deleteOnce : store.deleteOnce.spec (GF := GF) (hG := hG))
    (wp_refresh : refreshOnError.spec (GF := GF) (hG := hG)) :
    store.conditionalDelete.spec (GF := GF) (hG := hG) := by
  -- Stage 7b: restated at the Draft; the proof (at a93fbf6a24, before the restatement) is
  -- adapted in the Prove phase, after the Freeze: the cached object (`getStateFromObject`, `cachedOk`), `Preconditions.Check` before `validateDeletion`, and `refreshOnError`'s generalized spec.
  sorry

end proof

end k8s
end EtcdGrove
end Perennial
