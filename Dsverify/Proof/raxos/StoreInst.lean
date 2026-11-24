/-
The memory of `sync.Map` and of `ClientBatchStore` (the lab's `StoreInst.lean`), sorry-free.

Perennial's generated `TypedPointsto`/`IntoValTypedUnderlying` instances of `sync.Map` go through
those of `internal/sync.HashTrieMap`, an axiomatized type, which are `sorry`
(`Perennial/GeneratedProof/internal/sync.lean`, `typed_pointsto'HashTrieMap`,
`into_val_typed'HashTrieMap`; notes/perennial-changes.md), and so do the generated instances of
`ClientBatchStore` (`raxos/replica/src`, whose one field is a `sync.Map`). Here, of high priority:
`sync.Map`'s points-to is the deployment's vocabulary's (`QpVocab.map.tp`, `Hyp.lean`) and its
`IntoValTypedUnderlying` the hypothesis `MapHyp.ivt`; `ClientBatchStore`'s are the generated
definitions restated over them, so that every proof that allocates, splits or calls into a store
uses these and no `sorry`.
-/
module

public import Dsverify.Proof.raxos.Hyp
public import Dsverify.GeneratedProof.raxos.replica.src

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI

section syncmap
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `sync.Map`'s points-to: the vocabulary's (`QpVocab.map.tp`). -/
instance (priority := high) raxos.syncMap_typed_pointsto [qv : raxos.hyp.QpVocab GF] :
    TypedPointsto (GF := GF) sync.Map :=
  qv.map.tp

/-- `sync.Map`'s memory respects it: the hypothesis `MapHyp.ivt`. -/
instance (priority := high) raxos.syncMap_into_val_typed [qv : raxos.hyp.QpVocab GF]
    [h : raxos.hyp.sync.MapHyp qv.map] :
    IntoValTypedUnderlying (GF := GF) sync.Map sync.Map.underlying :=
  h.ivt

end syncmap

namespace raxos.replica.src.ClientBatchStore

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [qv : raxos.hyp.QpVocab GF]

attribute [local instance] go.tagged_internal_inst

instance (priority := high) ClientBatchStore_typed_pointsto' :
    TypedPointsto (GF := GF) raxos.replica.src.ClientBatchStore where
  typedPointstoDef l v dq := iprop(
    "clientBatches" ∷ typedPointsto (structFieldRef raxos.replica.src.ClientBatchStore go!"clientBatches" l)
      v.clientBatches' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance (priority := high) ClientBatchStore_into_val_typed' [raxos.replica.src.Assumptions]
    [raxos.hyp.sync.MapHyp qv.map] :
    IntoValTypedUnderlying (GF := GF) raxos.replica.src.ClientBatchStore
      raxos.replica.src.ClientBatchStore.underlying := by
  solve_into_val_typed_struct

instance (priority := high) ClientBatchStore_access_load_clientBatches' (l : Loc)
    (v : raxos.replica.src.ClientBatchStore) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef raxos.replica.src.ClientBatchStore go!"clientBatches" l) v.clientBatches' dq)
      (typedPointsto (structFieldRef raxos.replica.src.ClientBatchStore go!"clientBatches" l) v.clientBatches' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance (priority := high) ClientBatchStore_access_store_clientBatches' (l : Loc)
    (v : raxos.replica.src.ClientBatchStore) (clientBatches' : sync.Map) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef raxos.replica.src.ClientBatchStore go!"clientBatches" l) v.clientBatches' (DFrac.own 1))
      (typedPointsto (structFieldRef raxos.replica.src.ClientBatchStore go!"clientBatches" l) clientBatches' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with clientBatches' := clientBatches' } : raxos.replica.src.ClientBatchStore) (DFrac.own 1)) := by
  solve_pointsto_access_struct

end def_

end raxos.replica.src.ClientBatchStore

end Perennial
