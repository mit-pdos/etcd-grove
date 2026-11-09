/-
`(*DoubleBarrier).enteredClients(cli)` (`double_barrier.go`): `Get(key/waiters, WithPrefix(),
WithSort(CreateRevision, Ascend))`.

**Users**: `Enter` (twice). Internal.

**Proof sketch**: `isClient_KV`; `KV.GetTriple` (`b.ctx`: `ctxOk`, `ctxPrin who ctx who`; `lo = 0`, `authLb γ 0`) with an update made of
`etcdPeek` (its commit's `etcdLb γ σ`; `Reach σ0 σ` by `etcdLb_reach` inside it); the reply is the
range's answer at `σ`'s store, or an error (`errVal`, `indefCall`: `recipeErrOk`).

**Changes**: old spec over the recipes' client invariant; now the read's answer.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`b.enteredClients(c)`**: the waiters under `key/waiters` by creation revision, read at a state reached from `σ0`, or an error. -/
def DoubleBarrier.enteredClients.spec : Prop :=
  ∀ (b c : Loc) (γ : Cluster) (who : Principal) (key : GoString) (count id : w64)
    (my : Option RKSt) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ dbOwn b γ who key count id my ∗ isClient c γ who ∗ etcdPeek γ ∗ etcdLb γ σ0 }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"enteredClients")) (Val #c))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); dbOwn b γ who key count id my ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (σ : State) (m : RangeRespM) (a : RangeAns),
          etcdLb γ σ ∗ rangeRespOwn resp (DFrac.own 1) m ∗
          ⌜Reach σ0 σ ∧ m.hdr.map (·.revision) = some (W64 σ.kv.rev) ∧ m.ofAns a ∧
            (opGetM (waitersPfx key) [withPrefixM, withSortM SortByCreateRevision SortAscend]).rangeReq.answers
              σ.kv.store a⌝) ∨
       (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ recipeErrOk err)) }}

end spec

end Recipes
end EtcdGrove
end Perennial
