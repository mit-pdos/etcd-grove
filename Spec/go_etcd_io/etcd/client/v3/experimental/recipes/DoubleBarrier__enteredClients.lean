/-
`recipes.(*DoubleBarrier).enteredClients(cli)` (`client/v3/experimental/recipes/double_barrier.go`). Lean-first (no Rocq
counterpart); see `InvDoubleBarrier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvDoubleBarrier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`b.enteredClients(client)`**, with the barrier's session's client, knowing etcd has reached
`lo`: the get `Get(key + "/waiters", WithPrefix(), WithSort(SortByCreateRevision, SortAscend))`;
`(resp, nil)` with `resp` listing the keys with the prefix `key/waiters` of etcd's state at its
revision `R ≥ lo`, sorted by create revision (`waitersResp`), or `(nil, err)`. -/
abbrev DoubleBarrier.enteredClients.spec : Prop :=
  ∀ (b s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (key : GoString)
    (count lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isDoubleBarrier b s γ client id key count ∗ etcdReached lo }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"enteredClients"))
      (Val #client))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (R : w64) (kvs : List EtcdKv), etcdReached R ∗
        waitersResp (key ++ go!"/") (key ++ go!"/waiters") resp R kvs ∗ ⌜sint.Z lo ≤ sint.Z R⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
