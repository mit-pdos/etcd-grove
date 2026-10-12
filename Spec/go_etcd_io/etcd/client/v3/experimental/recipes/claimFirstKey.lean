/-
`recipes.claimFirstKey(kv, kvs)` (`client/v3/experimental/recipes/client.go`). Lean-first (no Rocq counterpart);
see `InvRecipesClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

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

/-- **`claimFirstKey(kv, kvs)`**, for a read-only slice of `*KeyValue`s `ps` holding `vs`
(`kvPtrsAt`: a get response's), each a key under the prefix `pfx` of `kv`'s contracts with a
positive mod revision, knowing etcd has reached `lo`: claims them in order (`deleteRevKey`) and
* `(p, nil)`: `p` is the `i`-th, the first one claimed (`revKeyDeleted` at some `r ≥ lo`, with
  the token of the revision `r`, `etcdRevToken`), each before it was gone at some revision at
  least `lo` (`revKeyGone`);
* `(nil, nil)`: every one was gone at some revision at least `lo`;
* `(nil, err)` with an error. -/
abbrev claimFirstKey.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx : GoString) (sl : GoSlice) (ps : List Loc) (vs : List EtcdKv)
    (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗ sl ↦*□ ps ∗
      kvPtrsAt ps vs ∗ ⌜∀ v ∈ vs, pfx <+: v.key ∧ 0 < sint.Z v.modRev⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.claimFirstKey))
      (Val #(GoInterface.ok kv))) (Val #sl))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ n : Nat, claimedBefore pfx lo vs n ∗
        ((⌜p = null ∧ n = vs.length⌝) ∨
         (∃ (v : EtcdKv) (r : w64), ⌜ps[n]? = some p ∧ vs[n]? = some v⌝ ∗ kvValAt p v ∗
           etcdReached r ∗ revKeyDeleted pfx v.key v.modRev r ∗ etcdRevToken r ∗
           ⌜sint.Z lo ≤ sint.Z r⌝))) ∨
      ⌜err ≠ GoInterface.nil ∧ p = null⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
