/-
`recipes.newSequentialKV(kv, prefix, val)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
see `InvRecipesClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesSeq

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

/-- **`newSequentialKV(kv, prefix, val)`**, for a prefix `kp` whose range and bookkeeping key
`__kp` (`baseKey kp`) are under the prefix `pfx` of `kv`'s contracts (the priority queue's are
at the empty prefix: `kp/...` and `__kp` are two disjoint prefixes), knowing etcd has reached
`lo`: gets the last key under `kp` (at a revision `g ≥ lo`), parses its last `/`-field as a
number `n` (`fmt.Sscanf`), and puts `__kp` and `kp/%016d(n + 1)` in one transaction at `r ≥ g`
if `__kp` was not modified since `g` (otherwise retries): on success a fresh `*RemoteKV` for a
key under `kp ++ "/"` put at `r` (`seqKeyPutAt`: the key made from etcd's state at `g`,
`SeqNext`, and etcd's state at `r` the two puts on its state at `r - 1`); a nil pointer with
the error otherwise (the get's, `Sscanf`'s on a last key whose field is not a number, the
transaction's). Not "created": the transaction does not check that the key is absent. Its order
and freshness hold under a premise on the keys under `kp` (`seqKeyPutAt_order`,
`seqKeyPutAt_created`, `InvRecipesSeq.lean`). -/
abbrev newSequentialKV.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx kp val : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗ ⌜pfx <+: kp ∧ pfx <+: baseKey kp⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV))
      (Val #(GoInterface.ok kv))) (Val #kp)) (Val #val))
  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (g r : w64),
        ownRemoteKV rk ⟨GoInterface.ok kv, key, r, val⟩ ∗ etcdReached r ∗
        seqKeyPutAt pfx kp key val g r ∗
        ⌜(kp ++ go!"/") <+: key ∧ sint.Z lo ≤ sint.Z g ∧ sint.Z g ≤ sint.Z r ∧
          sint.Z r < 2 ^ 63 - 1⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ rk = null⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
