/-
`recipes.(*PriorityQueue).EnqueueUint64(val, pr)` (`client/v3/experimental/recipes/priority_queue.go`),
added by etcd-io/etcd#18557 (`notes/pr-verify/etcd-18557.md`). Lean-first (no Rocq counterpart);
see `InvRecipesQueue.lean` and `PriorityQueue__Enqueue.lean`, whose spec this is with a `uint64`
priority.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesQueue
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`q.EnqueueUint64(val, pr)`**, as `Enqueue`'s spec with `pr : w64`, knowing etcd has reached `lo`: `newSequentialKV(client.KV,
fmt.Sprintf("%s%05d", key ++ "/", pr), val)`, on the prefix `kp = key ++ "/" ++ <pr, 5 digits>`
(the priority, zero-padded to at least 5 digits: `Sprintf`'s model; a priority of `10^5` or
more has 6 to 20 digits, so the prefixes no longer have one length, `pqueue_enqueueUint64_*` in
`Results.lean`): `nil` means a key under `kp ++ "/"` was put with
the value `val` at some `r` etcd has reached, made from etcd's state at the get's revision `g`,
`lo ≤ g ≤ r` (`seqKeyPutAt`, unit 1b's: not "created", the transaction does not check the key's
absence; its order, greater than every key under `kp` then, and its freshness hold under the
premise on the keys under `kp`, `seqKeyPutAt_order`, `seqKeyPutAt_created`); or an error. -/
abbrev PriorityQueue.EnqueueUint64.spec : Prop :=
  ∀ (q client : Loc) (key val : GoString) (pr : w64) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isPriorityQueue q client key ∗ etcdReached lo }}
    (App (App (Val (q @!! go.GoType.PointerType PriorityQueue.ty @!! go!"EnqueueUint64")) (Val #val))
      (Val #pr))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (g r : w64), etcdReached r ∗
        seqKeyPutAt [] (key ++ go!"/" ++ _root_.Perennial.fmt.padZeros 5
            (_root_.Perennial.fmt.decimal (uint.Z pr))) k val g r ∗
        ⌜(key ++ go!"/" ++ _root_.Perennial.fmt.padZeros 5
            (_root_.Perennial.fmt.decimal (uint.Z pr)) ++ go!"/") <+: k ∧
          sint.Z lo ≤ sint.Z g ∧ sint.Z g ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial
