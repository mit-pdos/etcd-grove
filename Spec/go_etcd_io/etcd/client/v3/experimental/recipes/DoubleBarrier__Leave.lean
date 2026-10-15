/-
`recipes.(*DoubleBarrier).Leave()` (`client/v3/experimental/recipes/double_barrier.go`). Lean-first (no Rocq
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`b.Leave()`**, with a key `st` with the prefix `key/waiters` in `myKey` (`Leave` without a
key is a nil dereference unless no waiter is left), knowing etcd has reached `lo`: see
`leaveResult`: `nil` means the key absent at some revision at least `lo`, or its record already
deleted by the caller. The key's `KV` may become nil (its `Delete`). -/
abbrev DoubleBarrier.Leave.spec : Prop :=
  ∀ (b s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (key : GoString)
    (count : w64) (ek : Loc) (st : RemoteKVSt) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isDoubleBarrier b s γ client id key count ∗
      dbMyKey b (key ++ go!"/") (some (ek, st)) ∗ etcdReached lo ∗
      ⌜key ++ go!"/waiters" <+: st.key⌝ }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"Leave")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (∃ kv' : GoInterface, dbMyKey b (key ++ go!"/") (some (ek, { st with kv := kv' }))) ∗
      leaveResult (key ++ go!"/") st lo err }}

end spec

end recipes
end EtcdGrove
end Perennial
