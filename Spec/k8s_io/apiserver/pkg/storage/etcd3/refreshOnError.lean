/-
`refreshOnError(st, err, getCurrentState)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:128`; phase 4
of `notes/k8s-etcd3-plan.md`, generalized in stage 7b). Lean-first (no Rocq counterpart).

For a state just read from etcd (`current`): the state and the error, unchanged (the closure is not
called; the state's object is not read, `ownStateX`). For a state from a cached object (not
current): the old state is dropped and the closure `f` called (`getStateOk`, with the caller's
maker of read updates for its read); its error is answered, or its state `st'` at the state `σ`
its read fired at (`stAt`'s error `e0`, "not found" without `ign`) with the error `err` again if
the read is at the cached state's revision (the cached data was not stale: the key's mod
revision there, `modAt`, `0` if absent), else `nil` (retry).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.State

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev refreshOnError.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (c : StoreCfg GF Obj) (st : Loc) (s : OState Obj)
    (err : GoInterface) (f : GoFunc) (x : GoInterface) (key : GoString) (ign : Bool)
    (R : w64 → w64 → KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ ownStateX c st s x ∗
      (if s.current then iprop(True) else iprop(getStateOk c key ign R f ∗
        ∀ R0 m, |==> □ [∧list] y ∈ c.ms, ⌜R R0 m = fun _ => iprop(True)⌝ ∨
          kvReadAu y.γr.kv (R R0 m))) }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.refreshOnError)) (Val #st))
      (Val #err)) (Val #f))
  {{ (st' : Loc) (err' : GoInterface), RET (PairV #st' #err');
      if s.current then iprop(⌜st' = st ∧ err' = err⌝ ∗ ownStateX c st s x)
      else iprop(unkErr c err' ∨ ∃ (σ : KVState) (e0 : GoInterface),
        □ R (W64 (σ.rev : Int)) (kubernetes.modAt key σ) σ ∗
        ⌜∀ v ∈ σ.kvs, v.value.length ≤ 2 ^ 27⌝ ∗ stAt c key ign σ st' e0 ∗
        ⌜err' = if e0 = GoInterface.nil ∧ kubernetes.modAt key σ = s.rev then err else e0⌝) }}

end spec

end k8s
end EtcdGrove
end Perennial
