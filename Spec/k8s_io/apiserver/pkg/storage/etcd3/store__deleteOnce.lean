/-
`(*store).deleteOnce(ctx, key, out, origState, v, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

One attempt at deleting the prepared key `key`: `OptimisticDelete(key, origState.rev,
GetOnFailure: true)` through the client, with the caller's updates at the members (`k8sAuRW`,
D30n: the linearization point hands the caller's token `W`) and `origState` a state `s` at a mod
revision (not `0`) from a read or from the cached object (`stFrom`, stage 7b), on which the
preconditions (`pre`) and `validateDeletion` (`validate`) passed. A key-value at `s`'s mod revision
has `s`'s object (the caller's history, D30j, `stFrom_item`), so the transaction is the model's
`delete` when it succeeds. Its outcomes:

- an error of the client (the update fired at most once);
- success: the update fired as the write at `σ`, `out` the deleted object at the next revision (the
  model's answer, `respIs`);
- a conflict: the update fired as a read at the state `σ` the transaction saw, the new state is
  the store's reading of the key there (`stAt`: "not found", or its key-value), and the update was
  the linearization point there (`Φ σ`) if the model's step is the identity at `σ`
  (`stepHand`), else `W` is back.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

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
abbrev store.deleteOnce.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (out : GoInterface) (o0 : Obj)
    (rv0 : GoString) (st : Loc) (s : OState Obj)
    (v : _root_.Perennial.reflect.Value) (p : Loc) (pre : Obj → Nat → Bool)
    (validate : Obj → Nat → Option E) (W : IProp GF) (Φ : KVState → IProp GF),
  c.pfx <+: key → key.length ≤ opKeyMax →
  s.rev ≠ W64 0 →
  pre s.o (uint.nat s.rev) = true →
  validate s.o (uint.nat s.rev) = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ ownState c st s ∗ stFrom c key s ∗
      c.S.objAt out o0 rv0 ∗ ⌜reflectM.reflElem v c.S.objTy p⌝ ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (delStep key pre validate) W Φ) }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"deleteOnce")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #out)) (Val #st)) (Val #v)) (Val #false))
  {{ (st' : Loc) (ok : Bool) (err : GoInterface), RET (PairV (PairV #st' #ok) #err);
      (unkErr c err ∗ ∃ o rv, c.S.objAt out o rv) ∨
      (⌜ok = true ∧ err = GoInterface.nil⌝ ∗ ∃ σ, Φ σ ∗
        respIs c ((c.abs σ).delete key pre validate).2 err out) ∨
      (⌜ok = false⌝ ∗ c.S.objAt out o0 rv0 ∗ ∃ σ, rdFacts c σ ∗ stAt c key false σ st' err ∗
        (if stepHand c (delStep key pre validate) σ then Φ σ else W)) }}

end spec

end k8s
end EtcdGrove
end Perennial
