/-
`(*store).GuaranteedUpdate(ctx, key, destination, ignoreNotFound, preconditions, tryUpdate,
cachedExistingObject)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

An update, retried on conflicts: with the caller's updates at the members (`k8sAuRW`, D30n:
persistent, firing as a plain read any number of times, and once as the linearization point,
handing the caller's timeless token `W` back), its outcome is `correctness.Model`'s `update` with
the canonical bit (D30g, `updOut`): at the state the update fired at as the linearization point
(`Φ σ`): the write (`destination` the result at the new revision), or a read-like answer (the no-op
of an unchanged canonical object, "not found", a failed precondition, `tryUpdate`'s error, nothing
changed); or an error
(the client's, or the codec's or transformer's). `tryUpdate` is the
caller's callback, answering `f` (`tryUpdateOk`).

`ignoreNotFound` (`ign`) runs `tryUpdate` on the zero object at resource version `0` for an absent
key (the model's `update`, which creates it). The preconditions `pp` hold `pr` (`preAt`; `nil`:
none), checked as the model's `pre` (`ObjCodec.preOk`). The cached object `cx` is `nil` or one the
key held at its resource version `r` (`cachedOk`); with one, the store runs the preconditions and
`tryUpdate` on it, and if the result encodes as it does, re-reads the key and returns (or rewrites)
what it finds without running them again, so the spec asks (D1, a scope premise, the user's choice
(a) for the driver, `notes/k8s-etcd3-plan.md` "7b: Draft, the cached no-op"): no resource version
precondition, and a `tryUpdate` that does not depend on the resource version
(`issues/k8s-etcd3-cached-noop-skips-preconditions.md`). For now the key is valid; `tryUpdate` sets
no TTL (D30d).

**The written result fits etcd's request limit** (`notes/decisions.md`, "GuaranteedUpdate's size
premise"): the premise bounds `tryUpdate`'s result `o'` (`storedSizeOk`) only where the store
writes it, as Go does: `o'` from the object `o` decoded from a stored value `v` (the transformer's
data `d`, stale or not), when that reading is stale or `o'`'s encoding differs from `d` (Go's
no-op skip is `!origState.stale && bytes.Equal(data, origState.data)`). The value read is within
etcd's limit (`v.length ≤ etcdKeyMax`, the server's `etcdState_vals`), which a caller whose result
grows the value boundedly uses. With `ignoreNotFound` the zero object's result is written when
the key is absent, and with a cached object its result when its encoding differs from the
object's (the store's data for it): the two other size premises.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps
public import Proof.k8s_io.apiserver.pkg.storage.Defs

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
abbrev store.GuaranteedUpdate.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (dest : GoInterface) (o0 : Obj)
    (rv0 : GoString) (ign : Bool) (pp : Loc) (pr : KPre) (cx : GoInterface)
    (ca : Option (Obj × w64)) (f : Obj → Nat → Except E Obj) (uf : GoFunc) (W : IProp GF)
    [Timeless W] (Φ : KVState → IProp GF) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ⌜prepareKeyM c.resourcePrefix key false = some k ∧ (c.pathPrefix ++ k).length ≤ opKeyMax ∧
        -- the size premise: a result the store writes fits (see the file header)
        (∀ (v d : GoString) (stl : Bool) (o : Obj) (n : Nat) (o' : Obj), v.length ≤ etcdKeyMax →
          c.S.fromS v = some (d, stl) → c.S.decode d = some o → f o n = .ok o' →
          (stl = true ∨ c.S.encode o' ≠ d) → c.S.storedSizeOk o') ∧
        (ign = true → ∀ o', f c.S.zero 0 = .ok o' → c.S.storedSizeOk o') ∧
        (∀ o r o', ca = some (o, r) → f o (uint.nat r) = .ok o' → c.S.encode o' ≠ c.S.encode o →
          c.S.storedSizeOk o') ∧
        -- the cached object's scope premise (D1; `issues/k8s-etcd3-cached-noop-skips-preconditions.md`)
        (∀ o r, ca = some (o, r) → pr.rv = none ∧ ∀ n, f o n = f o (uint.nat r))⌝ ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt dest o0 rv0 ∗ preAt pp pr ∗
      cachedOk c (c.pathPrefix ++ k) cx ca ∗ W ∗
      ([∗list] x ∈ c.ms,
        k8sAuRW x.γr.kv c (updStep (c.pathPrefix ++ k) ign c.S.zero (c.S.preOk pr) f) W Φ) ∗
      tryUpdateOk c f uf }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"GuaranteedUpdate"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #dest)) (Val #ign)) (Val #pp)) (Val #uf))
      (Val #cx))
  {{ (err : GoInterface), RET #err;
      updOut c (c.pathPrefix ++ k) ign c.S.zero (c.S.preOk pr) f Φ err dest }}

end spec

end k8s
end EtcdGrove
end Perennial
