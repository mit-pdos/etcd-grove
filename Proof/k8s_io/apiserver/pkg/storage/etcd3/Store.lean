/-
Lean-first (no Rocq counterpart).

# The store (`*etcd3.store`): its predicate and its answers (`notes/k8s-etcd3-plan.md`, phase 4)

- `StoreCfg`: what a store was made with (`New`): the object specification and the contract's
  interface values, the key prefixes, the kubernetes client and the members it talks to, the
  group-resource and metrics tracker it reports to.
- `isStore sp c` (persistent): the store's fields as `New` set them, read-only (the unary paths
  never write them), its client `*kubernetes.Client` (`Kubernetes` is the client itself, as
  `kubernetes.New` sets it) over `New`'s `clientv3.Client` of the members (`isNewClient`,
  sending a write at most once, each member's KV registered), and the contract (`contractOk`).
- `storageErrIs err code key rv`: `err` is a `*storage.StorageError` with these fields (what
  `NewKeyNotFoundError`, `NewKeyExistsError` return); `respIs`: a model answer as the error and
  the object a method leaves.
- `kvWf c σ`: etcd's state is the store's (sorted, `Model.lean`'s `KWf` under the store's
  prefix), what the callers' updates must give at the linearization point (D30i).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Contract
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- **A store's configuration** (see the file header). -/
structure StoreCfg (GF : BundledGFunctors) (Obj : Type) where
  S : ObjSpec GF Obj
  codec : GoInterface
  vi : GoInterfaceOk
  ti : GoInterfaceOk
  di : GoInterfaceOk
  pathPrefix : GoString
  resourcePrefix : GoString
  gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource
  /-- the `*kubernetes.Client` -/
  kc : Loc
  /-- its `clientv3.Client` -/
  cl : Loc
  ms : List (client.SrvAt GF)
  V : client.WEnv GF
  /-- the metrics tracker and its `Get` tracker -/
  mt : Loc
  lt : Loc

/-- The model's prefix: the store's keys (`pathPrefix` and the resource's). -/
def StoreCfg.pfx (c : StoreCfg GF Obj) : GoString := c.pathPrefix ++ c.resourcePrefix

/-- **The store `sp`** (persistent; see the file header). -/
def isStore (sp : Loc) (c : StoreCfg GF Obj) : IProp GF :=
  iprop(⌜sp ≠ null⌝ ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"client" sp ↦□ c.kc ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"codec" sp ↦□ c.codec ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"versioner" sp ↦□
      GoInterface.ok c.vi ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"transformer" sp ↦□
      GoInterface.ok c.ti ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"decoder" sp ↦□
      GoInterface.ok c.di ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"pathPrefix" sp ↦□ c.pathPrefix ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"resourcePrefix" sp ↦□
      c.resourcePrefix ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"groupResource" sp ↦□ c.gr ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"metricsTracker" sp ↦□ c.mt ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.metrics.EtcdMetricsTracker go!"Get" c.mt ↦□
      c.lt ∗ ⌜c.lt ≠ null⌝ ∗
    c.kc ↦□ (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
        #c.kc)) ∗
    isNewClient c.cl (c.ms.map client.SrvAt.addr) c.V ∗
    client.clientWriteOnce c.cl (c.ms.map client.SrvAt.addr) ∗
    ([∗list] x ∈ c.ms, client.kvRegsAt x) ∗
    contractOk c.S c.codec c.vi c.ti c.di)

instance isStore_persistent (sp : Loc) (c : StoreCfg GF Obj) : Persistent (isStore sp c) := by
  unfold isStore; infer_instance

/-- **A `*storage.StorageError`** with these fields (no wrapped error). -/
def storageErrIs (err : GoInterface) (code : w64) (key : GoString) (rv : w64) : IProp GF :=
  iprop(∃ p : Loc, ⌜err = interface.mkOk
      (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #p⌝ ∗
    p ↦□ k8s_io.apiserver.pkg.storage.StorageError.mk code key rv GoInterface.nil)

/-- **A model answer, as the method leaves it** (`err` and the object `out`): an object at a
resource version, the zero object, a key not found or existing (`StorageError`s with codes `1`,
`2`); the other errors (not answered by the unary methods' specs yet) as any error. -/
def respIs {E : Type} (c : StoreCfg GF Obj) (r : KResp Obj E) (err out : GoInterface) : IProp GF :=
  match r with
  | .obj o rv => iprop(⌜err = GoInterface.nil⌝ ∗ c.S.objAt out o (c.S.fmtRV (W64 (rv : Int))))
  | .zero => iprop(⌜err = GoInterface.nil⌝ ∗ c.S.objAt out c.S.zero [])
  | .err (.notFound k rv) =>
    iprop(storageErrIs err (W64 1) k (W64 (rv : Int)) ∗ ∃ o rv', c.S.objAt out o rv')
  | .err (.keyExists k) =>
    iprop(storageErrIs err (W64 2) k (W64 0) ∗ ∃ o rv', c.S.objAt out o rv')
  | .err _ => iprop(⌜err ≠ GoInterface.nil⌝ ∗ ∃ o rv', c.S.objAt out o rv')

/-- **etcd's state is the store's** (D30i): sorted by key, and the store's invariant under its
prefix (`KWf`). -/
def kvWf (c : StoreCfg GF Obj) (σ : KVState) : Prop :=
  σ.kvs.Pairwise etcdKvLess ∧ KWf c.S.dec c.pfx (linkv.absSt σ)

/-- The model state of etcd's state for the store `c`. -/
def StoreCfg.abs (c : StoreCfg GF Obj) (σ : KVState) : KSt Obj :=
  absK c.S.dec c.pfx (linkv.absSt σ)

end defs

end k8s
end EtcdGrove
end Perennial
