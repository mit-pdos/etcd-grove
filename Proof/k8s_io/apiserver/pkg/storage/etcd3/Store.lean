/-
Lean-first (no Rocq counterpart).

# The store (`*etcd3.store`): its predicate and its answers (`notes/k8s-etcd3-plan.md`, phase 4)

- `StoreCfg`: what a store was made with (`New`): the object specification and the contract's
  interface values, the key prefixes, the kubernetes client and the members it talks to, the
  group-resource and metrics tracker it reports to.
- `isStore sp c` (persistent): the store's fields as `New` set them, read-only (the unary paths
  never write them), its client `*kubernetes.Client` (`Kubernetes` is the client itself, as
  `kubernetes.New` sets it) over `New`'s `clientv3.Client` of the members (`isNewClient`,
  sending a write at most once, each member's KV registered, its workload admitting the store's
  writes), the contract (`contractOk`), and the list path's fields (`storeListOk`: the aggregator
  factory, `collectorMux`'s reader pool, the group-resource's UTF-8; stage 7e-2, #15).
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
public import Proof.go_etcd_io.etcd.client.v3.ClientErr
public import GeneratedProof.k8s_io.apimachinery.pkg.runtime.schema
public import GeneratedProof.k8s_io.apiserver.pkg.storage.etcd3.metrics
public import GeneratedProof.k8s_io.apiserver.pkg.storage
public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.AggrDefs
public import Proof.unicode.utf8.Valid
public import Perennial.Proof.sync.RWMutexThreads

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-- **A callback's error as the Go error the store returns** (`validateDeletion`'s, `tryUpdate`'s):
the store returns it unchanged, so a caller that knows its callback's errors (`GoInterface`: the
error itself) can tell them apart from the others. -/
class KUserErr [GooseExts] (E : Type) where
  is : E → GoInterface → Prop

instance [GooseExts] : KUserErr Empty := ⟨fun e _ => nomatch e⟩

instance [GooseExts] : KUserErr GoInterface := ⟨fun e err => err = e⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  /-- the caller's history of etcd's key-values by key and mod revision (D30j) -/
  γh : GName

/-- The model's prefix: the store's keys (`pathPrefix` and the resource's). -/
def StoreCfg.pfx (c : StoreCfg GF Obj) : GoString := c.pathPrefix ++ c.resourcePrefix

/-- The share `q` of the store's `resourceSizeEstimator` field, `nil` (what a `collectorMux` read
lock gives: nothing in the verified programs calls `EnableResourceSizeEstimation`, `store.go:677`). -/
def rseNilR (sp : Loc) (q : Qp) : IProp GF :=
  iprop(structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"resourceSizeEstimator" sp
    ↦{DFrac.own q} (null : Loc))

instance rseNilR_timeless (sp : Loc) (q : Qp) : Timeless (rseNilR (GF := GF) sp q) := by
  unfold rseNilR; infer_instance

instance rseNilR_fractional (sp : Loc) : Fractional (rseNilR (GF := GF) sp) where
  fractional q1 q2 := by
    unfold rseNilR
    exact (typedPointsto_dfractional (GF := GF) _ (null : Loc)).dfractional (DFrac.own q1)
      (DFrac.own q2)

/-- The namespace of the stores' `collectorMux` reader pools. -/
abbrev storePoolN : Namespace := nroot.@"k8sEtcd3StorePool"

/-- **The list path's store fields** (stage 7e-2, #15, D2; persistent): the list error aggregator
factory (`New`'s pick, read-only: `aggrFactoryOk`), `collectorMux`'s reader tokens in a thread pool
(`notes/bounds-plan.md`: a reader borrows one with its thread token) guarding `resourceSizeEstimator
↦ nil`, and the group-resource's labels valid UTF-8 (the metrics' labels, attack R1). -/
def storeListOk (sp : Loc) (c : StoreCfg GF Obj) : IProp GF :=
  iprop(∃ (f : GoFunc) (γp : GName),
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"listErrAggrFactory" sp ↦□ f ∗
    aggrFactoryOk f ∗
    threadPool.isThreadPool storePoolN γp
      (sync.ownRWMutex (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"collectorMux" sp)
        (rseNilR sp)) ∗
    ⌜utf8Valid c.gr.Group' ∧ utf8Valid c.gr.Resource'⌝ ∗
    ⌜prepareKeyM c.resourcePrefix c.resourcePrefix false = some c.resourcePrefix⌝)

instance storeListOk_persistent (sp : Loc) (c : StoreCfg GF Obj) :
    Persistent (storeListOk sp c) := by
  unfold storeListOk; infer_instance

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
    contractOk c.S c.codec c.vi c.ti c.di ∗
    storeListOk sp c)

instance isStore_persistent (sp : Loc) (c : StoreCfg GF Obj) : Persistent (isStore sp c) := by
  unfold isStore; infer_instance

/-- **A `*storage.StorageError`** with these fields (no wrapped error). -/
def storageErrIs (err : GoInterface) (code : w64) (key : GoString) (rv : w64) : IProp GF :=
  iprop(∃ p : Loc, ⌜err = interface.mkOk
      (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #p⌝ ∗
    p ↦□ k8s_io.apiserver.pkg.storage.StorageError.mk code key rv GoInterface.nil)

/-- **An error whose outcome is unknown** (a method's first disjunct: its write, if any, may or may
not have fired): not `nil`, and the client's (`clientErr`, `statusErrOk`, `errCellOk`: the store
returns the client's errors unchanged), an `InternalError` (the transformer's failures, wrapped),
or the codec's own (`ObjSpec.encErr`). None is a `*StorageError` or a callback's error, which a
caller tells apart by type or identity. -/
def unkErr (c : StoreCfg GF Obj) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗
    ((⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err) ∨
      ⌜(∃ ie : k8s_io.apiserver.pkg.storage.InternalError,
          err = interface.mkOk k8s_io.apiserver.pkg.storage.InternalError.ty #ie) ∨
        c.S.encErr err⌝))

instance unkErr_persistent (c : StoreCfg GF Obj) (err : GoInterface) :
    Persistent (unkErr c err) := by
  unfold unkErr; infer_instance

open Iris.ProofMode in
theorem unkErr_ne (c : StoreCfg GF Obj) (err : GoInterface) :
    unkErr (GF := GF) c err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  unfold unkErr
  iintro ⟨%h, -⟩
  ipureintro; exact h

open Iris.ProofMode in
theorem unkErr_client (c : StoreCfg GF Obj) (err : GoInterface) (hn : err ≠ GoInterface.nil)
    (hc : clientErr err) :
    go_etcd_io.etcd.cache.v3.errCellOk err ⊢ go_etcd_io.etcd.cache.v3.statusErrOk err -∗
      unkErr c err := by
  iintro #Hcl #H
  unfold unkErr
  isplitr
  · ipureintro; exact hn
  ileft
  iframe H Hcl
  ipureintro; exact hc

open Iris.ProofMode in
theorem unkErr_internal (c : StoreCfg GF Obj) (ie : k8s_io.apiserver.pkg.storage.InternalError) :
    ⊢ unkErr (GF := GF) c (interface.mkOk k8s_io.apiserver.pkg.storage.InternalError.ty #ie) := by
  unfold unkErr
  isplitr
  · ipureintro; nofun
  iright
  ipureintro; exact .inl ⟨ie, rfl⟩

open Iris.ProofMode in
theorem unkErr_enc (c : StoreCfg GF Obj) (err : GoInterface) (hn : err ≠ GoInterface.nil)
    (he : c.S.encErr err) : ⊢ unkErr (GF := GF) c err := by
  unfold unkErr
  isplitr
  · ipureintro; exact hn
  iright
  ipureintro; exact .inr he

/-- **A model answer, as the method leaves it** (`err` and the object `out`): an object at a
resource version, the zero object, a key not found or existing (`StorageError`s with codes `1`,
`2`), a failed precondition (`invalidErrIs`, code `4`), a callback's error (`KUserErr`), a minimum
resource version above the read's (the error `IsTooLargeResourceVersion` recognizes,
`apierrors.tooLargeErrIs`: a `*apierrors.StatusError`, which no other answer is; stage 7e-2, #20); the other
errors (`rvSetOnCreate`, not answered by the unary methods' specs yet) as any error. -/
def respIs {E : Type} [KUserErr E] (c : StoreCfg GF Obj) (r : KResp Obj E) (err out : GoInterface) : IProp GF :=
  match r with
  | .obj o rv => iprop(⌜err = GoInterface.nil⌝ ∗ c.S.objAt out o (c.S.fmtRV (W64 (rv : Int))))
  | .zero => iprop(⌜err = GoInterface.nil⌝ ∗ c.S.objAt out c.S.zero [])
  | .err (.notFound k rv) =>
    iprop(storageErrIs err (W64 1) k (W64 (rv : Int)) ∗ ∃ o rv', c.S.objAt out o rv')
  | .err (.keyExists k) =>
    iprop(storageErrIs err (W64 2) k (W64 0) ∗ ∃ o rv', c.S.objAt out o rv')
  | .err (.user e) =>
    iprop(⌜err ≠ GoInterface.nil ∧ KUserErr.is e err⌝ ∗ ∃ o rv', c.S.objAt out o rv')
  | .err (.invalidObj k) => iprop(invalidErrIs err k ∗ ∃ o rv', c.S.objAt out o rv')
  | .err (.tooLarge _ _) =>
    iprop(apierrors.tooLargeErrIs err ∗ ∃ o rv', c.S.objAt out o rv')
  | .err _ => iprop(⌜err ≠ GoInterface.nil⌝ ∗ ∃ o rv', c.S.objAt out o rv')

/-- **etcd's state is the store's** (D30i): sorted by key, and the store's invariant under its
prefix (`KWf`). -/
def kvWf (c : StoreCfg GF Obj) (σ : KVState) : Prop :=
  σ.kvs.Pairwise etcdKvLess ∧ KWf c.S.dec c.pfx (linkv.absSt σ)

/-- **A revision's changes** (stage 7b, D2 of `questions.md`): each key the revision wrote
(`some` of its value) or deleted (`none`), each key once. -/
abbrev Changes := List (GoString × Option GoString)

/-- **The state's key-values, seen in the caller's history** (persistent; D30j): the history
`γh` maps each revision to its changes (read-only), which the caller records at each commit; each
key-value of the state is among its mod revision's changes. Two states seen there agree on a key at
a mod revision. -/
def kvSeen (γh : GName) (σ : KVState) : IProp GF :=
  iprop(□ ∀ v : EtcdKv, ⌜v ∈ σ.kvs⌝ → ∃ ch : Changes,
    ghostMapElem γh v.modRev DFrac.discard ch ∗
      ⌜(v.key, some v.value) ∈ ch ∧ (ch.map Prod.fst).Nodup⌝)

instance kvSeen_persistent (γh : GName) (σ : KVState) : Persistent (kvSeen (GF := GF) γh σ) := by
  unfold kvSeen; infer_instance

/-- Two entries of a list with distinct keys and the same key are the same. -/
theorem Changes.eq_of_key {ch : Changes} (hnd : (ch.map Prod.fst).Nodup) {k : GoString}
    {x y : Option GoString} (hx : (k, x) ∈ ch) (hy : (k, y) ∈ ch) : x = y := by
  induction ch with
  | nil => cases hx
  | cons p ch ih =>
    have hnd' := List.nodup_cons.1 hnd
    rcases List.mem_cons.1 hx with hx1 | hx1 <;> rcases List.mem_cons.1 hy with hy1 | hy1
    · rw [← hx1] at hy1; exact (Prod.mk.inj hy1).2.symm
    · subst hx1; exact absurd (List.mem_map_of_mem (f := Prod.fst) hy1) hnd'.1
    · subst hy1; exact absurd (List.mem_map_of_mem (f := Prod.fst) hx1) hnd'.1
    · exact ih hnd'.2 hx1 hy1

/-- **Two states seen in the history agree** on a key-value's value at a mod revision. -/
theorem kvSeen_agree (γh : GName) (σ1 σ2 : KVState) (v1 v2 : EtcdKv) (h1 : v1 ∈ σ1.kvs)
    (h2 : v2 ∈ σ2.kvs) (hk : v1.key = v2.key) (hm : v1.modRev = v2.modRev) :
    kvSeen (GF := GF) γh σ1 ∗ kvSeen γh σ2 ⊢ ⌜v1.value = v2.value⌝ := by
  unfold kvSeen
  iintro ⟨#H1, #H2⟩
  icases H1 $$ %v1 %h1 with ⟨%ch1, #E1, %hc1⟩
  icases H2 $$ %v2 %h2 with ⟨%ch2, #E2, %hc2⟩
  ihave #E1' : ghostMapElem γh v2.modRev DFrac.discard ch1 $$ []
  · rw [← hm]; iexact E1
  ihave %he := ghostMapElem_agree $$ E1' E2
  ipureintro
  subst he
  rw [hk] at hc1
  exact Option.some.inj (Changes.eq_of_key hc1.2 hc1.1 hc2.1)

/-- **A key-value seen in the history has its value in every state seen there**, at its key and
mod revision. -/
theorem kvSeen_same (γh : GName) (σ0 σ : KVState) (kv0 : EtcdKv) (h0 : kv0 ∈ σ0.kvs) :
    kvSeen (GF := GF) γh σ0 ∗ kvSeen γh σ ⊢
      ⌜∀ v ∈ σ.kvs, v.key = kv0.key → v.modRev = kv0.modRev → v.value = kv0.value⌝ := by
  have hv : ∀ v : EtcdKv, kvSeen (GF := GF) γh σ0 ∗ kvSeen γh σ ⊢
      ⌜v ∈ σ.kvs → v.key = kv0.key → v.modRev = kv0.modRev → v.value = kv0.value⌝ := by
    intro v
    by_cases h1 : v ∈ σ.kvs
    · by_cases h2 : v.key = kv0.key
      · by_cases h3 : v.modRev = kv0.modRev
        · iintro ⟨#H0, #H⟩
          ihave %he := kvSeen_agree γh σ0 σ kv0 v h0 h1 h2.symm h3.symm $$ [H0 H]
          · iframe H0 H
          ipureintro
          exact fun _ _ _ => he.symm
        · iintro -; ipureintro; exact fun _ _ h => absurd h h3
      · iintro -; ipureintro; exact fun _ h => absurd h h2
    · iintro -; ipureintro; exact fun h => absurd h h1
  exact (BI.forall_intro hv).trans (BI.pure_forall.2.trans (BI.pure_mono fun h v => h v))

/-- The model state of etcd's state for the store `c`. -/
def StoreCfg.abs (c : StoreCfg GF Obj) (σ : KVState) : KSt Obj :=
  absK c.S.dec c.pfx (linkv.absSt σ)

end defs

/-! ## Pure facts of the abstraction -/

section pure
variable [GooseExts]
variable {Obj : Type} [DecidableEq Obj]

theorem W64_uint_nat (x : w64) : W64 ((uint.nat x : Nat) : Int) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [uint.nat, W64]
  rw [BitVec.toNat_ofInt]
  have := x.isLt
  omega

/-- A prepared key is under the store's prefix. -/
theorem prepareKeyM_prefix (pp rp key k : GoString) (r : Bool) (h : prepareKeyM rp key r = some k) :
    (pp ++ rp) <+: (pp ++ k) := by
  have last : ∀ k0 : GoString, (if rp <+: k0 then some k0 else none) = some k → rp <+: k := by
    intro k0 hk0
    by_cases hp : rp <+: k0
    · rw [ite_eq_left hp] at hk0; cases hk0; exact hp
    · rw [ite_eq_right hp] at hk0; cases hk0
  apply (List.prefix_append_right_inj pp).2
  unfold prepareKeyM at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h <;> exact last _ h

/-- The decoded reading of a stored value: the transformer's data and the codec's object. -/
theorem ObjCodec.dec_some (C : ObjCodec Obj) (v : GoString) (o : Obj) (b : Bool)
    (h : C.dec v = some (o, b)) :
    ∃ d st, C.fromS v = some (d, st) ∧ C.decode d = some o ∧ b = (!st && decide (C.encode o = d)) := by
  unfold ObjCodec.dec at h
  split at h
  · cases h
  · rename_i d st hf
    cases hd : C.decode d with
    | none => simp [hd] at h
    | some o' =>
      simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨d, st, hf, hd, rfl⟩

end pure

section abs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- A key with no key-value has no item. -/
theorem StoreCfg.abs_none (c : StoreCfg GF Obj) (σ : KVState) (k : GoString)
    (h : mvcc.findKey k σ.kvs = none) : (c.abs σ).items k = none := by
  simp [StoreCfg.abs, absK, linkv.absSt, linkv.absM, h]

/-- A stored value under the prefix decodes, in a state of the store. -/
theorem StoreCfg.dec_of_wf (c : StoreCfg GF Obj) (σ : KVState) (hwf : kvWf c σ) (k : GoString)
    (hk : c.pfx <+: k) (v : EtcdKv) (h : mvcc.findKey k σ.kvs = some v) :
    ∃ o b, c.S.dec v.value = some (o, b) := by
  have := hwf.2.1 k (linkv.absVR v) hk (by simp [linkv.absSt, linkv.absM, h])
  obtain ⟨⟨o, b⟩, hob⟩ := Option.isSome_iff_exists.1 this
  exact ⟨o, b, hob⟩

/-- A key's item: its value decoded, at its mod revision. -/
theorem StoreCfg.abs_some (c : StoreCfg GF Obj) (σ : KVState) (k : GoString) (hk : c.pfx <+: k)
    (v : EtcdKv) (h : mvcc.findKey k σ.kvs = some v) (o : Obj) (b : Bool)
    (hd : c.S.dec v.value = some (o, b)) :
    (c.abs σ).items k = some ⟨o, uint.nat v.modRev, b⟩ := by
  simp [StoreCfg.abs, absK, linkv.absSt, linkv.absM, h, hk, itemOf, linkv.absVR, hd]

end abs

end k8s
end EtcdGrove
end Perennial
