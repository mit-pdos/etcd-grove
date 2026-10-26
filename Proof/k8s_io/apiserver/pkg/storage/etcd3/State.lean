/-
Lean-first (no Rocq counterpart).

# The store's `*objState` (`store.go`'s `objState`; phase 4 of `notes/k8s-etcd3-plan.md`)

What the store knows of a key between its read and its conditional write (`Delete`,
`GuaranteedUpdate`): the object (decoded into a fresh object of the store's type), the key-value's
mod revision, the transformed data and its staleness, and whether it was just read from etcd
(`current`).

- `OState`: those, as one record of pure values;
- `ownState c st s`: the `*objState` `st` holds `s` (its object owned, its data read-only, its
  `meta` the `ResponseMeta` with the resource version);
- `stOfKv c kv s`: `s` is what the store reads of the key-value `kv` (`stateFromEtcdResponse`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-- **An `objState`'s contents** (see the file header). -/
structure OState (Obj : Type) where
  o : Obj
  rev : w64
  data : GoString
  current : Bool
  stale : Bool

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- **The `*objState` `st` holds `s`** (see the file header). -/
def ownState (c : StoreCfg GF Obj) (st : Loc) (s : OState Obj) : IProp GF :=
  iprop(∃ (x : GoInterface) (m : Loc) (dsl : GoSlice), ⌜st ≠ null⌝ ∗
    st ↦ k8s_io.apiserver.pkg.storage.etcd3.objState.mk x m s.rev dsl s.current s.stale ∗
    c.S.objAt x s.o (c.S.fmtRV s.rev) ∗ dsl ↦*□ s.data ∗
    m ↦ k8s_io.apiserver.pkg.storage.ResponseMeta.mk (W64 0) s.rev)

/-- **`s` is the store's reading of the key-value `kv`**: its mod revision, the transformer's
data and staleness of its value, the object the data decodes to, just read. -/
def stOfKv (c : StoreCfg GF Obj) (kv : EtcdKv) (s : OState Obj) : Prop :=
  s.rev = kv.modRev ∧ c.S.fromS kv.value = some (s.data, s.stale) ∧
    c.S.decode s.data = some s.o ∧ s.current = true

/-- **The `*objState` `st` holds `s`, its object `x` given away** (to `tryUpdate`). -/
def ownStateX (c : StoreCfg GF Obj) (st : Loc) (s : OState Obj) (x : GoInterface) : IProp GF :=
  iprop(∃ (m : Loc) (dsl : GoSlice), ⌜st ≠ null⌝ ∗
    st ↦ k8s_io.apiserver.pkg.storage.etcd3.objState.mk x m s.rev dsl s.current s.stale ∗
    dsl ↦*□ s.data ∗ m ↦ k8s_io.apiserver.pkg.storage.ResponseMeta.mk (W64 0) s.rev)

open Iris.ProofMode in
theorem ownState_split (c : StoreCfg GF Obj) (st : Loc) (s : OState Obj) :
    ownState c st s ⊢ ∃ x, ownStateX c st s x ∗ c.S.objAt x s.o (c.S.fmtRV s.rev) := by
  unfold ownState ownStateX
  iintro ⟨%x, %m, %dsl, %h, Hst, Hobj, #Hdsl, Hm⟩
  iexists x
  iframe Hobj
  iexists m, dsl
  iframe Hst Hdsl Hm
  ipureintro; exact h

/-- **The store's answer for the key `key` at the state `σ`** (`stateFromEtcdResponse` of a read
at `σ`): "not found" at `σ`'s revision, or a new `*objState` of its key-value. -/
def stAt (c : StoreCfg GF Obj) (key : GoString) (σ : KVState) (st : Loc) (err : GoInterface) :
    IProp GF :=
  match mvcc.findKey key σ.kvs with
  | none => iprop(⌜st = null⌝ ∗ storageErrIs err (W64 1) key (W64 (σ.rev : Int)))
  | some kv => iprop(⌜err = GoInterface.nil⌝ ∗ ∃ s, ownState c st s ∗ ⌜stOfKv c kv s⌝)

/-- **`getCurrentState`'s closure `f`** (persistent: callable at each retry): given, for the call,
the caller's single-use maker of a read update at each member for the response's pair
(`Client.Get.spec`'s, D30n), it reads the key through the client and answers `stAt` at the state
`σ` the update fired at, with `R` at `σ`'s pair (`rdPair`'s parts), or fails with the client's
error. -/
def getStateOk (c : StoreCfg GF Obj) (key : GoString) (R : w64 → w64 → KVState → IProp GF)
    (f : GoFunc) : IProp GF :=
  iprop(□ ∀ Ψ : val → IProp GF,
    (∀ R0 m, |==> □ [∧list] x ∈ c.ms, ⌜R R0 m = fun _ => iprop(True)⌝ ∨
      kvReadAu x.γr.kv (R R0 m)) -∗
    ▷ (∀ (st : Loc) (err : GoInterface),
        (unkErr c err ∨ ∃ σ, □ R (W64 (σ.rev : Int)) (kubernetes.modAt key σ) σ ∗
          stAt c key σ st err) -∗ Ψ (PairV #st #err)) -∗
    WP (App (Val #f) (Val #())) {{ Ψ }})

instance getStateOk_persistent (c : StoreCfg GF Obj) (key : GoString) (R : w64 → w64 → KVState → IProp GF)
    (f : GoFunc) : Persistent (getStateOk c key R f) := by
  unfold getStateOk; infer_instance

end defs

end k8s
end EtcdGrove
end Perennial
