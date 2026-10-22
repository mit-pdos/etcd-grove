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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

end defs

end k8s
end EtcdGrove
end Perennial
