/-
`(*store).getStateFromObject(obj, current)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:1239`)
with `current = false`, on `GuaranteedUpdate`'s `cachedExistingObject`: an object holding `o` at
resource version `fmtRV r` gives a new `*objState` of `o` at `r`, its data `o`'s encoding (the
versioner's `ObjectResourceVersion`, `PrepareObjectForStorage`, `runtime.Encode`, `UpdateObject`,
`versionerOk`/`encodeOk`), not current, not stale; or the codec's error. Lean-first (no Rocq
counterpart; stage 7b of `notes/k8s-etcd3-plan.md`).
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.getStateFromObject.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (x : GoInterface) (o : Obj)
    (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      c.S.objAt x o (c.S.fmtRV r) }}
    (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"getStateFromObject"))
      (Val #x)) (Val #false))
  {{ (st : Loc) (err : GoInterface), RET (PairV #st #err);
      (⌜err = GoInterface.nil⌝ ∗ ownState c st ⟨o, r, c.S.encode o, false, false⟩) ∨
      unkErr c err }}

end spec

end k8s
end EtcdGrove
end Perennial
