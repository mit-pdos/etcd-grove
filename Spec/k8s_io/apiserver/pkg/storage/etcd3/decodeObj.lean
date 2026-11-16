/-
`decodeObj(codec, versioner, data, rev)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:894-910`) of
data that decodes to `o` (the watch path's values do, under `kvWfHist`: the decode error and its
`fatalOnDecodeError` panic are not reached): `runtime.Decode` (`watchContractOk`) then the versioner's
`UpdateObject`: the object `o` at the resource version `rev`, no error. Proved (k8s 7f-5a-P step 3).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

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
abbrev decodeObj.spec : Prop :=
  ∀ (Obj : Type) (S : ObjSpec GF Obj) (W : WatchSpec Obj) (codec : GoInterface) (vi : GoInterfaceOk)
    (dsl : GoSlice) (d : GoString) (o : Obj) (rev : w64),
  S.decode d = some o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      watchContractOk S W codec ∗ versionerOk S vi ∗ dsl ↦*□ d }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.decodeObj)) (Val #codec))
      (Val #(GoInterface.ok vi))) (Val #dsl)) (Val #rev))
  {{ (x err : GoInterface), RET (PairV #x #err); ⌜err = GoInterface.nil⌝ ∗ S.objAt x o (S.fmtRV rev) }}

end spec

end k8s
end EtcdGrove
end Perennial
