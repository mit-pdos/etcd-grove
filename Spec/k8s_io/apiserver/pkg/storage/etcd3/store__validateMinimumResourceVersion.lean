/-
`(*store).validateMinimumResourceVersion(minimumResourceVersion, actualRevision)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go:1286`): for a minimum `m` the versioner parses to `n`
(`""` parses to `0`, `ObjCodec.parse_empty`), `nil` if `n` is at most the revision, else
`NewTooLargeResourceVersionError(n, rev, 0)`, a `*apierrors.StatusError`. Lean-first (no Rocq
counterpart). Stage 7b of `notes/k8s-etcd3-plan.md` (before: `""` only).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.validateMinimumResourceVersion.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (m : GoString) (n rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ⌜c.S.parseRV m = some n⌝ }}
    (App (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
      go!"validateMinimumResourceVersion")) (Val #m)) (Val #rev))
  {{ (err : GoInterface), RET #err;
      ⌜if uint.nat rev < uint.nat n then ∃ l : Loc, err = interface.mkOk
          (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l
        else err = GoInterface.nil⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
