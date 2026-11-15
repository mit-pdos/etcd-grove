/-
`(*store).pagedChunks(ctx, keyPrefix, opts, withRev, limit, continueKey)` (`k8s.io/apiserver/pkg/
storage/etcd3/store.go:881-920`): the iterator over a paginated list's pages (`pagesOk`). Each page
is a `getList` read (`store.getList.spec`): the first with `Q`'s update at `withRev` (`0`: the
latest), the later ones with `P σ`'s at the first page's revision, from the last key and `"\x00"`,
the limit doubled up to `maxLimit`; an error goes to `listReadError`. Proved (stage 7e-2,
`notes/k8s-7e-2-draft.md` §3.5 with B5 (a)). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

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
abbrev store.pagedChunks.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (kp : GoString)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (rev0 lim0 : w64)
    (Q : w64 → KVState → IProp GF) (P : KVState → KVState → IProp GF),
  kp.length ≤ opKeyMax → 0 ≤ sint.Z rev0 → 0 ≤ sint.Z lim0 → opts.Predicate'.Continue' = [] →
  (∃ k, prepareKeyM c.resourcePrefix c.resourcePrefix false = some k ∧
    (c.pathPrefix ++ k).length ≤ opKeyMax) →
  (∀ R σ, Q R σ ⊢ ⌜kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ R σ σ', Q R σ ∗ P σ σ' ⊢ ⌜kvSameHist σ σ' ∧ σ.rev ≤ σ'.rev⌝) →
  kp ≠ [] → (∀ x ∈ c.ms, noRefusalAt x.addr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"pagedChunks")) (Val #(GoInterface.ok ci)))
      (Val #kp)) (Val #opts)) (Val #rev0)) (Val #lim0)) (Val #([] : GoString)))
  {{ (f : GoFunc), RET #f; pagesOk c f kp opts.Recursive' rev0 lim0 Q P }}

end spec

end k8s
end EtcdGrove
end Perennial
