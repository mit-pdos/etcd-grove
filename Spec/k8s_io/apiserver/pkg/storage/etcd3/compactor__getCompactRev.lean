/-
`(*compactor).getCompactRev(ctx)` (`k8s.io/apiserver/pkg/storage/etcd3/compact.go`): the watch
loop's read of the compactors' key (Q1 (b) of `notes/k8s-compactor-plan.md`, the user's approval
of D2 2026-11-04; the shapes in `CompactorDefs.lean`). Lean-first (no Rocq counterpart).

`Get(ctx, compact_rev_key)` through the client's KV (`clientKvOk`) with the caller's read update
(`keyReadOk`); the key's value, if present, parsed (`ParseInt`); the header's revision. On success,
the value parsed is a compaction revision (`recRevOk`: the key holds `keyValOk` values, `0` if
absent) and the revision read is at least `1` (`keyHistOk`'s): where the loop's watch starts. The
error is one `fmt` formats by its `Error()` (`fmt.argOk`: `fmt.Errorf`'s; klog-args-fix, 2026-11-14,
for the caller's `klog.Errorf`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Spec.fmt.Errorf

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

/-- See the file header. -/
abbrev compactor.getCompactRev.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [sync.Assumptions]
    (c cl : Loc) (γk : KVNames) (recorded : w64 → IProp GF) (γc : CompactorNames)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      compactorCore c cl γk recorded γc ∗ clientKvOk cl γk ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ keyReadOk γk recorded }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"getCompactRev")) (Val #(GoInterface.ok ci)))
  {{ (cr cur : w64) (err : GoInterface), RET (PairV (PairV #cr #cur) #err);
      (fmt.argOk err ∗ ⌜err ≠ GoInterface.nil⌝) ∨
        (⌜err = GoInterface.nil ∧ 1 ≤ sint.Z cur⌝ ∗ recRevOk γk recorded cr) }}

end spec

end k8s
end EtcdGrove
end Perennial
