/-
`(*kv).Compact(ctx, rev)` by a client of members at other machines, at the cluster view (`notes/etcd-dist-plan.md` §18.4; a
trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/KVCompactDist.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`KV_Compact_dist`: `(*kv).Compact(ctx, rev)` across machines** (mirrors `kv.Compact.spec`,
server side `etcdCompactSpecW`): a cluster in compaction mode, the caller knowing the KV has reached
`rev` plus the retention (`kvRevLbZ`, which a `Put`'s reply gives). Any auth mode is allowed by
`kv.Compact.spec`; the deployment's compaction mode excludes auth on (`NewServer`'s `cmp = true →
on = false`). -/
abbrev KV_Compact_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (rev : w64),
  1 ≤ sint.Z rev → Γ.kv.cmp = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientAt cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ kvRevLbZ Γ.kv (sint.Z rev + Γ.kv.cret) }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Compact")) (Val #(GoInterface.ok ctx))) (Val #rev)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : CompactRespM, compactRespMsg resp m) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
