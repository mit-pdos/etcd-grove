/-
`(*kv).Delete(ctx, key, opts...)` by a client of members at other machines, at the cluster view (`notes/etcd-dist-plan.md` §18.4; a
trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/KVDeleteDist.lean`). Lean-first (no Rocq
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

/-- **`KV_Delete_dist`: `(*kv).Delete(ctx, key, opts...)` across machines** (mirrors
`kv.Delete.spec` at `dup = false`, server side `etcdDeleteSpecW`), auth off. -/
abbrev KV_Delete_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientAt cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ opDeletePanics key opts ∧ (opDeleteModel key opts).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key opts)).base.rangeEnd ≠ [W8 0]⌝ ∗
      AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ) ∗
           ⌜kvRoom σ⌝, COMM Q σ }> ∗
      ⌜opSizeOk (opDeleteModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
        ⌜m.deleted = W64 ((rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts))).length : Int) ∧
          m.prevs = (if (deleteWireOf (opDeleteModel key opts)).base.prevKV then
            rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts)) else []) ∧
          m.hdr.revision = W64 ((kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ).rev : Int) ∧
          kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ)⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
