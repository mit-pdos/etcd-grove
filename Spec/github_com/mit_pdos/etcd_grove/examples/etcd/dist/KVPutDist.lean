/-
`(*kv).Put(ctx, key, val, opts...)` by a client of members at other machines, at the cluster view (`notes/etcd-dist-plan.md` §18.4; a
trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/KVPutDist.lean`). Lean-first (no Rocq
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

/-- **`KV_Put_dist`: `(*kv).Put(ctx, key, val, opts...)` across machines** (mirrors the proved
client spec `kv.Put.spec` at `dup = false`, whose server side is `etcdPutSpecW`): `kv.Put.spec` with
`isKv api γ false` replaced by `kvClientAt` at `Γ` and `γ := Γ.kv`, for a cluster with auth off; the
error arm without `kvErr` (nothing is claimed of a remote call's error). -/
abbrev KV_Put_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (key val : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  Γ.auth = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientAt cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ (opPutModel key val opts).putPanics ∧ (opPutModel key val opts).t = W64 2 ∧
        (putWireOf (opPutModel key val opts)).leaseID = W64 0⌝ ∗
      AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv (kvOpStep (.put (putWireOf (opPutModel key val opts))) σ) ∗ ⌜kvRoom σ⌝,
           COMM Q σ }> ∗
      ⌜opSizeOk (opPutModel key val opts)⌝ }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
          m.prev = (if (putWireOf (opPutModel key val opts)).base.prevKV then
            (σ.store.lookup (putWireOf (opPutModel key val opts)).key).map
              (KVRec.toKv (putWireOf (opPutModel key val opts)).key) else none) ∧
          kvRevFits (σ.rev + 1) ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.put (putWireOf (opPutModel key val opts))) σ)⌝ ∗
        kvRevLb Γ.kv m.hdr.revision) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
