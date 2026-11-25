/-
`(*kv).Get(ctx, key, opts...)` by a client of members at other machines, at the cluster view (`notes/etcd-dist-plan.md` §18.4; a
trust-boundary axiom until #24's S2 client side: `Proof/.../etcd/dist/KVGetDist.lean`). Lean-first (no Rocq
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

/-- **`KV_Get_dist`: `(*kv).Get(ctx, key, opts...)` across machines** (mirrors `kv.Get.spec`,
server side `etcdRangeSpecEW`/`etcdRangeSpecW`): `kv.Get.spec` with `isKv` replaced by `kvClientAt`
at `Γ`, `γ := Γ.kv`. Any auth mode: a read is retried only when immutable (`Unavailable`), so the
read update stays persistent as in `kv.Get.spec`. -/
abbrev KV_Get_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString)
    (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientAt cl api eps V Γ ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAtRes opts_sl opts R ∗ R ∗
      sortNamesIf (opGetModel key opts).base.sortSet ∗
      ⌜¬ opGetPanics opts ∧ (opGetModel key opts).t = W64 1⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜(rangeWireOf (opGetModel key opts)).base.serializable = false⌝ ∗
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV Γ.kv σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>)) ∗
      ⌜opSizeOk (opGetModel key opts)⌝ }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ (R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          (if (rangeWireOf (opGetModel key opts)).base.serializable then iprop(True) else iprop(□ Q σ)) ∗
          ⌜sint.Z (rangeWireOf (opGetModel key opts)).base.rev ≤ (σ.rev : Int) ∧
            txn.srvRangeOk (rangeWireOf (opGetModel key opts))
              (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs m.kvs m.more ∧
            m.count = txn.srvCount (rangeWireOf (opGetModel key opts))
              (σ.at (σ.readRev (rangeWireOf (opGetModel key opts)).base.rev)).kvs true ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧ kvLogOk σ⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝)) }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
