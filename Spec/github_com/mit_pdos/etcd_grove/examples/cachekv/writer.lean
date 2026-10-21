/- Lean-first (no Rocq counterpart).

`writer(cli, w, tried, lo, hi)` (cachekv.go): the Puts `tried[lo:hi]` through `New`'s client
configured for one attempt, each with the writer's update (`put_au`: the workload lets the
client deposit the plan's puts), logging each that returned no error in `w` with `okFact`
(`wsInv`, the log's lock invariant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Writes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.cachekv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- See the file header. -/
abbrev writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString) (V : client.WEnv GF)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (w : Loc) (tsl : GoSlice)
    (tried : List ckv) (lo hi : w64) (P : List (GoString × GoString)) (γm : GName),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  γr.kv.wl = watchkv.workload P → tried.map pairOf = P →
  0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl ep V ∗ clientKVOnce cl ep ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
      tsl ↦*□ tried ∗ ckKV γr γm ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.cachekv.writes go!"mu" w)
        (wsInv w E) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.writer))
      (Val #cl)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); True }}

end spec

end cachekv
end EtcdGrove
end Perennial
