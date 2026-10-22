/- Lean-first (no Rocq counterpart).

`writer(cli, w, tried, lo, hi)` (watchkv.go): the Puts `tried[lo:hi]` through `New`'s client
that sends a write at most once (`clientWriteOnce`), each with the writer's update (`put_au`: the workload lets the
client deposit the plan's puts), logging each that returned no error in `w` with `okFact`
(`wsInv`, the log's lock invariant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Writes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.watchkv

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

/-- See the file header. -/
abbrev writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString) (V : client.WEnv GF)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (w : Loc) (tsl : GoSlice)
    (tried : List wkv) (lo hi : w64) (P : List (GoString × GoString)),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  γr.kv.wl = workload P → tried.map pairOf = P →
  0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.watchkv ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl [ep] V ∗ EtcdGrove.client.clientWriteOnce cl [ep] ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
      tsl ↦*□ tried ∗ wkKV γr ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.watchkv.writes go!"mu" w)
        (wsInv w E) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.watchkv.writer))
      (Val #cl)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); True }}

end spec

end watchkv
end EtcdGrove
end Perennial
