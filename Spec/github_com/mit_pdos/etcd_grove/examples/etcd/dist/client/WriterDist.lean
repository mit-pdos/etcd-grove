/- Lean-first (no Rocq counterpart).

`etcdstart.Writer(cli, w, tried, lo, hi)` (`examples/lib/etcdstart/watch.go`) **across machines** (#50
N10a, `notes/etcd-dist-plan.md` §24): `Writer.spec` (`Spec/.../lib/etcdstart/Writer.lean`) with its
client of one process (`cli`'s `KV` field a `*kv` with `isKv api γk false`) replaced by a client of the
cluster's members at other machines (`kvClientAt cl api eps V Γ`, `KVClientDist.lean`; auth off,
`Γ.auth = false`) and `γk := Γ.kv`, so that its `Put`s are `KV_Put_dist`'s. Everything else is
verbatim: the Puts `tried[lo:hi]` in order, each with the caller's write update (one of its persistent
family, fired at most once, its result `QW k v σ`) in a context with the request timeout, each that
returned no error logged in `w` (`wsInvF`) with the caller's fact `OkF` of its record (from `QW` and the
reply's facts: its revision is `σ`'s next, `kvLogOk σ`). One more difference: the log's lock invariant
is `wsInvT w OkF γt` (`wsInvF`, or the token `γt` once the caller has taken the log out), and `Writer`
holds the token `γt` while it runs (so it finds the log): its caller, `writerOp`, returns the log it
reads after `Writer`, which `wsInvF` alone would keep in the lock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev Writer_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (QW : GoString → GoString → KVState → IProp GF) (OkF : wrec → IProp GF) (w : Loc)
    (γt : GName) (tsl : GoSlice) (tried : List wkv) (lo hi : w64),
  Γ.auth = false → (∀ p, Persistent (OkF p)) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length → (∀ x ∈ tried, wkvSizeOk x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ token γt ∗
      kvClientAt cl api eps V Γ ∗ tsl ↦*□ tried ∗
      (□ ∀ (k v : GoString), ⌜(k, v) ∈ tried.map pairOf⌝ -∗
        AU <{ ∃∃ (σ : KVState), etcdKV Γ.kv σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV Γ.kv (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) ∗ ⌜kvRoom σ⌝,
            COMM QW k v σ }>) ∗
      (□ ∀ (k v : GoString) (σ : KVState), QW k v σ -∗ ⌜σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ⌝ -∗
        OkF ⟨W64 ((σ.rev + 1 : Nat) : Int), k, v⟩) ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" w)
        (wsInvT w OkF γt) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writer))
      (Val #cl)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); levelTok 0 ∗ token γt }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
