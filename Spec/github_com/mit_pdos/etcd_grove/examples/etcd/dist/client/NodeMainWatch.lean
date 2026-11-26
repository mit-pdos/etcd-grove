/- Lean-first (no Rocq counterpart).

`NodeMain(w, c, addr, eps)` (`examples/etcd/dist/client/nodes.go`) **for a watch or cache workload** (#50 N10a,
`notes/etcd-dist-plan.md` §24; cache since F8: the two kinds share the arm): writer machine `c`'s client of the members' endpoints rotated by `c`
(`newClient(Rotate(eps, c))`; if it fails, `NodeMain` returns), then `remote.ServeClient` at `addr` with
`writerOp` and `writerCodec`, which never returns. M1's `NodeMain.spec` is the kv arm's; this is the watch
arm's (kinds `Watch`, 1, and `Cache`, 2); F8's full `NodeMain.spec` applies it to those kinds.

**The triple:** from the writer machine's share at the rotated endpoints (`nodeWatchPre`: its level
token, a view with auth off whose members serve every endpoint, the writer service's protocols at
`addr`; `WriterWire.lean`) and `Rotate`'s bound, `NodeMain` does not panic (it returns only when its
client fails to connect).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev NodeMainWatch.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (w : Workload) (c : w64) (addr : GoString) (eps : GoSlice)
    (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜(w.kind = W64 1 ∨ w.kind = W64 2) ∧
        (0 ≤ sint.Z c → sint.Z c < sint.Z w.clients → sint.Z c + epsL.length ≤ 2 ^ 63)⌝ ∗
      eps ↦*□ epsL ∗ (⌜0 ≤ sint.Z c ∧ sint.Z c < sint.Z w.clients ∧ epsL ≠ []⌝ -∗
        nodeWatchPre addr (rotateL epsL (sint.nat c))) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain))
      (Val #w.val)) (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
