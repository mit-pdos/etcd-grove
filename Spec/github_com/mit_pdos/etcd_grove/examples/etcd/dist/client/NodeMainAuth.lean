/- Lean-first (no Rocq counterpart).

`NodeMain(w, c, addr, eps)` (`examples/etcd/dist/client/nodes.go`) **for an auth workload** (#50 F7 S8, kind
`Auth`, 5): principal machine `c` (`NodeCount` is `deployment.AuthPrincipals`, 4) runs `remote.ServeClient` at
`addr` with `principalOp` and `principalCodec`, its client closure answering the members' endpoints `eps`
themselves (not rotated: each call makes its principal's client, `principalClient`); it never returns. F8's
`NodeMain.spec` reaches this arm with a `False` share (D2); this is the arm's triple, as `NodeMainWatch.spec`
is the writers'.

**The triple:** from the principal machine's share at the endpoints (`nodeAuthPre`: its level token, an
auth-on view whose members serve every endpoint, the principal service's protocols at `addr`;
`PrincipalWire.lean`), `NodeMain` does not panic (it returns only when `c` or `eps` fails the guard).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Defs
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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev NodeMainAuth.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (w : Workload) (c : w64) (addr : GoString) (eps : GoSlice)
    (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜w.kind = W64 5⌝ ∗
      eps ↦*□ epsL ∗ (⌜0 ≤ sint.Z c ∧ sint.Z c < 4 ∧ epsL ≠ []⌝ -∗ nodeAuthPre addr epsL) }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMain))
      (Val #w.val)) (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
