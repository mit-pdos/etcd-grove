/- Lean-first (no Rocq counterpart).

`writerOp(sys, in)` (`examples/etcd/dist/client/nodes.go`): **a writer machine's call** of the watch
workload (#50 N10a, `notes/etcd-dist-plan.md` §24), the operation its `remote.ServeClient` runs for each
of the orchestrator's calls: `sys` its client (made once by `NodeMain`), `in` the call's Puts (a
`[]etcdstart.KV`); it does the Puts through the client (`etcdstart.Writer`, here `Writer_dist`) and
returns the log of those that returned no error (a `[]etcdstart.PutRec`, never `nil`).

**The triple** is `remote.reportOp`'s, at the writer's wire and service (`WriterWire.lean`): from the
machine's resource `writerTok Γ eps V sys` (its client of the view `Γ`, auth off, and its level
token), a value describing the input `(n, ps)` (the Puts, read-only) and the service's precondition
`wP Γ (n, ps)` (the orchestrator's adapter `kmOf Γ n`, the start's changes seen, each Put of the plan
and small, fewer than `2 ^ 56`), `writerOp` returns a value describing a log `rs` with `wQ Γ (n, ps) rs`
(each record's `okFactK`: its revision, from `2` on, is the put of its key and value in a state the
clients saw) and gives the resource back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev writerOp.spec : Prop :=
  ∀ [π : NetProtoGS] (Γ : DistView) (eps : List GoString) (V : WEnv GF),
  Γ.auth = false → errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (sys x : GoInterface) (i : WN × List wkv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      writerTok Γ eps V sys ∗ (writerWire (GF := GF) WN).ivAt x i ∗ wP (Gg := hG.goose_globalGS) Γ i }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerOp)) (Val #sys))
      (Val #x))
  {{ (v : GoInterface), RET #v; writerTok Γ eps V sys ∗
      ∃ rs : List wrec, (writerWire (GF := GF) WN).ovAt v rs ∗ wQ (Gg := hG.goose_globalGS) Γ i rs }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
