/- Lean-first (no Rocq counterpart).

`writerOp(sys, in)` (`examples/etcd/dist/client/nodes.go`): **a writer machine's call** of the watch
workload (#50 N10a, `notes/etcd-dist-plan.md` §24), the operation its `remote.ServeClient` runs for each
of the orchestrator's calls: `sys` its client (`*clientv3.Client`, made once by `NodeMain` from the
members' endpoints rotated), `in` the call's Puts (a `[]etcdstart.KV`); it does the Puts through the
client (`etcdstart.Writer`, here `Writer_dist`) and returns the log of those that returned no error (a
`[]etcdstart.PutRec`, never `nil`).

**The triple:** from the client of the cluster's view `Γ` (auth off), the Puts `ps` (read-only), the
clients' adapter of the orchestrator (`client.kmInv γ` at the cluster's KV, `γ.kv = Γ.kv`, with the
plan's property `γ.W = wkW P`, and the start's changes `[[]]` seen) and each Put one of the plan's,
small enough to send, `writerOp` returns the log `oks` with each record's fact `okFactK γ p`: its
revision, from `2` on, is the put of its key and value in a state the clients saw (what the
orchestrator's check reads). The level token is threaded (the machine's).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist etcdstart

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
  ∀ [π : NetProtoGS] (cl api : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView)
    (γ : KMNames) (P : List (GoString × GoString)) (sl : GoSlice) (ps : List wkv),
  Γ.auth = false → errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  γ.kv = Γ.kv → γ.W = etcd_partition.wkW P → (∀ p ∈ ps, pairOf p ∈ P ∧ wkvSizeOk p) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ kvClientAt cl api eps V Γ ∗ sl ↦*□ ps ∗ kmInv γ ∗
      monoListLbOwn γ.ch ([[]] : List (List mvcc.Change)) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerOp))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty) #cl)))
      (Val #(interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.KV.ty) #sl)))
  {{ (v : GoInterface), RET #v; levelTok 0 ∗
      ∃ (osl : GoSlice) (oks : List wrec),
        ⌜v = interface.mkOk (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.PutRec.ty) #osl⌝ ∗
        osl ↦* oks ∗ □ [∗list] p ∈ oks, etcd_partition.okFactK γ p }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
