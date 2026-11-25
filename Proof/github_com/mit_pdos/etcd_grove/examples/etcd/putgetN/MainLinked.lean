/-
`Main`'s callees linked (the clusterN Scope, 2026-11-15), by hand, as putget3's (`putget3/MainLinked.lean`):
`etcd_putgetN.Main.wp_proof` applied to the examples' shared start's linked `Members`, `StartMembers`,
`Serve` and `NewClient` (`etcdstart/Link.lean`), `context`'s `Background`, the axiom of `zap.NewNop`, and
`rafthttp.bootCfg_of_le` (a directory of up to `1000` members is within the transport's `peersMax`).
`Results.lean` restates it.
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Assumptions]

/-- **putgetN's `Main(k)` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putgetN/Main.lean`), under the semantic premises of
its callees' linked results (putget3's). -/
theorem etcd_putgetN.wp_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_putgetN.Main.spec (GF := GF) (hG := hG) :=
  etcd_putgetN.Main.wp_proof zap.NewNop.wp_proof etcdstart.wp_Members etcdstart.wp_StartMembers
    etcdstart.wp_Serve etcdstart.wp_NewClient context.wp_Background
    context.WithTimeoutBackground.wp_proof context.wp_ErrAny mvcc.api.mvccApi_names_nonempty_law_holds
    (fun dir ps h hl => rafthttp.bootCfg_of_le dir ps h (by unfold peersMax; omega)) _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof

end results

end EtcdGrove
end Perennial
