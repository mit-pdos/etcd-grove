/-
`nd.serveClient(c)` (`examples/raft/kvnet/node.go`): the node `id` answers one client request on the
connection `c` (its accepted end, `cn`, `true`), whose hello byte it has read (`recvTokL cn true
(kvP F id) [helloClientB]`), with its writer's token of the reply direction (`sendTok cn true
(kvQ F id) []`): it reads one request frame (within `helloTimeout`, `closeAfter`), runs it
(`Node.handle`, whose answer has the protocol's fact), and writes the reply frame (`putB [0]`, no
answer, or `putB (1 :: v)`), which the protocol `kvQ` admits (`server_reply`, `server_noans`); then
closes `c`. Partial correctness: it returns, with nothing. At the store's seam `rep`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev Node.serveClient.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF) : Prop :=
  ∀ (nd : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH)
    (c : GoInterface) (cn : Nat) (a : GoString) (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      isNodeS F rep nd γ N id n ∗ confLaw F rep cf γ N id ∗ net.isConn (GF := GF) c cn true a ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit ∗ recvTokL cn true (kvP F id) [helloClientB] ∗
      sendTok cn true (kvQ F id) [] }}
    (App (Val (nd @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node.ty
      @!! go!"serveClient")) (Val #c))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
