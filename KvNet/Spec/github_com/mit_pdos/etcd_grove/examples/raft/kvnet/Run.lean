/-
`Run(cfg)` (`examples/raft/kvnet/node.go`): the replica `cfg.ID`'s process: it listens on its address
(`cfg.Addrs[cfg.ID] = a`, valid, with the protocols `kvP F id`/`kvQ F id`: `addrProto`), starts the
replica (`StartNode`, from the start resources `S`, at the configuration), then accepts connections forever, each served
in a goroutine of its own (`Node.serve`, with the acceptor's end `accept_au` gives). At the store's
seams `rep`, `cf`, `S`. Partial correctness: it never returns (the post is never reached).
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
abbrev Run.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeConfig) (M : GMap w64 GoString)
    (a : GoString) (eof ed : GoInterface),
  M !! cfg.ID' = some a →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      cfg.Addrs' ↦$□ M ∗ addrProto a (kvP F cfg.ID') (kvQ F cfg.ID') ∗
      S cfg.ID' cfg.Dir' cfg.Opts' M ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Run)) (Val #cfg))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
