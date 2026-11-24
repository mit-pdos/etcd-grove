/-
`r.add(d)` (`udptransport.go`), **over the protocol's facts**: `d` a fragment (`dgOwn`, at the
model `dg`) with its fact (`udpFragOk`: the chunk of the body recorded under its name). When it
completes its message, the body returned is the one recorded under the name, with its fact: the
chunks held are all of that body (`ownPartial`'s `chunkSlot`s, which agree by `udpMsgAt`), and
they make it (`chunks_flatten`). `reack` has no meaning to the spec; nor have eviction and the
memory bounds, the code's free choice.
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions] [net_udp_sem : net.UdpFieldAssumptions]

/-- See the file header. -/
abbrev reassembler.add.spec : Prop :=
  ∀ (F : KvFacts GF) (γu : UdpNames) (r : Loc) (d : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.datagram) (dg : DgM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ ownReassembler F γu r ∗ dgOwn d dg ∗ ⌜dg.kind = kindFragmentB⌝ ∗ udpFragOk F γu dg }}
    (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.reassembler.ty @!! go!"add")) (Val #d))
  {{ (body : GoSlice) (complete reack : Bool), RET (PairV (PairV #body #complete) #reack);
      ownReassembler F γu r ∗
      (⌜complete = false⌝ ∨ ⌜complete = true⌝ ∗ ∃ bs : List w8, body ↦* bs ∗ udpMsgAt γu dg.key bs ∗
        udpBodyOk F bs) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
