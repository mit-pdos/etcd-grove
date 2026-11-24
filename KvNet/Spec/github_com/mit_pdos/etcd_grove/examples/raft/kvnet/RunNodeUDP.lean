/-
`RunNodeUDP(id, addrs, dir, voters, ...)` (`nodeudp.go`): `RunNode` with `RunUDP`: the same check
(`runNodeOk`: `ValidCluster`, `id` among the replicas, `dir` shorter than `MaxDirLen`; else it returns
at once) and the same address map, and the process's UDP start for every address map that holds
exactly the addresses (`addrMapOk`), as `S`. Every configuration is allowed: the resources are needed
only if the check passes. `ValidCluster` checks every address, so `openUDP`'s own-address panic cannot
happen. (kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`; the check as `RunNode`'s since 2026-11-24.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpBootDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs

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
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev RunNodeUDP.spec (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF) : Prop :=
  ∀ (γu : UdpNames) (id : w64) (addrs dir : GoString) (voters : w64) (pv cq sd : Bool)
    (msz mcs mif : w64) (eof ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      (⌜runNodeOk (splitAddrs addrs) (uint.nat id) dir (uint.nat voters) (uint.nat msz)
          (uint.nat mcs) (uint.nat mif)⌝ -∗
        (∀ a, ⌜(splitAddrs addrs)[uint.nat id - 1]? = some a⌝ -∗
          addrProto a (kvP F id) (kvQ F id)) ∗
        (∀ M, ⌜addrMapOk (splitAddrs addrs) M⌝ -∗
          S id dir ⟨voters, pv, cq, sd, msz, mcs, mif⟩ M ∗ udpProcStart F γu id dir M)) ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      context.isClosedchanInit }}
    (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunNodeUDP)) (Val #id))
      (Val #addrs)) (Val #dir)) (Val #voters)) (Val #pv)) (Val #cq)) (Val #sd))
      (Val #msz)) (Val #mcs)) (Val #mif))
  {{ RET #(); True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
