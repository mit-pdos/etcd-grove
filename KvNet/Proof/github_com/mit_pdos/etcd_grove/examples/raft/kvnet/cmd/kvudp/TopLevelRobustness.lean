/-
# `raft/kvnet/cmd/kvudp`: the top-level robustness theorem's proof (skeleton, 2026-11-24)

`notes/kvudp-proof-plan.md`, "The top level". The plan, as kvnet's proof
(`KvNet/Proof/.../kvnet/TopLevelRobustness.lean`) with the UDP side added:

* the start (`NetFsUdp.kvudp_dist_crash_adequacy`'s `Hstart`): kvnet's global allocation (the store's
  names, the addresses' TCP protocols, raft's cluster), and kvudp's: the names' invariant `udpMsgInv γu`
  (`udpHi γu id 0` for every replica `id`, empty maps), and one `udpAddrInv` per replica address, from
  the UDP extension's start resources (`kvudp_udp_globalStart`: `udpSent a []` for every valid address);
* a generation's boot: kvnet's `kvGen_boot`, and the boot file's (`durable`'s boot on the second file of
  the directory, `udp_boot_alloc`), giving `RunNodeUDP`'s `udpProcStart`;
* a crash: kvnet's `kvGen_crash`, and the boot file's (`udp_boot_crash`, `durable`'s crash lemma,
  `bootOk_crash`);
* the programs: `RunNodeUDP.wp_proof` (through `RunUDP`, `startNodeUDP` at kvnet's seams), kvcheck's as
  kvnet's.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.TopLevelRobustness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvudp

/-- **kvudp is robust** (the statement: `raft_kvudp_robust.spec`). -/
theorem raft_kvudp_robust : raft_kvudp_robust.spec := by
  sorry

/-- **kvudp is robust, an example**: from `raft_kvudp_robust`. -/
theorem raft_kvudp_robust_example : raft_kvudp_robust_example.spec := by
  sorry

end raft_kvudp
end EtcdGrove
end Perennial
