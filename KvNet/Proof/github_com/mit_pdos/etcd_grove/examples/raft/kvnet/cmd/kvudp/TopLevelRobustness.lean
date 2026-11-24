/-
# `raft/kvnet/cmd/kvudp`: the top-level robustness theorem's proof (skeleton, 2026-11-24)

`notes/kvudp-proof-plan.md`, "The top level". The plan, as kvnet's proof
(`KvNet/Proof/.../kvnet/TopLevelRobustness.lean`) with the UDP side added:

* the start (`NetFsUdp.kvudp_dist_crash_adequacy`'s `Hstart`): kvnet's global allocation (the store's
  names, the addresses' TCP protocols, raft's cluster), and kvudp's: the names' invariant `udpMsgInv γu`
  (`udpHi γu id 0` for every replica `id`, empty maps), and one `udpAddrInv` per replica address, from
  the UDP extension's start resources (`kvudp_udp_globalStart`: `udpSent a []` for every valid address);
* a generation's boot: kvnet's `kvGen_first`/`kvGen_crash` hand back the rest of the directory
  (`kvDirRest`: the claim on every other name, half the root's call permission); the boot file's two
  names out of it (`osNames_take2`, `kvBoot_names_fresh`), then `udp_gen_boot` (`DurFs.durBootOnly` and
  `udp_boot_alloc`): `RunNodeUDP`'s `udpProcStart`, beside kvnet's `kvGen_boot`;
* a crash: kvnet's `kvGen_crash`, and the boot file's (`udp_boot_crash`, `durable`'s crash lemma on the
  boot file, `bootOk_crash`; see the plan's risks: the crash's `crashRest` must serve both files);
* the programs: `RunNodeUDP.wp_proof` (through `RunUDP`, `startNodeUDP` at kvnet's seams), kvcheck's as
  kvnet's.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.TopLevelRobustness
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.cmd.kvudp.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvudp

open NetFsUdp

section proof
attribute [local instance] kvudpExts kvudpExtsSemantics kvudpExts_hasNet kvudpExts_hasFs
  kvudpExts_hasUdp
variable [go_gctx : GoGlobalContext]

/-- **kvudp is robust** (the statement: `raft_kvudp_robust.spec`). -/
theorem raft_kvudp_robust : raft_kvudp_robust.spec := by
  sorry

/-- **kvudp is robust, an example**: from `raft_kvudp_robust`. -/
theorem raft_kvudp_robust_example : raft_kvudp_robust_example.spec := by
  sorry

end proof

end raft_kvudp
end EtcdGrove
end Perennial
