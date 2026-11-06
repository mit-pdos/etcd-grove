/-
Lean-first (no Rocq counterpart).

**The multi-member lease example's vocabulary** (`examples/etcd/leasecatchup/leasecatchup.go`;
lease-mono3 step 1, 2026-11-06, `notes/lease-mono3-plan.md`, Scope §2 and §3): the cluster's
configuration (`config()`, `clusterCfg`), which meets the cluster's specs' premise
(`clusterCfg_ok`); the bootstrap facts and the named premises are the three-member cluster's
(`cluster3.BootFacts`, `cluster3.premises`) at that configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The cluster's configuration** (`config()`): token `leasecatchup`, members
`leasecatchup-{1,2,3}`, peer addresses `127.0.0.1:2401{1,2,3}`, client addresses
`127.0.0.1:2402{1,2,3}`, bridge addresses `127.0.0.1:2403{1,2,3}`, a snapshot every applied entry
and the log compacted to one entry below it (`SnapCount = SnapCatchUp = 1`). -/
abbrev clusterCfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config :=
  { Token' := go!"leasecatchup", Name1' := go!"leasecatchup-1", Name2' := go!"leasecatchup-2",
    Name3' := go!"leasecatchup-3",
    Peer1' := go!"127.0.0.1:24011", Peer2' := go!"127.0.0.1:24012", Peer3' := go!"127.0.0.1:24013",
    Client1' := go!"127.0.0.1:24021", Client2' := go!"127.0.0.1:24022",
    Client3' := go!"127.0.0.1:24023",
    Bridge1' := go!"127.0.0.1:24031", Bridge2' := go!"127.0.0.1:24032",
    Bridge3' := go!"127.0.0.1:24033",
    SnapCount' := W64 1, SnapCatchUp' := W64 1 }

/-- **The configuration meets the cluster's specs' premise** (`cluster3.cfgOk`). -/
theorem clusterCfg_ok : cluster3.cfgOk clusterCfg := by
  constructor <;> dsimp only [clusterCfg] <;> (try unfold plainEndpoint) <;> decide

/-- The TTL every lease is granted with (`grantTTL`, seconds). -/
abbrev grantTTL : w64 := W64 3600

end pure

end etcd_leasecatchup
end EtcdGrove
end Perennial
