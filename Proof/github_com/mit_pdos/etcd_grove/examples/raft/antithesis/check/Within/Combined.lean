/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): W6's budget laws without hypotheses:
its `_of` laws (`Within/Ready.lean`, ...) applied to the other groups' laws (`inMemory_within`,
`onDisk_within`, `onDisk_keeps`, `boot_within`, `send_within`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Mem
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Write
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Flush
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Bind
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Step
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.InMemory
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.OnDisk
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Send
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws2

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

theorem State.mem_within : ActionWithin State.mem := State.mem_within_of State.inMemory_within

theorem State.write_within : ActionWithin State.write := State.write_within_of State.onDisk_within

theorem State.flush_within : ActionWithin State.flush := State.flush_within_of State.onDisk_within

theorem State.ready_within : ActionWithin State.ready :=
  State.ready_within_of State.onDisk_keeps State.inMemory_within State.onDisk_within

theorem State.bind_within : ActionWithin State.bind :=
  State.bind_within_of State.onDisk_keeps State.inMemory_within State.onDisk_within
    State.boot_within State.send_within

theorem State.step_within : StepWithin :=
  State.step_within_of State.onDisk_keeps State.inMemory_within State.onDisk_within
    State.boot_within State.send_within

end AntCheck
end EtcdGrove
end Perennial
