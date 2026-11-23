/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the budget law of `Bind`
(`State.bind_within_of`): each action's, the ones not proved here taken as hypotheses.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Ready
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Mem
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Write
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Flush
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Wrote
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Recv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Net
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Made
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.ApplyEv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.RestoreEv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.ConfEv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.SnapEv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.ReadAsked
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.ReadGiven

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

theorem State.bind_within_of (onDisk_keeps : W6Laws.OnDiskKeeps) (inMemory_within : InMemoryWithin)
    (onDisk_within : OnDiskWithin) (boot_within : ActionWithin State.boot)
    (send_within : ActionWithin State.send) : ActionWithin State.bind := by
  intro s n ev b E s' hn hW hNO hCh hb ho hv
  unfold State.bind at ho
  by_cases h_boot : (ev.e == go!"boot") = true
  · simp only [h_boot, ↓reduceIte] at ho; exact boot_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_boot, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_recv : (ev.e == go!"recv") = true
  · simp only [h_recv, ↓reduceIte] at ho; exact State.recv_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_recv, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_ready : (ev.e == go!"ready") = true
  · simp only [h_ready, ↓reduceIte] at ho; exact State.ready_within_of onDisk_keeps inMemory_within onDisk_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_ready, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_mem : (ev.e == go!"mem") = true
  · simp only [h_mem, ↓reduceIte] at ho; exact State.mem_within_of inMemory_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_mem, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_write : (ev.e == go!"write") = true
  · simp only [h_write, ↓reduceIte] at ho; exact State.write_within_of onDisk_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_write, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_wrote : (ev.e == go!"wrote") = true
  · simp only [h_wrote, ↓reduceIte] at ho; exact State.wrote_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_wrote, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_flush : (ev.e == go!"flush") = true
  · simp only [h_flush, ↓reduceIte] at ho; exact State.flush_within_of onDisk_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_flush, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_net : (ev.e == go!"net") = true
  · simp only [h_net, ↓reduceIte] at ho; exact State.net_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_net, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_made : (ev.e == go!"made") = true
  · simp only [h_made, ↓reduceIte] at ho; exact State.made_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_made, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_send : (ev.e == go!"send") = true
  · simp only [h_send, ↓reduceIte] at ho; exact send_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_send, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_apply : (ev.e == go!"apply") = true
  · simp only [h_apply, ↓reduceIte] at ho; exact State.applyEv_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_apply, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_restore : (ev.e == go!"restore") = true
  · simp only [h_restore, ↓reduceIte] at ho; exact State.restoreEv_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_restore, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_conf : (ev.e == go!"conf") = true
  · simp only [h_conf, ↓reduceIte] at ho; exact State.confEv_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_conf, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_snap : (ev.e == go!"snap") = true
  · simp only [h_snap, ↓reduceIte] at ho; exact State.snapEv_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_snap, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_readreq : (ev.e == go!"readreq") = true
  · simp only [h_readreq, ↓reduceIte] at ho; exact State.readAsked_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_readreq, Bool.false_eq_true, ↓reduceIte] at ho
  by_cases h_read : (ev.e == go!"read") = true
  · simp only [h_read, ↓reduceIte] at ho; exact State.readGiven_within s n ev b E s' hn hW hNO hCh hb ho hv
  simp only [h_read, Bool.false_eq_true, ↓reduceIte] at ho
  simp only [pure_ok, Except.ok.injEq, reduceCtorEq] at ho

end AntCheck
end EtcdGrove
end Perennial
