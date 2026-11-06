/-
**The stop's serving readers from the stocks `NewServer` hands out** (R2c review F3, 2026-11-06;
round 2's N3: its own module, so that the stop's slot `StopApi` does not import the watch server's
vocabulary). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section readers
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The stop's serving readers** (`srvStopReaders`) from `NewServer`'s 64 store readers and its
watchable store's 64 (`srvWatchReaders`, each holding a reader of the store:
`srvWatchReaders_storeReaders`). -/
theorem srvStopReaders_intro [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions] (s : Loc)
    (E : apply.AEnv GF) :
    ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗ srvWatchReaders s E 64 ⊢
      srvStopReaders (GF := GF) E := by
  unfold srvStopReaders
  rw [← List.replicate_append_replicate]
  iintro ⟨Hsts, HWR⟩
  iapply BigSepL.bigSepL_append.2
  iframe Hsts
  iapply srvWatchReaders_storeReaders $$ HWR

end readers

end EtcdGrove
end Perennial
