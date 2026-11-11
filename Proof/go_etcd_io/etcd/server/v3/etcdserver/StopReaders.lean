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

/-- **The stop's serving readers** (`srvStopReaders`) from `NewServer`'s 64 reader tokens and its
watch service's 64 (`srvWatchReaders`' tokens, `srvWatchReaders_readers`), joined by the API's
`mvccReaders_split.law`. -/
theorem srvStopReaders_intro (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) (s : Loc)
    (E : apply.AEnv GF) :
    mvcc.api.mvccReaders E.γ 64 ∗ srvWatchReaders s E 64 ⊢ srvStopReaders (GF := GF) E := by
  unfold srvStopReaders
  iintro ⟨Hsts, HWR⟩
  ihave Hw := srvWatchReaders_readers s E 64 $$ HWR
  iapply (hRS E.γ 64 64).2
  iframe Hsts Hw

end readers

end EtcdGrove
end Perennial
