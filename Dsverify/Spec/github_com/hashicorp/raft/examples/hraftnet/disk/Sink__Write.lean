/-
(hraft_robust R3) The spec of `disk.(*Sink).Write` (`snap.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SinkDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- `k.Write(p)` on an open sink: appends `p`'s bytes. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Write.spec : Prop :=
  ∀ (k : Loc) (p : GoSlice) (dq : DFrac) (bs c : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ sinkSt k (some bs) ∗ p ↦*{dq} c }}
      (App (Val (k @!! go.GoType.PointerType Sink.ty @!! go!"Write")) (Val #p))
    {{ RET (PairV #(W64 c.length) #interface.nil); sinkSt k (some (bs ++ c)) ∗ p ↦*{dq} c }}

end sec

end Perennial
