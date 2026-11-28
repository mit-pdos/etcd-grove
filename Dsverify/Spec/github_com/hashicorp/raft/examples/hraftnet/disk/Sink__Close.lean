/-
(hraft_robust R3) The spec of `disk.(*Sink).Close` (`snap.go`).
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

/-- `k.Close()`: on an open sink with `bs`, the close obligation `Qc m bs` (`m` the sink's metadata) and the
client's commit (`snapCommitAU`), makes the snapshot the latest unless the store's is newer, and returns the
commit's result `R`: when it is newer, it is written to the file under the lock (`persist`), `Qc m bs` held by
the invariant from the rename to the commit after the write (`snapsCrash` gives it back if the new file
survives a crash), the client's commit holding the rest; otherwise the commit runs at once. On a closed sink,
nothing. The close obligation shows the configuration's servers (read-only: `persist` encodes them). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Sink.Close.spec : Prop :=
  ∀ (k s : Loc) (g : SnapGen) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (id : GoString)
    (ver idx term cfgIdx : w64) (cfg : Configuration) (o : Option (List w8)) (R : IProp GF),
    (∀ m b, Qc m b ⊢ (∃ svs : List Server, m.Configuration'.Servers' ↦*□ svs) ∗ Qc m b) →
    {{ sinkCore k s g Qc Wf id ver idx term cfgIdx cfg ∗ sinkSt k o ∗
        (match o with
          | some bs => iprop(Qc (sinkMeta ver idx term cfgIdx cfg id bs) bs ∗
              (Qc (sinkMeta ver idx term cfgIdx cfg id bs) bs -∗
                snapCommitAU g (sinkMeta ver idx term cfgIdx cfg id bs) bs R))
          | none => iprop(True)) }}
      (App (Val (k @!! go.GoType.PointerType Sink.ty @!! go!"Close")) (Val #()))
    {{ RET #interface.nil; sinkSt k none ∗ (match o with | some _ => R | none => iprop(True)) }}

end sec

end Perennial
