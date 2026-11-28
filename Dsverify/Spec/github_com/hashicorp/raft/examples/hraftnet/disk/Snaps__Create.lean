/-
(hraft_robust R3) The spec of `disk.(*Snaps).Create` (`snap.go`).
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

/-- `s.Create(ver, idx, term, cfg, cfgIdx, trans)`: a fresh sink, open and empty, with some id (`nextID`
incremented in memory only). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.Create.spec : Prop :=
  ∀ (g : SnapGen) (s : Loc) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (ver idx term cfgIdx : w64)
    (cfg : Configuration) (trans : GoInterface),
    {{ isSnaps g s Qc Wf }}
      (App (App (App (App (App (App (Val (s @!! go.GoType.PointerType Snaps.ty @!! go!"Create"))
        (Val #ver)) (Val #idx)) (Val #term)) (Val #cfg)) (Val #cfgIdx)) (Val #trans))
    {{ (k : Loc) (id : GoString),
        RET (PairV #(interface.mkOk (go.GoType.PointerType Sink.ty) #k) #interface.nil);
        sinkCore k s g Qc Wf id ver idx term cfgIdx cfg ∗ sinkSt k (some []) }}

end sec

end Perennial
