/-
(hraft_robust R3) The spec of `disk.(*Snaps).Open` (`snap.go`).
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

/-- `s.Open(id)`: atomically, the latest's metadata and a reader over a copy of its bytes if its id is `id`,
else an error (`openPost`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.Open.spec : Prop :=
  ∀ (g : SnapGen) (s : Loc) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (eof : GoInterface)
    (id : GoString) (Φ : val → IProp GF),
    isSnaps g s Qc Wf ∗ globalAddr io.EOF ↦□ eof ∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, snapsOwn g old ∗
        (snapsOwn g old ={∅,⊤ \ ↑storeN}=∗ ∀ v : val, openPost old id eof v -∗ Φ v)) ⊢
    WP (App (Val (s @!! go.GoType.PointerType Snaps.ty @!! go!"Open")) (Val #id)) {{ Φ }}

end sec

end Perennial
