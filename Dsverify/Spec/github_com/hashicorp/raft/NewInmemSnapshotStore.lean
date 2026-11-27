/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/NewInmemSnapshotStore.lean (241f27e).
-/
/-
`raft.NewInmemSnapshotStore`'s spec: a fresh store with no snapshot (its handle). Its reader
tokens go to a thread pool, which needs the bound `threadBound GF ≤ 2^28` (a quarter thread pool, `HrVerify/Proof/Threads/QPool.lean`, D15).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemSnapshotStoreBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft in
/-- `NewInmemSnapshotStore()` returns a fresh store with no snapshot. -/
abbrev github_com.hashicorp.raft.NewInmemSnapshotStore.spec : Prop :=
  ThreadBoundLe GF (2 ^ 28) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (@! github_com.hashicorp.raft.NewInmemSnapshotStore)) (Val #()))
  {{ (m : Loc), RET #m; isInmemSnapshotStore m }}

end spec

end Perennial
