/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/HasExistingState.lean (241f27e).
-/
/-
`raft.HasExistingState`'s spec (API-internal): fresh stores have no state.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `HasExistingState(logs, stable, snaps)` on an empty log and a stable store without a current
term: false, nil. -/
abbrev github_com.hashicorp.raft.HasExistingState.spec : Prop :=
  ∀ (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Qc : SnapshotMeta → List w8 → IProp GF) (logsI stableI snapsI : GoInterfaceOk) (γ : GNames) (i : SID)
    (ownL : LogAbs → IProp GF) (ownS : StableAbs → IProp GF) (ownSS : SnapLatest → IProp GF)
    (eof : GoInterface) (sst : StableAbs) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     isLogStore logsI ownL Wl ∗ isStableStore stableI ownS Ws ∗ isSnapStore snapsI ownSS eof Qc ∗
     ownL LogAbs.empty ∗ ownS sst ∗ ⌜(sst.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0) = W64 0⌝ ∗
     ownSS none ∗ rtok tid }}
    (App (App (App (Val (@! github_com.hashicorp.raft.HasExistingState)) (Val #(GoInterface.ok logsI)))
      (Val #(GoInterface.ok stableI))) (Val #(GoInterface.ok snapsI)))
  {{ RET (PairV #false #interface.nil); ownL LogAbs.empty ∗ ownS sst ∗ ownSS none ∗ rtok tid }}

end spec

end Perennial
