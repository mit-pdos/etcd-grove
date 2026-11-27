/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__sendLatestSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).sendLatestSnapshot`'s spec (stage 3, raft-internal: the replication goroutine; crosses the snapshot store, the transport and the commitment).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

/-- `(*Raft).sendLatestSnapshot(s)`, by the replication goroutine of the leader `i` of term `T` for
voter `j`: opens the store's latest snapshot (an error if there is none or it was replaced
meanwhile); stops (`true`, fix `5894fa2`, D31) if its server's term is no longer `T` (before the check
the snapshot is a valid install of `T` or the term moved on: `gprot.snapValid_or_left`,
`snapValid_follow`); sends it to `j` as a valid InstallSnapshot request of `T` (`isReq`); stops
(`true`) on a newer term in the response (`handleStaleTerm`); on success sets `nextIndex` and counts
the snapshot in the commitment (`commitInv`'s `lciOk` disjunct); returns `(false, err)` with any error
otherwise. -/
abbrev github_com.hashicorp.raft.Raft.sendLatestSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗ replFields s ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"sendLatestSnapshot")) (Val #s))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err); rtok tid ∗ replFields s }}

end spec

end Perennial
