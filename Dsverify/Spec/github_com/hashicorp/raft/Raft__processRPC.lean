/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__processRPC.lean (241f27e).
-/
/-
`raft.(*Raft).processRPC`'s spec (raft-internal interface; called by the follower, candidate and
leader loops). Handles one RPC delivered to server `i` (a valid request of a kind the program sends,
with its response channel) and responds on it.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

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

/-- `(*Raft).processRPC(rpc)`: the main goroutine handles the RPC and responds to it. Unless it
becomes a follower, its term and log are unchanged (its callers' loops rely on it: review R1 T1-2). (Stage 2) A TimeoutNow (`timeoutNow`) makes the server a Candidate
with its term and log unchanged; a candidate from a leadership transfer does not step down on a valid
AppendEntries of its term (`appendEntries`), so it may stay Candidate with its log changed, the term
then having another leader (so `runCandidate` cannot win it after its log changed). -/
abbrev github_com.hashicorp.raft.Raft.processRPC.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (s : SState) (st : w32) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      mainOwnAt r γ rc i s st ∗ rpcP γ rc.snapP i rpc ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"processRPC")) (Val #rpc))
  {{ RET #(); ∃ (s' : SState) (st' : w32), mainOwnAt r γ rc i s' st' ∗ rtok tid ∗
      (⌜st' = stFollower ∨ (st' = st ∧ s'.term = s.term ∧ s'.log = s.log) ∨
        (st' = stCandidate ∧ s'.term = s.term ∧ s'.log = s.log)⌝ ∨
       ⌜st' = st ∧ st = stCandidate ∧ s'.term = s.term⌝ ∗ ∃ ℓ : SID, ⌜ℓ ≠ i⌝ ∗ leaderIs γ s.term ℓ) }}

end spec

end Perennial
