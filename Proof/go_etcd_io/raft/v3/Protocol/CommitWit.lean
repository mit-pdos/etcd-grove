/-
Lean-first (no Rocq counterpart). D22 S-b (2026-10-19): the commit witness a node hands out with a
`Ready`'s hard state (`commitWit`, `hsWit`), which `SnapMint.lean`'s `isMessage_snap_recontent`
consumes (`notes/decisions.md`, "D22 S-b carried out").
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWitCore

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- What a node at term `T` with commit index `c` knows of its full log `F`: its records,
`commitIn γ F c T` and the committed prefix `F.take c` (D22 S-b; `SnapMint.lean`'s header). -/
def commitWit (γ : RaftNames) (T c : w64) : IProp GF :=
  iprop(∃ F, ⌜PlogWf base0 F⌝ ∗ logRecs γ base0 F ∗ commitIn γ F c T ∗
    isCommitted γ (F.take (uint.Z c).toNat))

instance commitWit_persistent (γ : RaftNames) (T c : w64) :
    Persistent (commitWit (GF := GF) γ T c) := by
  unfold commitWit; infer_instance
instance commitWit_timeless (γ : RaftNames) (T c : w64) :
    Timeless (commitWit (GF := GF) γ T c) := by
  unfold commitWit; infer_instance

/-- A quorum certificate at or before `old` is also a certificate at or before
`t`. The recovered WAL's local commit index is irrelevant to this implication. -/
theorem commitWit_mono_term (γ : RaftNames) (old t c : w64) (ht : uint.Z old ≤ uint.Z t) :
    commitWit (GF := GF) γ old c ⊢ commitWit γ t c := by
  unfold commitWit
  iintro ⟨%F, %Hwf, #Hr, #Hc, #Hknown⟩
  iexists F
  iframe Hr Hknown
  isplitr
  · ipureintro; exact Hwf
  iapply commitIn_agree γ F F c old t ht rfl rfl $$ Hc

/-- (D22 S-b, item 2) What a `Ready`'s hard state `h` says, the committed log handed out with it
of length `n`: nothing for the zero record (a `nil` `HardState` reads as it), else raft's state at
the `Ready`: the witness of its term and commit index, which bounds what was handed out. (A
non-`nil` `HardState` is `hardState()` of the node at the `Ready`.) -/
def hsWit (γ : RaftNames) (h : HardStateM) (n : Nat) : IProp GF :=
  iprop(⌜h = HardStateM.mk (W64 0) (W64 0) (W64 0)⌝ ∨
    (commitWit γ h.Term' h.Commit' ∗ ⌜(n : Int) ≤ uint.Z h.Commit'⌝))

instance hsWit_persistent (γ : RaftNames) (h : HardStateM) (n : Nat) :
    Persistent (hsWit (GF := GF) γ h n) := by
  unfold hsWit; infer_instance
instance hsWit_timeless (γ : RaftNames) (h : HardStateM) (n : Nat) :
    Timeless (hsWit (GF := GF) γ h n) := by
  unfold hsWit; infer_instance

/-- (D22l) What a hard state raft once had says (persistent; `ownRawNode` keeps it of
`prevHardSt`): nothing for the zero record, else the witness of its term and commit index. -/
def phsWit (γ : RaftNames) (h : HardStateM) : IProp GF :=
  iprop(⌜h = HardStateM.mk (W64 0) (W64 0) (W64 0)⌝ ∨ commitWit γ h.Term' h.Commit')

instance phsWit_persistent (γ : RaftNames) (h : HardStateM) :
    Persistent (phsWit (GF := GF) γ h) := by
  unfold phsWit; infer_instance

theorem phsWit_zero (γ : RaftNames) :
    ⊢ phsWit (GF := GF) γ (HardStateM.mk (W64 0) (W64 0) (W64 0)) := by
  unfold phsWit; ileft; ipureintro; rfl

theorem phsWit_of_hsWit (γ : RaftNames) (h : HardStateM) (n : Nat) :
    hsWit (GF := GF) γ h n ⊢ phsWit γ h := by
  unfold hsWit phsWit
  iintro (%H | ⟨#H, -⟩)
  · ileft; ipureintro; exact H
  · iright; iexact H

/-- A `Ready`'s witness over `prevHardSt`'s update gives the witness of its own hard state. -/
theorem phsWit_of_hsWit_next (γ : RaftNames) (p h : HardStateM) (n : Nat) :
    hsWit (GF := GF) γ (phsNext p h) n ⊢ phsWit γ h := by
  iintro #H
  by_cases He : h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0
  · unfold phsWit; ileft; ipureintro
    obtain ⟨h1, h2, h3⟩ := He
    cases h; simp only at h1 h2 h3; subst h1 h2 h3; rfl
  · rw [phsNext_ne p h He]
    iapply phsWit_of_hsWit γ h n $$ H

/-- The witness of a hard state, at a committed log within its commit index. -/
theorem hsWit_of_phsWit (γ : RaftNames) (h : HardStateM) (n : Nat)
    (Hn : (n : Int) ≤ uint.Z h.Commit') :
    phsWit (GF := GF) γ h ⊢ hsWit γ h n := by
  unfold hsWit phsWit
  iintro (%H | #H)
  · ileft; ipureintro; exact H
  · iright; iframe H; ipureintro; exact Hn

variable [CrashGS GF] in
/-- A witness bounds every shorter committed log. -/
theorem hsWit_mono (γ : RaftNames) (h : HardStateM) (n m : Nat) (H : m ≤ n) :
    hsWit (GF := GF) γ h n ⊢ hsWit γ h m := by
  unfold hsWit
  iintro (%Hz | ⟨#Hw, %Hn⟩)
  · ileft; ipureintro; exact Hz
  · iright; iframe Hw; ipureintro; omega

variable [CrashGS GF] in
/-- Every node holds the witness of its own term and commit index. -/
theorem ownRaftGhost_commitWit (γ : RaftNames) (id : w64) (s : PState) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ commitWit γ s.term s.commit := by
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, H⟩
  iNamed H
  unfold commitWit
  iexists fp ++ s.log
  isplitr; · ipureintro; exact full_wf _ _ _ Hfull.1 Hfull.2.1
  isplitr; · iapply logRecs_full γ s.base fp s.log Hfull.1 $$ Hfrecs Hrecs
  isplitr; · iexact Hcommit
  iunfold cprefix at Hcmt
  iexact Hcmt

end ghost

end EtcdGrove
end Perennial
