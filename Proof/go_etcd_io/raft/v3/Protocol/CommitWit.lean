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

/-- (keepfix (c), F2', 2026-11-27) **A hard state with a nonzero commit index has a nonzero term**,
once the bootstrap log is non-empty: the entry at the commit index has a term `≥ 1` (a boot entry's
is `1`, a leader's at least `2`) and at most the node's term. What makes the raft term an etcd apply
batch records nonzero (`nodeDriver_hardStateTerm`). -/
def TermPos (γ : RaftNames) (h : HardStateM) : Prop :=
  γ.reBoot ≠ [] → 1 ≤ uint.Z h.Commit' → 1 ≤ uint.Z h.Term'

theorem TermPos_zero (γ : RaftNames) : TermPos γ (HardStateM.mk (W64 0) (W64 0) (W64 0)) := by
  intro _ h
  exfalso; revert h; word

/-- (keepfix (c), F2') `TermPos` of a full log's commit index and a term bounding its entries. -/
theorem termPos_of_full (γ : RaftNames) (F : List EntryM) (c T : w64) :
    uint.Z c ≤ plogLastIndexZ base0 F →
    (∀ (j x : w64), plogTermAt base0 F j = some x → uint.Z x ≤ uint.Z T) →
    ⊢ logRecs (GF := GF) γ base0 F -∗ ⌜γ.reBoot ≠ [] → 1 ≤ uint.Z c → 1 ≤ uint.Z T⌝ := by
  intro Hc HT
  iintro #H
  by_cases H1 : 1 ≤ uint.Z c
  · obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp
      (plogTermAt_in_range base0 F c ⟨by rw [base0_index]; exact uint_Z_nonneg c, Hc⟩)
    icases logRecs_termAt_pos γ F c x Hx H1 $$ H with %Hp
    ipureintro; intro hb _
    have := Hp hb; have := HT c x Hx; omega
  · ipureintro; intro _ h; omega

/-- (D22 S-b, item 2) What a `Ready`'s hard state `h` says, the committed log handed out with it
of length `n`: nothing for the zero record (a `nil` `HardState` reads as it), else raft's state at
the `Ready`: the witness of its term and commit index. Either way the commit index bounds what was
handed out (keepfix (c), F1, 2026-11-27: the bound out of the disjunction, so a zero record bounds it
by 0), and (F2') a nonzero commit index comes with a nonzero term (`TermPos`). (A non-`nil`
`HardState` is `hardState()` of the node at the `Ready`.) -/
def hsWit (γ : RaftNames) (h : HardStateM) (n : Nat) : IProp GF :=
  iprop(⌜(n : Int) ≤ uint.Z h.Commit'⌝ ∗ ⌜TermPos γ h⌝ ∗
    (⌜h = HardStateM.mk (W64 0) (W64 0) (W64 0)⌝ ∨ commitWit γ h.Term' h.Commit'))

instance hsWit_persistent (γ : RaftNames) (h : HardStateM) (n : Nat) :
    Persistent (hsWit (GF := GF) γ h n) := by
  unfold hsWit; infer_instance
instance hsWit_timeless (γ : RaftNames) (h : HardStateM) (n : Nat) :
    Timeless (hsWit (GF := GF) γ h n) := by
  unfold hsWit; infer_instance

/-- (D22l) What a hard state raft once had says (persistent; `ownRawNode` keeps it of
`prevHardSt`): nothing for the zero record, else the witness of its term and commit index; and
(keepfix (c), F2') a nonzero commit index comes with a nonzero term (`TermPos`). -/
def phsWit (γ : RaftNames) (h : HardStateM) : IProp GF :=
  iprop(⌜TermPos γ h⌝ ∗ (⌜h = HardStateM.mk (W64 0) (W64 0) (W64 0)⌝ ∨ commitWit γ h.Term' h.Commit'))

instance phsWit_persistent (γ : RaftNames) (h : HardStateM) :
    Persistent (phsWit (GF := GF) γ h) := by
  unfold phsWit; infer_instance

theorem phsWit_zero (γ : RaftNames) :
    ⊢ phsWit (GF := GF) γ (HardStateM.mk (W64 0) (W64 0) (W64 0)) := by
  unfold phsWit
  isplitr; · ipureintro; exact TermPos_zero γ
  ileft; ipureintro; rfl

theorem phsWit_of_hsWit (γ : RaftNames) (h : HardStateM) (n : Nat) :
    hsWit (GF := GF) γ h n ⊢ phsWit γ h := by
  unfold hsWit phsWit
  iintro ⟨-, %Hp, #H⟩
  isplitr; · ipureintro; exact Hp
  iexact H

/-- A `Ready`'s witness over `prevHardSt`'s update gives the witness of its own hard state. -/
theorem phsWit_of_hsWit_next (γ : RaftNames) (p h : HardStateM) (n : Nat) :
    hsWit (GF := GF) γ (phsNext p h) n ⊢ phsWit γ h := by
  iintro #H
  by_cases He : h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0
  · obtain ⟨h1, h2, h3⟩ := He
    have : h = HardStateM.mk (W64 0) (W64 0) (W64 0) := by
      cases h; simp only at h1 h2 h3; subst h1 h2 h3; rfl
    rw [this]; iapply phsWit_zero
  · rw [phsNext_ne p h He]
    iapply phsWit_of_hsWit γ h n $$ H

/-- The witness of a hard state, at a committed log within its commit index. -/
theorem hsWit_of_phsWit (γ : RaftNames) (h : HardStateM) (n : Nat)
    (Hn : (n : Int) ≤ uint.Z h.Commit') :
    phsWit (GF := GF) γ h ⊢ hsWit γ h n := by
  unfold hsWit phsWit
  iintro #H
  isplitr; · ipureintro; exact Hn
  iexact H

variable [CrashGS GF] in
/-- A witness bounds every shorter committed log. -/
theorem hsWit_mono (γ : RaftNames) (h : HardStateM) (n m : Nat) (H : m ≤ n) :
    hsWit (GF := GF) γ h n ⊢ hsWit γ h m := by
  unfold hsWit
  iintro ⟨%Hn, #Hw⟩
  iframe Hw; ipureintro; omega

variable [CrashGS GF] in
/-- (keepfix (c), F2') A running node's commit index is nonzero only at a nonzero term, once the
bootstrap log is non-empty: its full log's entry at the commit index has a record (term `≥ 1`) and a
term at most the node's (`TermsLe`). -/
theorem ownRaftGhost_termPos (γ : RaftNames) (id : w64) (s : PState) {md : Bool} :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
      ⌜γ.reBoot ≠ [] → 1 ≤ uint.Z s.commit → 1 ≤ uint.Z s.term⌝ := by
  unfold ownRaftGhost ownLogGhost
  iintro ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, H⟩
  iNamed H
  ihave #Hl := logRecs_full γ s.base fp s.log Hfull.1 $$ Hfrecs Hrecs
  iapply termPos_of_full γ (fp ++ s.log) s.commit s.term ?_ ?_ $$ Hl
  · rw [full_last_index _ _ _ Hfull.1]; exact Hlog_ok.2.2
  · intro j x Hx; exact (Hfull.2.2 j x Hx).1

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
