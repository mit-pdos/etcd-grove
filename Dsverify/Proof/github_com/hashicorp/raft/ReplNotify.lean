/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/ReplNotify.lean (241f27e).
-/
/-
Verify futures in the replication subsystem (stage 2): the followers' notify sets, the heartbeat's
pending futures and their snapshot, vote tokens.

* `notifyInv`: the notify lock's resource (`replShared`'s), `replShared_notify`;
* `pendEntry`: a pending future taken by `heartbeat` before its snapshot `ss` (registered at
  `sv ≼ ss`), `notify_snap` (the snapshot after every pending registration, `gprot.histLb_now`);
* `voteTok_excl` (a voter votes once);
* map helpers (`bigSepM_keys_loc`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The notify lock's resource (`replShared`): the notify map and its registered futures. -/
def notifyInv (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch : Loc) (j : SID) (s : Loc) :
    IProp GF :=
  iprop(∃ (m : GoMap) (M : GMap Loc Unit), s.[followerReplication, go!"notify"] ↦ m ∗ m ↦$ M ∗
    [∗map] v ↦ _u ∈ M, notifyEntry γ rc i T vch j v)

theorem replShared_notify (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID)
    (s : Loc) :
    replShared (GF := GF) r γ rc i T j s ⊢ ∃ vch : Loc, r.[Raft, go!"verifyCh"] ↦□ vch ∗
      sync.isMutex (s.[followerReplication, go!"notifyLock"]) (notifyInv γ rc i T vch j s) := by
  unfold replShared notifyInv
  iintro ⟨%cm, %stopCh, %trig, %notif, %sd, %tde, %γs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, ⟨%vch, #Hv, #Hm⟩⟩
  iexists vch
  iframe #

/-- The replication state's `lastContactLock` (`replShared`). -/
theorem replShared_contact (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID)
    (s : Loc) :
    replShared (GF := GF) r γ rc i T j s ⊢
      rwLock replContactLockN (s.[followerReplication, go!"lastContactLock"])
        (fun q => iprop(∃ t : time.Time, s.[followerReplication, go!"lastContact"] ↦{DFrac.own q} t)) := by
  unfold replShared
  iintro ⟨%cm, %stopCh, %trig, %notif, %sd, %tde, %γs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, #H, -⟩
  iexact H

instance respWit_persistent γ j T ss : Persistent (respWit (GF := GF) γ j T ss) := by
  unfold respWit; infer_instance

instance verifyReg_persistent γ rc i T sv L vch v :
    Persistent (verifyReg (GF := GF) γ rc i T sv L vch v) := by
  unfold verifyReg vregIs; infer_instance

/-- (heartbeat) A verify future taken from the notify set before the heartbeat's snapshot `ss`:
registered by the leader `i` of `T` at `sv ≼ ss` (stage 4: with the leader's log `L`, `j` one of its
latest configuration's voters), with `j`'s vote token. -/
def pendEntry (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch : Loc) (j : SID) (ss : Snap)
    (v : Loc) : IProp GF :=
  iprop(∃ (sv : Snap) (L : RLog), histLb γ sv ∗ ⌜snapLe sv ss⌝ ∗ verifyReg γ rc i T sv L vch v ∗
    voteTok rc v j ∗ ⌜j ∈ cfgOfC γ.cv L⌝)

theorem pendEntry_notify (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch : Loc) (j : SID)
    (ss : Snap) (v : Loc) :
    pendEntry (GF := GF) γ rc i T vch j ss v ⊢ notifyEntry γ rc i T vch j v := by
  unfold pendEntry notifyEntry
  iintro ⟨%sv, %L, Hsv, -, Hreg, Htok, %Hj⟩
  iexists sv, L; iframe; ipureintro; exact Hj

theorem notify_collect (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (vch : Loc) (j : SID) :
    ∀ l : List (Loc × Unit),
    ([∗list] kv ∈ l, notifyEntry (GF := GF) γ rc i T vch j kv.1) ⊢
      ∃ S : List Snap, ([∗list] s ∈ S, histLb γ s) ∗
        [∗list] kv ∈ l, ∃ (sv : Snap) (L : RLog), ⌜sv ∈ S⌝ ∗ histLb γ sv ∗
          verifyReg γ rc i T sv L vch kv.1 ∗ voteTok rc kv.1 j ∗ ⌜j ∈ cfgOfC γ.cv L⌝ := by
  intro l
  induction l with
  | nil =>
    iintro -
    iexists []
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | cons kv l ih =>
    iintro Hl
    ihave ⟨H1, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    iunfold notifyEntry at H1
    icases H1 with ⟨%sv, %L, #Hsv, #Hreg, Htok, %Hj⟩
    ihave ⟨%S, #HS, Hl⟩ := ih $$ Hl
    iexists (sv :: S)
    isplitl []
    · iapply BigSepL.bigSepL_cons.2
      iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitl [Htok]
    · iexists sv, L
      isplitr; · ipureintro; exact List.mem_cons_self
      iframe; iframe #
      ipureintro; exact Hj
    iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hl
    iintro ⟨%sv', %L', %hm, Hs', Hr', Ht', %Hj'⟩
    iexists sv', L'
    isplitr; · ipureintro; exact List.mem_cons_of_mem _ hm
    iframe
    ipureintro; exact Hj'

variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- **The heartbeat's snapshot** (taken after the pending set, before the send): later than the
registration of every pending future. -/
theorem notify_snap (E : CoPset) (hE : ↑gprotN ⊆ E) (γ : GNames) (rc : RCtx GF) (i : SID)
    (T : Nat) (vch : Loc) (j : SID) (M : GMap Loc Unit) :
    Inv (GF := GF) γ ∗ ([∗map] v ↦ _u ∈ M, notifyEntry γ rc i T vch j v) ⊢ |={E}=>
      ∃ ss : Snap, histLb γ ss ∗ [∗map] v ↦ _u ∈ M, pendEntry γ rc i T vch j ss v := by
  iintro ⟨#Hinv, Hm⟩
  ihave Hm := (BigSepM.bigSepM_toList (PROP := IProp GF)).1 $$ Hm
  ihave ⟨%S, #HS, Hl⟩ := notify_collect γ rc i T vch j (toList M) $$ Hm
  ihave Hds : iprop([∗list] p ∈ ([] : List (SID × Nat)), durLb (GF := GF) γ p.1 p.2) $$ []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  imod histLb_now γ E hE S [] (by simp) $$ [Hinv HS Hds] with ⟨%ss, #Hss, %Hle⟩
  · iframe #; iframe
  imodintro
  iexists ss
  iframe #
  iapply (BigSepM.bigSepM_toList (PROP := IProp GF)).2
  iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hl
  unfold pendEntry
  iintro ⟨%sv, %L, %hm, Hs, Hr, Ht, %Hj⟩
  iexists sv, L
  iframe
  isplitr; · ipureintro; exact Hle.1 sv hm
  iframe
  ipureintro; exact Hj

/-- A voter's vote token for `v` is exclusive: it is not among the tokens of the votes counted. -/
theorem voteTok_excl (rc : RCtx GF) (v : Loc) (j : SID) (Q : List SID) (X : SID → IProp GF)
    (h : j ∈ Q) :
    voteTok rc v j ∗ ([∗list] j' ∈ Q, voteTok rc v j' ∗ X j') ⊢ False := by
  obtain ⟨k, hk⟩ := List.getElem?_of_mem h
  iintro ⟨Ht, Hl⟩
  ihave ⟨Ht2, -⟩ := BigSepL.bigSepL_lookup (Φ := fun _ j' => iprop(voteTok rc v j' ∗ X j')) hk $$ Hl
  unfold voteTok
  ihave %Hne := ghostMapElem_ne _ _ _ _ _ _ $$ Ht Ht2
  exact absurd rfl Hne

/-- (Stage 3) To open `raftConf`'s `▷ ∃ cfg`. -/
instance configuration_inhabited : Inhabited Configuration := ⟨Perennial.zero_val Configuration⟩

/- (stage 4) `isRaft_voters_bound` (`|γ.srvs| < 2^32` from the bootstrap configuration) is removed: no longer
derivable (the servers are not a configuration's voters), and its one user (`verifyFuture.vote`) now bounds the
vote count by the registration's `|cfgOfC γ.cv L| < 2 * quorumSize < 2^64` (`verifyReg`). -/

/-- A map's big separating conjunction as one over its keys (any order without duplicates). -/
theorem bigSepM_keys_loc (Ψ : Loc → IProp GF) :
    ∀ (keys : List Loc) (m : GMap Loc Unit), keys.Nodup → (∀ k, k ∈ keys ↔ (m !! k).isSome) →
    ([∗map] k ↦ _u ∈ m, Ψ k) ⊢ [∗list] k ∈ keys, Ψ k := by
  intro keys
  induction keys with
  | nil => intro m _ _; iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons k rest ih =>
    intro m hnd hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hk k).mp List.mem_cons_self)
    iintro Hm
    ihave ⟨Hk, Hm⟩ := (BigSepM.bigSepM_delete (Φ := fun k _ => Ψ k) (m := m) hv).1 $$ Hm
    have hdel : ∀ k', k' ≠ k → (Iris.Std.delete m k) !! k' = m !! k' :=
      fun k' hne => Iris.Std.get?_delete_ne (m := m) (Ne.symm hne)
    have hdelk : (Iris.Std.delete m k) !! k = none := Iris.Std.get?_delete_eq (m := m) rfl
    ihave Hrest := ih (Iris.Std.delete m k) (List.nodup_cons.mp hnd).2 (fun k' => by
      by_cases hk' : k' = k
      · subst hk'; rw [hdelk]; simp; exact (List.nodup_cons.mp hnd).1
      · rw [hdel k' hk', ← hk k']; simp [hk']) $$ Hm
    iapply BigSepL.bigSepL_cons.2
    iframe

end defs

end github_com.hashicorp.raft

end Perennial
