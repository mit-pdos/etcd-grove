/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__observe.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).LeaderWithID`: the observers called under `observersLock` (read) (a reader token borrowed from
the lock's thread pool with the thread token).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Perennial.Proof.sync.Results
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.observe.wp_proof :
    github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG) := by
  intro r γ rc i s d tid
  wp_start as ⟨#His, Harg, Htok⟩
  ihave #Hl := isRaft_locks r γ rc i $$ His
  ihave #Hterm := isRaft_termCell r γ rc i $$ His
  unfold raftLocks rwLock
  icases Hl with ⟨-, -, -, ⟨%γp, -, #Hpool⟩, -⟩
  iapply wp_fupd
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  imod qpool.borrow_lc observersLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ (observersP γ i r)) $$ [$Hown] as ⟨Hrl, HP⟩
  iunfold observersP at HP
  icases HP with ⟨%m, %mv, Hm, Hmv, #Hobs⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) (Val _)) (Val _))
  iapply wp_map_for_range (fun _ _ => iprop(obsArg γ i s d ∗ r_ptr ↦ r ∗ o_ptr ↦ d ∗
    ∃ v : Loc, or_ptr ↦ v)) _ go.uint64 _ m mv _ $$ Hmv
  iintro %keys %Hkeys
  isplitl [Harg r o or]
  · iframe
  isplitr
  · imodintro
    iintro %k %key %v %Hkv ⟨Harg, r, o, %v0, or⟩
    ihave #Hov := (BigSepM.bigSepM_lookup Hkv.2) $$ Hobs
    unfold obsOk
    icases Hov with ⟨%fl, %id, #Hch, #Hbl, #Hf, #Hid, #Hfl⟩
    wp_auto
    wp_if_destruct
    · unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iframe
    · wp_bind (App (Val #fl) (Val #ob_ptr))
      iunfold filterOk at Hfl
      iapply Hfl $$ %ob_ptr %s %d %_ Hterm Harg ob
      inext
      iintro %b Harg ob
      wp_auto
      cases b <;> wp_auto
      all_goals
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iframe
  iintro ⟨Harg, -⟩ Hmv
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock _ (observersP γ i r)) $$ [$Hrl Hm Hmv] as Hown
  · inext; iunfold observersP; iexists m, mv; iframe; iframe #
  imod qpool.giveBack observersLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
    with Htok
  imodintro
  iapply HΦ; iframe

end proof

end Perennial
