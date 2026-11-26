/-
**The frozen floor** (F7 stage S5, `notes/etcd-dist-f7.md`, "Handoff S5-1", item 3): after the set-up froze the
cluster's auth history at `hs` (`authHistFrozen`, at a committed prefix `Lset` whose auth state is `setupSt r`)
and a barrier left a member's floor above it (`authFloorD … L₀ m`, `Lset <+: L₀`), every state the member
records from the floor on is `setupSt r` (`authFloorD_frozen`): the cross-machine form of the single-process
`akAuthFixed`. Each such state is the history's after a committed prefix `L' ⊒ L₀` (`authFloorD`'s last
conjunct), whose admin states are a lower bound of the history (`authHistLb_of_reqLogLb`, the KV invariant),
so a prefix of the frozen `hs` (`authHistFrozen_prefix`); they extend `Lset`'s, which are `hs`, so they are
`hs`, and the state is `hs`'s last. An anonymous principal's lease check at or above the floor is then
refuted (`leaseCheckD_none_frozen`): `setupSt` has auth enabled, and `P = none` binds no user.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ProposeOn

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd

section pure
variable [GooseExts]

/-- A committed prefix extending `Lset` whose admin states are a prefix of `Lset`'s has `Lset`'s auth state. -/
theorem srvAuthAtLog_frozen (γk : KVNames) (Lset L₀ L' : List EntryModel) (hs : List auth.AuthState)
    (h1 : Lset <+: L₀) (h2 : L₀ <+: L') (hadm : admStates γk srvAuthSt0 Lset = hs)
    (hp : admStates γk srvAuthSt0 L' <+: hs) :
    srvAuthAtLog γk srvAuthSt0 L' = srvAuthAtLog γk srvAuthSt0 Lset := by
  have hq : hs <+: admStates γk srvAuthSt0 L' := hadm ▸ admStates_prefix γk srvAuthSt0 Lset L' (h1.trans h2)
  have heq : admStates γk srvAuthSt0 L' = hs :=
    hp.eq_of_length (Nat.le_antisymm hp.length_le hq.length_le)
  rw [← admStates_getLastD γk srvAuthSt0 L' srvAuthSt0, heq, ← hadm, admStates_getLastD]

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The frozen floor** (see the file header): from the floor's index `i ≤ m` on, member `mid` records only
`setupSt r`. -/
theorem authFloorD_frozen (Γ : DistView) (γR : ServerRaftNames) (mid : w64) (L₀ Lset : List EntryModel)
    (m : Nat) (γz : GName) (hs : List auth.AuthState) (r : Nat) (hLs : Lset <+: L₀)
    (hadm : admStates Γ.kv srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r)
    (E : CoPset) (hE1 : ↑kvN ⊆ E) (hE2 : ↑authHistN ⊆ E) :
    ⊢ kvInvOn (GF := GF) γR Γ.kv srvAuthSt0 -∗ authHistFrozen Γ.kv γz hs -∗ authFloorD Γ γR mid L₀ m -∗
      ∃ i : Nat, ⌜i ≤ m⌝ ∗ □ (∀ (j : Nat) (st : auth.AuthState), ⌜i ≤ j⌝ -∗
        auth.authStateAt (Γ.au mid) j st ={E}=∗ ⌜st = etcd_auth.setupSt r⌝) := by
  iintro #Hinv #Hfz #Hfl
  iunfold authFloorD at Hfl
  icases Hfl with ⟨-, %L, %i, %Hi, -, -, #Hall⟩
  iexists i
  isplitr
  · ipureintro; exact Hi.2
  imodintro
  iintro %j %st %Hj #Hst
  ispecialize Hall $$ %j %st
  ihave ⟨%L', %HL', #HL'lb⟩ := Hall $$ [] Hst
  · ipureintro; exact Hj
  imod authHistLb_of_reqLogLb γR Γ.kv srvAuthSt0 L' E hE1 $$ Hinv HL'lb with #Hlb
  imod authHistFrozen_prefix Γ.kv γz hs _ E hE2 $$ Hfz Hlb with %hp
  imodintro
  ipureintro
  rw [HL'.2, srvAuthAtLog_frozen Γ.kv Lset L₀ L' hs hLs HL'.1 hadm hp, hst]

/-- **An anonymous lease check at or above a frozen floor is refuted**: its disabled arm reads a state
`setupSt r`, which has auth enabled; its info arm binds `none` to a user. -/
theorem leaseCheckD_none_frozen (γa : auth.AuthNames) (i n : Nat) (r : Nat) (hin : i ≤ n) (E : CoPset)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) :
    ⊢ (□ ∀ (j : Nat) (st : auth.AuthState), ⌜i ≤ j⌝ -∗
        auth.authStateAt γa j st ={E}=∗ ⌜st = etcd_auth.setupSt r⌝) -∗
      leaseCheckD γa none n K ={E}=∗ False := by
  simp only [leaseCheckD, auth.enabledVerdictFrom]
  iintro #Hfx Hc
  icases Hc with (⟨%j, %st, #Hst, %Hj⟩ | ⟨%info, %Hp, -⟩)
  · ispecialize Hfx $$ %j %st
    imod Hfx $$ [] Hst with %Heq
    · ipureintro; omega
    subst Heq
    simp [etcd_auth.setupSt] at Hj
  · cases Hp

end ghost

end etcd_dist_client
end EtcdGrove
end Perennial
