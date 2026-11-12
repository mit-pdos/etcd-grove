/-
# Deciding conf entries by a rule: a client library over raft's decisions (2026-10-28)

The conf-change decision switch, §2 (`notes/spec-first-study/raft-decisions-spec.md`). Raft's API
mentions no rule: a cluster's conf entries are decided by the client, once per position
(`ownConfDecisions`, `confDecide`, `InvNodeRule.lean`). A client that decides by a rule `r` (as
kv does) keeps the authority in an invariant (`confPolicy γ N' r`, persistent), with, for each
recorded decision, the facts making it the rule's answer at its prefix and membership; then any
caller, at a committed conf entry and the membership before it, obtains the rule's decision
(`confPolicy_decide`): the recorded one if the position is decided (the same at every caller), else
recorded now.

Outside raft's kernel: built on `InvNodeRule`'s laws (`ownConfDecisions_witness`, `confDecide`,
`confAt_agree`) and `InvNode`'s `isCommittedLogLb_agree`, it unseals nothing.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section policy
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem take_eq_of_cmp' {α : Type} (l1 l2 : List α) (k : Nat) (h : l1 <+: l2 ∨ l2 <+: l1)
    (h1 : k ≤ l1.length) (h2 : k ≤ l2.length) : l1.take k = l2.take k := by
  rcases h with h | h
  · rw [List.prefix_iff_eq_take.1 h, List.take_take, Nat.min_eq_left h1]
  · rw [List.prefix_iff_eq_take.1 h, List.take_take, Nat.min_eq_left h2]

private theorem getElem?_eq_of_cmp' {α : Type} (l1 l2 : List α) (k : Nat) (h : l1 <+: l2 ∨ l2 <+: l1)
    (h1 : k < l1.length) (h2 : k < l2.length) : l1[k]? = l2[k]? := by
  have := take_eq_of_cmp' l1 l2 (k + 1) h h1 h2
  have e1 : (l1.take (k + 1))[k]? = l1[k]? := by rw [List.getElem?_take]; simp
  have e2 : (l2.take (k + 1))[k]? = l2[k]? := by rw [List.getElem?_take]; simp
  rw [← e1, ← e2, this]

/-- A recorded decision is the rule's answer at its position: at a committed conf entry `e`, the
membership `m` before it. -/
def policyRec (γ : Cluster) (r : ConfRule) (k : Nat) (d : ConfDecision) : IProp GF :=
  iprop(∃ (l : List LogEntry) (e : LogEntry) (m : Membership), isCommittedLogLb γ l ∗ confAt γ k m ∗
    ⌜l[k]? = some e ∧ d = ConfDecision.ofRule (r (l.take k) m e)⌝)

instance policyRec_persistent (γ : Cluster) (r : ConfRule) (k : Nat) (d : ConfDecision) :
    Persistent (policyRec (GF := GF) γ r k d) := by
  unfold policyRec; infer_instance

instance policyRec_timeless (γ : Cluster) (r : ConfRule) (k : Nat) (d : ConfDecision) :
    Timeless (policyRec (GF := GF) γ r k d) := by
  unfold policyRec; infer_instance

/-- The invariant's body: the decisions, each the rule's. -/
def confPolicyBody (γ : Cluster) (r : ConfRule) : IProp GF :=
  iprop(∃ D : GMap Nat ConfDecision, ownConfDecisions γ D ∗
    □ (∀ (k : Nat) (d : ConfDecision), ⌜D !! k = some d⌝ -∗ policyRec γ r k d))

/-- **The cluster's conf entries are decided by the rule `r`** (persistent): the authority over the
decisions in an invariant at `N'`, each decision the rule's at its prefix and membership. -/
@[no_expose] def confPolicy (γ : Cluster) (N' : Namespace) (r : ConfRule) : IProp GF :=
  inv N' (confPolicyBody γ r)

instance confPolicy_persistent (γ : Cluster) (N' : Namespace) (r : ConfRule) :
    Persistent (confPolicy (GF := GF) γ N' r) := by
  unfold confPolicy; infer_instance

/-- **Handing the decisions to a rule**: the authority, with none recorded, into the invariant. -/
theorem confPolicy_alloc (γ : Cluster) (N' : Namespace) (r : ConfRule) (E : CoPset) :
    ⊢ ownConfDecisions (GF := GF) γ ∅ ={E}=∗ confPolicy γ N' r := by
  iintro Hown
  unfold confPolicy
  iapply inv_alloc
  inext
  unfold confPolicyBody
  iexists ∅
  iframe Hown
  imodintro
  iintro %k %d %h
  exact absurd h (by simp)

/-- **The rule's decision on a committed conf entry** `e` at position `k`, where the membership is
`m`: the recorded decision if the position is decided (the same at every caller), else decided now.
The caller shows the rule's answer allowed at `m` (per call: no global premise on `r`). -/
theorem confPolicy_decide (γ : Cluster) (N N' : Namespace) (E : CoPset) (r : ConfRule)
    (l : List LogEntry) (k : Nat) (e : LogEntry) (m m' : Membership) :
    l[k]? = some e → e.isConfChange → ↑N' ⊆ E →
    (ConfDecision.ofRule (r (l.take k) m e)).step m = some m' →
    ⊢ isCluster (GF := GF) γ N ∗ confPolicy γ N' r ∗ isCommittedLogLb γ l ∗ confAt γ k m ={E}=∗
      confDecided γ k (ConfDecision.ofRule (r (l.take k) m e)) := by
  intro he hc HE hs
  iintro ⟨#Hc, #Hp, #Hl, #Ha⟩
  unfold confPolicy
  simp only [confPolicyBody]
  iinv Hp with ⟨%D, >Hown, >#Hall⟩ Hclose
  cases hD : D !! k with
  | some d =>
    -- decided: the rule's answer at the recorded prefix and membership, which are the caller's
    ihave #Hrec := Hall $$ %k %d %hD
    unfold policyRec
    icases Hrec with ⟨%l', %e', %m'', #Hl', #Ha', %P⟩
    obtain ⟨he', hd⟩ := P
    icases isCommittedLogLb_agree γ l l' $$ [Hl Hl'] with %Hcmp
    · iframe Hl Hl'
    icases confAt_agree γ k m m'' $$ [Ha Ha'] with %Hm
    · iframe Ha Ha'
    subst Hm
    have hk : k < l.length := (List.getElem?_eq_some_iff.mp he).1
    have hk' : k < l'.length := (List.getElem?_eq_some_iff.mp he').1
    have Ht : l.take k = l'.take k := take_eq_of_cmp' l l' k Hcmp (by omega) (by omega)
    have Hee : e = e' := by
      have := getElem?_eq_of_cmp' l l' k Hcmp hk hk'
      rw [he, he'] at this; exact Option.some.inj this
    subst Hee
    rw [← Ht] at hd
    subst hd
    icases ownConfDecisions_witness γ D k _ hD $$ Hown with ⟨Hown, #Hd⟩
    imod Hclose $$ [Hown] with -
    · inext
      iexists D
      iframe Hown Hall
    imodintro
    iexact Hd
  | none =>
    -- undecided: the rule's answer recorded now
    imod confDecide γ N D l k e m m' _ hD he hc hs $$ [Hc Hl Ha Hown] with ⟨Hown, #Hd, -⟩
    · iframe Hc Hl Ha Hown
    imod Hclose $$ [Hown] with -
    · inext
      iexists D.insert k (ConfDecision.ofRule (r (l.take k) m e))
      iframe Hown
      imodintro
      iintro %k' %d' %hk'
      by_cases hkk : k = k'
      · subst hkk
        have : d' = ConfDecision.ofRule (r (l.take k) m e) := by
          have h2 : (D.insert k (ConfDecision.ofRule (r (l.take k) m e))) !! k = some d' := hk'
          rw [GMap.lookup_insert] at h2; exact (Option.some.inj h2).symm
        subst this
        unfold policyRec
        iexists l, e, m
        iframe Hl Ha
        ipureintro; exact ⟨he, rfl⟩
      · have h2 : (D.insert k (ConfDecision.ofRule (r (l.take k) m e))) !! k' = some d' := hk'
        rw [GMap.lookup_insert_ne _ _ hkk] at h2
        iapply Hall $$ %k' %d' %h2
    imodintro
    iexact Hd

end policy

end EtcdGrove
end Perennial
