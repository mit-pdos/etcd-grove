/-
# Raft's node API: a cluster of a conf-change rule, with snapshots (2026-10-28, stage U4a)

The definitions behind `InvNodeRule.lean`'s sealed predicates, and the proofs of their laws
(`*_impl`): raft's dynamic mode of a rule `r` from the initial membership `c0` (`ConfRule.toDec`),
outside the no-snapshot mode, with the registry of the snapshots the client made (`RuleNames`,
`SnapsMade.lean`).

- **A cluster** (`isClusterU`): its nodes in the dynamic mode of some rule and initial membership
  (`ModeRule`), with snapshots, a registry, no snapshot directories. The rule is not a parameter:
  candidate 13's decisions will replace it (`notes/spec-first-study/raft-node-unified-candidate-13.md`,
  section 13); a client reads the configuration through `confAtU` (the membership after the first
  `k` committed entries) and `confDecidedU` (the decision on the conf entry at position `k`), and
  obtains decisions from the rule it allocated the cluster with (`confPolicyU`, the interim stand-in
  for candidate 13's `confPolicyInv`).
- Two rules of one cluster fold every log alike (`ModeRule.fold_eq`): the predicates name the rule
  existentially and agree.
-/
module

public import Proof.go_etcd_io.raft.v3.SnapsMade
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Pure lemmas -/

section pure
variable [GooseExts]

/-- Two comparable lists agree below both lengths. -/
theorem take_eq_of_cmp {α : Type} (l1 l2 : List α) (k : Nat) (h : l1 <+: l2 ∨ l2 <+: l1)
    (h1 : k ≤ l1.length) (h2 : k ≤ l2.length) : l1.take k = l2.take k := by
  rcases h with h | h
  · rw [List.prefix_iff_eq_take.1 h, List.take_take, Nat.min_eq_left h1]
  · rw [List.prefix_iff_eq_take.1 h, List.take_take, Nat.min_eq_left h2]

theorem getElem?_eq_of_cmp {α : Type} (l1 l2 : List α) (k : Nat) (h : l1 <+: l2 ∨ l2 <+: l1)
    (h1 : k < l1.length) (h2 : k < l2.length) : l1[k]? = l2[k]? := by
  have := take_eq_of_cmp l1 l2 (k + 1) h h1 h2
  have e1 : (l1.take (k + 1))[k]? = l1[k]? := by rw [List.getElem?_take]; simp
  have e2 : (l2.take (k + 1))[k]? = l2[k]? := by rw [List.getElem?_take]; simp
  rw [← e1, ← e2, this]

theorem take_succ_of_getElem? {α : Type} (l : List α) (k : Nat) (e : α) (h : l[k]? = some e) :
    l.take (k + 1) = l.take k ++ [e] := by
  rw [List.take_add_one, h]; rfl

/-- The rule's fold past positions with no conf entry. -/
theorem fold_take_noConf (r : ConfRule) (c0 : Membership) (l : List LogEntry) (a b : Nat)
    (hn : NoConfChangeIn l a b) (hab : a ≤ b) (hb : b ≤ l.length) :
    Membership.fold r c0 (l.take b) = Membership.fold r c0 (l.take a) := by
  induction b with
  | zero => rw [Nat.le_zero.1 hab]
  | succ b ih =>
    rcases Nat.lt_or_ge b a with h | h
    · rw [show a = b + 1 by omega]
    have hlt : b < l.length := by omega
    obtain ⟨e, he⟩ : ∃ e, l[b]? = some e := ⟨l[b], List.getElem?_eq_getElem hlt⟩
    rw [take_succ_of_getElem? l b e he,
      Membership.fold_snoc_normal r c0 _ e (hn b e h (by omega) he)]
    exact ih (fun k e' h1 h2 he' => hn k e' h1 (by omega) he') h (by omega)

/-- A decision as the rule gives it, up to the change's effect (`AsV2`'s form). -/
def DecMatch : Option ConfChangeIM → ConfDecision → Prop
  | none, .skip => True
  | some o, .apply o' => ccV2Of o = ccV2Of o'
  | _, _ => False

theorem decMatch_ofRule (x : Option ConfChangeIM) : DecMatch x (ConfDecision.ofRule x) := by
  cases x <;> trivial

/-- The fold's step at a decided conf entry is the decision's. -/
theorem foldStep_decMatch (r : ConfRule) (pre : List LogEntry) (m : Membership) (e : LogEntry)
    (d : ConfDecision) (hc : e.isConfChange) (hd : DecMatch (r pre m e) d) :
    Membership.foldStep r pre m e = d.step m := by
  unfold Membership.foldStep
  rw [ite_eq_left hc]
  cases h : r pre m e with
  | none =>
    rw [h] at hd
    cases d with
    | skip => rfl
    | apply o => exact absurd hd id
  | some o =>
    rw [h] at hd
    cases d with
    | skip => exact absurd hd id
    | apply o' =>
      show memApply o m = memApply o' m
      unfold memApply; rw [show ccV2Of o = ccV2Of o' from hd]

end pure

/-! ## The cluster's names -/

section names
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The cluster's names are of the rule `r` from `c0`: its snapshot names (`RuleNames`) and its
nodes' mode the rule's. -/
def ModeRule (γ : Cluster) (r : ConfRule) (c0 : Membership) : Prop :=
  RuleNames γ r c0 ∧ ∃ h0 h1, γ.mode = (RNMode.dyn (r.toDec c0) (stOf c0) h0 h1).all

theorem ModeRule.mode {γ : Cluster} {r : ConfRule} {c0 : Membership} (h : ModeRule γ r c0) :
    ∃ h0 h1, γ.mode inferInstance = RNMode.dyn (r.toDec c0) (stOf c0) h0 h1 := by
  obtain ⟨-, h0, h1, hm⟩ := h
  exact ⟨h0, h1, by rw [hm, RNMode.all_self]⟩

theorem ModeRule.valid {γ : Cluster} {r : ConfRule} {c0 : Membership} (h : ModeRule γ r c0) :
    c0.Valid := by
  obtain ⟨⟨-, hv, -⟩, -⟩ := h; exact hv

theorem cfgOf_inj {m1 m2 : Membership} (h : cfgOf m1 = cfgOf m2) : m1 = m2 := by
  rw [← memOf_cfgOf m1, h, memOf_cfgOf]

/-- **Two rules of one cluster fold every log alike.** -/
theorem ModeRule.fold_eq {γ : Cluster} {r1 r2 : ConfRule} {c1 c2 : Membership}
    (h1 : ModeRule γ r1 c1) (h2 : ModeRule γ r2 c2) (l : List LogEntry) :
    Membership.fold r1 c1 l = Membership.fold r2 c2 l := by
  have hr1 := h1.1
  have hr2 := h2.1
  obtain ⟨h01, -, hd1, -⟩ := h1.1
  have e1 := hr1.fold _ hd1 (LogEntry.toEntries l 0)
  have e2 := hr2.fold _ hd1 (LogEntry.toEntries l 0)
  rw [strip_toEntries] at e1 e2
  rw [e1] at e2
  cases f1 : Membership.fold r1 c1 l with
  | none =>
    rw [f1] at e2
    cases f2 : Membership.fold r2 c2 l with
    | none => rfl
    | some _ => rw [f2] at e2; cases e2
  | some m1 =>
    rw [f1] at e2
    cases f2 : Membership.fold r2 c2 l with
    | none => rw [f2] at e2; cases e2
    | some m2 =>
      rw [f2] at e2
      simp only [Option.map_some, Option.some.injEq] at e2
      rw [cfgOf_inj e2]

/-- What a cluster's names say (the `isClusterU` of `InvNodeRule`): its nodes in the dynamic mode
of a rule, with snapshots and a registry of them, no snapshot directories, the storages'
certificate registries in `N`. -/
def UniNames (γ : Cluster) (N : Namespace) : Prop :=
  (∃ r c0, ModeRule γ r c0) ∧ γ.raft.reSnapLoc = (fun _ => none) ∧ γ.raft.reCertNs = N

/-- **A cluster of a rule, with snapshots** (`InvNodeRule`'s `isCluster`). -/
def isClusterU (γ : Cluster) (N : Namespace) : IProp GF :=
  iprop(⌜UniNames γ N⌝ ∗ clusterInv γ N)

instance isClusterU_persistent (γ : Cluster) (N : Namespace) :
    Persistent (isClusterU (GF := GF) γ N) := by
  unfold isClusterU; infer_instance

/-- **The membership after the first `k` committed entries is `m`** (`InvNodeRule`'s `confAt`). -/
def confAtU (γ : Cluster) (k : Nat) (m : Membership) : IProp GF :=
  iprop(∃ l : List LogEntry, isCommittedLogLb γ l ∗
    ⌜k ≤ l.length ∧ ∃ r c0, ModeRule γ r c0 ∧ Membership.fold r c0 (l.take k) = some m⌝)

instance confAtU_persistent (γ : Cluster) (k : Nat) (m : Membership) :
    Persistent (confAtU (GF := GF) γ k m) := by
  unfold confAtU; infer_instance

/-- **The conf entry at position `k` of the committed log was decided `d`** (`InvNodeRule`'s
`confDecided`): the rule's decision there, up to the change's effect (`DecMatch`), and the membership
after it defined. -/
def confDecidedU (γ : Cluster) (k : Nat) (d : ConfDecision) : IProp GF :=
  iprop(∃ l : List LogEntry, isCommittedLogLb γ l ∗
    ⌜∃ e, l[k]? = some e ∧ e.isConfChange ∧ ∃ r c0, ModeRule γ r c0 ∧ ∃ m m',
      Membership.fold r c0 (l.take k) = some m ∧ Membership.fold r c0 (l.take (k + 1)) = some m' ∧
      DecMatch (r (l.take k) m e) d⌝)

instance confDecidedU_persistent (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Persistent (confDecidedU (GF := GF) γ k d) := by
  unfold confDecidedU; infer_instance

/-- **The cluster decides by the rule `r`** (`InvNodeRule`'s `confPolicy`). -/
def confPolicyU (γ : Cluster) (r : ConfRule) : IProp GF :=
  iprop(⌜∃ c0, ModeRule γ r c0⌝)

instance confPolicyU_persistent (γ : Cluster) (r : ConfRule) :
    Persistent (confPolicyU (GF := GF) γ r) := by
  unfold confPolicyU; infer_instance

/-- **The snapshots the client made** (`InvNodeRule`'s `ownSnapsMade`), of the cluster's rule. -/
def ownSnapsMadeU (γ : Cluster) (S : List SnapRec) : IProp GF :=
  iprop(∃ r c0, ⌜ModeRule γ r c0⌝ ∗ ownSnapsMade γ r c0 S)

/-- **The snapshot `s` was made** (`InvNodeRule`'s `snapMade`; persistent). -/
def snapMadeU (γ : Cluster) (s : SnapRec) : IProp GF :=
  iprop(∃ r c0, ⌜ModeRule γ r c0⌝ ∗ snapMade γ r c0 s)

instance snapMadeU_persistent (γ : Cluster) (s : SnapRec) :
    Persistent (snapMadeU (GF := GF) γ s) := by
  unfold snapMadeU; infer_instance

/-- **A founder's boot token** (`InvNodeRule`'s `nodeFounder`): node `id` of a cluster of the voters
`vs` (its initial membership theirs), raft's ghost state at the initial state, the empty log
committed, the term budget, and the node's table, empty. What its `RestartNode` takes. -/
def nodeFounderU (γ : Cluster) (N : Namespace) (vs : List w64) (id : w64) : IProp GF :=
  iprop(isClusterU γ N ∗
    ⌜γ.raft.reCfg = GMap.listToSet vs ∧ (∃ r, ModeRule γ r (Membership.simple (GMap.listToSet vs))) ∧
      vs ≠ [] ∧ vs.Nodup ∧ W64 0 ∉ vs ∧ (vs.length : Int) < 2 ^ 62⌝ ∗
    ownRaftGhost γ.raft id initPState true ∗ isCommitted γ.raft [] ∗
    inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 0) ∗
    (∃ g : GName, ⌜γ.nodeTab !! id = some g⌝ ∗ ghostMapAuth g 1 (∅ : GMap w64 CfgNames)))

/-- A fresh node's dynamic ghost state, from the allocation's (as `raft_dyn_alloc`'s). -/
theorem ownRaftGhostR_rinit (γr : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64) :
    ownRaftGhost (GF := GF) γr id initPState true ⊢ ownRaftGhostR γr dec c0 id (rinit c0) := by
  iintro Hg
  unfold ownRaftGhostR
  rw [show (rinit c0).p = initPState from rfl]
  iframe Hg
  isplitr; · ipureintro; exact RInv_rinit dec c0
  isplitr
  · unfold logRecs rinit
    iapply (BigSepL.bigSepL_nil).2; iempintro
  iintro %h
  exfalso; exact absurd h (by simp [initPState])

/-! ## The laws -/

theorem confAt_agree_impl (γ : Cluster) (k : Nat) (m1 m2 : Membership) :
    confAtU (GF := GF) γ k m1 ∗ confAtU γ k m2 ⊢ ⌜m1 = m2⌝ := by
  unfold confAtU
  iintro ⟨⟨%l1, #H1, %P1⟩, ⟨%l2, #H2, %P2⟩⟩
  icases isCommittedLogLb_agree_impl γ l1 l2 $$ [H1 H2] with %Hc
  · iframe H1 H2
  ipureintro
  obtain ⟨hk1, r1, c1, hm1, hf1⟩ := P1
  obtain ⟨hk2, r2, c2, hm2, hf2⟩ := P2
  rw [take_eq_of_cmp l1 l2 k Hc hk1 hk2, hm1.fold_eq hm2] at hf1
  rw [hf1] at hf2
  exact Option.some.inj hf2

theorem confAt_valid_impl (γ : Cluster) (k : Nat) (m : Membership) :
    confAtU (GF := GF) γ k m ⊢ ⌜m.Valid⌝ := by
  unfold confAtU
  iintro ⟨%l, -, %P⟩
  ipureintro
  obtain ⟨-, r, c0, hm, hf⟩ := P
  exact Membership.fold_valid r c0 m _ hm.valid hf

theorem confAt_noConf_impl (γ : Cluster) (l : List LogEntry) (a b : Nat) (m : Membership) :
    NoConfChangeIn l a b → a ≤ b → b ≤ l.length →
    isCommittedLogLb (GF := GF) γ l ∗ confAtU γ a m ⊢ confAtU γ b m := by
  intro hn hab hb
  unfold confAtU
  iintro ⟨#Hl, %l1, #H1, %P1⟩
  icases isCommittedLogLb_agree_impl γ l l1 $$ [Hl H1] with %Hc
  · iframe Hl H1
  iexists l
  iframe Hl
  ipureintro
  obtain ⟨hk1, r, c0, hm, hf⟩ := P1
  refine ⟨hb, r, c0, hm, ?_⟩
  rw [fold_take_noConf r c0 l a b hn hab hb,
    take_eq_of_cmp l l1 a Hc (by omega) hk1]
  exact hf

theorem confAt_decided_impl (γ : Cluster) (k : Nat) (m : Membership) (d : ConfDecision) :
    confAtU (GF := GF) γ k m ∗ confDecidedU γ k d ⊢
      ∃ m', ⌜d.step m = some m'⌝ ∗ confAtU γ (k + 1) m' := by
  unfold confAtU confDecidedU
  iintro ⟨⟨%l1, #H1, %P1⟩, ⟨%l, #H, %P⟩⟩
  icases isCommittedLogLb_agree_impl γ l l1 $$ [H H1] with %Hc
  · iframe H H1
  obtain ⟨hk1, r1, c1, hm1, hf1⟩ := P1
  obtain ⟨e, he, hce, r, c0, hm, m2, m', hf, hf', hd⟩ := P
  have hkl : k < l.length := (List.getElem?_eq_some_iff.mp he).1
  have Hm : m2 = m := by
    rw [take_eq_of_cmp l l1 k Hc (by omega) hk1, hm.fold_eq hm1] at hf
    rw [hf] at hf1; exact Option.some.inj hf1
  subst Hm
  have Hs : d.step m2 = some m' := by
    rw [take_succ_of_getElem? l k e he, Membership.fold_snoc, hf, Option.bind_some,
      foldStep_decMatch r _ m2 e d hce hd] at hf'
    exact hf'
  iexists m'
  isplitr; · ipureintro; exact Hs
  iexists l
  iframe H
  ipureintro
  exact ⟨hkl, r, c0, hm, hf'⟩

theorem confPolicy_decide_impl (γ : Cluster) (r : ConfRule) (l : List LogEntry) (k : Nat)
    (e : LogEntry) (m m' : Membership) :
    l[k]? = some e → e.isConfChange →
    (ConfDecision.ofRule (r (l.take k) m e)).step m = some m' →
    confPolicyU (GF := GF) γ r ∗ isCommittedLogLb γ l ∗ confAtU γ k m ⊢
      confDecidedU γ k (ConfDecision.ofRule (r (l.take k) m e)) := by
  intro he hce hst
  unfold confPolicyU confAtU confDecidedU
  iintro ⟨%Hp, #Hl, %l1, #H1, %P1⟩
  icases isCommittedLogLb_agree_impl γ l l1 $$ [Hl H1] with %Hc
  · iframe Hl H1
  iexists l
  iframe Hl
  ipureintro
  obtain ⟨c0, hm⟩ := Hp
  obtain ⟨hk1, r1, c1, hm1, hf1⟩ := P1
  have hkl : k < l.length := (List.getElem?_eq_some_iff.mp he).1
  have hf : Membership.fold r c0 (l.take k) = some m := by
    rw [take_eq_of_cmp l l1 k Hc (by omega) hk1, hm.fold_eq hm1]; exact hf1
  refine ⟨e, he, hce, r, c0, hm, m, m', hf, ?_, decMatch_ofRule _⟩
  rw [take_succ_of_getElem? l k e he, Membership.fold_snoc, hf, Option.bind_some,
    foldStep_decMatch r _ m e _ hce (decMatch_ofRule _)]
  exact hst

/-- A record's configuration, of one rule of the cluster, is of any other. -/
theorem snapConfAt_conv (γ : Cluster) (r1 r2 : ConfRule) (c1 c2 : Membership) (s : SnapRec)
    (h1 : ModeRule γ r1 c1) (h2 : ModeRule γ r2 c2) :
    snapConfAt (GF := GF) γ r1 c1 s ⊢ snapConfAt γ r2 c2 s := by
  unfold snapConfAt
  iintro ⟨%l, #Hl, %P⟩
  iexists l
  iframe Hl
  ipureintro
  rw [← h1.fold_eq h2]; exact P

theorem snapMade_elem_impl (γ : Cluster) (S : List SnapRec) (s : SnapRec) :
    ownSnapsMadeU (GF := GF) γ S ∗ snapMadeU γ s ⊢ ⌜s ∈ S⌝ := by
  unfold ownSnapsMadeU snapMadeU
  iintro ⟨⟨%r1, %c1, %h1, Hown⟩, ⟨%r2, %c2, %h2, #Hs⟩⟩
  ihave #Hs' : snapMade (GF := GF) γ r1 c1 s $$ [Hs]
  · unfold snapMade
    icases Hs with ⟨%g, %K, %key, %Hk, #Hlb, #Hc⟩
    iexists g, K, key
    iframe Hlb
    isplitr; · ipureintro; exact Hk
    iapply snapConfAt_conv γ r2 r1 c2 c1 s h2 h1 $$ Hc
  iapply snapMade_elem γ r1 c1 S s $$ [Hown Hs']
  iframe Hown Hs'

/-- **Certifying a snapshot of a committed prefix** (`InvNodeRule`'s `snapshotCert_make`): its
configuration the membership after the prefix (`confAtU`). -/
theorem snapshotCert_make_impl (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (l : List LogEntry) (i t : w64) (d : List w8) (m : Membership) (cs : ConfStateM)
    (S : List SnapRec) :
    l.length = uint.nat i → Option.map LogEntry.term l.getLast? = some t →
    SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ → confStateIs cs m →
    ⊢ isClusterU (GF := GF) γ N -∗ isCommittedLogLb γ l -∗ confAtU γ l.length m -∗
      ownSnapsMadeU γ S ={E}=∗
      ownSnapsMadeU γ (S ++ [⟨l.length, m, d⟩]) ∗
      snapshotCert γ N ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ := by
  intro Hlen Hlast Hok Hcs
  iintro #Hc #Hl #Ha Hown
  ihave %Hf : ⌜∀ r c0, ModeRule γ r c0 → Membership.fold r c0 l = some m⌝ $$ [Hl Ha]
  · unfold confAtU
    icases Ha with ⟨%l1, #H1, %P1⟩
    icases isCommittedLogLb_agree_impl γ l l1 $$ [Hl H1] with %Hcm
    · iframe Hl H1
    ipureintro
    intro r c0 hm
    obtain ⟨hk1, r1, c1, hm1, hf1⟩ := P1
    rw [← List.take_length (l := l), take_eq_of_cmp l l1 l.length Hcm (Nat.le_refl _) hk1,
      hm.fold_eq hm1]
    exact hf1
  unfold isClusterU
  icases Hc with ⟨-, #Hci⟩
  unfold ownSnapsMadeU
  icases Hown with ⟨%r, %c0, %hm, Hown⟩
  imod snapshotCert_make γ N E HE r c0 l i t d m cs S hm.1 Hlen Hlast Hok (Hf r c0 hm) Hcs
    $$ Hci Hl Hown with ⟨Hown, #Hcert⟩
  imodintro
  iframe Hcert
  iexists r, c0
  iframe Hown
  ipureintro; exact hm

/-- **What a certificate says** (`InvNodeRule`'s `snapshotCert_made`). -/
theorem snapshotCert_made_impl (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    isClusterU (GF := GF) γ N ∗ snapshotCert γ N k ⊢
      ∃ (l : List LogEntry) (m : Membership), isCommittedLogLb γ l ∗ confAtU γ l.length m ∗
        snapMadeU γ ⟨l.length, m, k.dat⟩ ∗
        ⌜l.length = uint.nat k.sid.index' ∧ Option.map LogEntry.term l.getLast? = some k.sid.term' ∧
          k.cl.Is m ∧ k.al = m.autoLeave⌝ := by
  unfold isClusterU
  iintro ⟨⟨%Hu, -⟩, #Hk⟩
  obtain ⟨⟨r, c0, hm⟩, -⟩ := Hu
  icases snapshotCert_made γ N r c0 k hm.1 $$ Hk with ⟨%l, %m, #Hl, #Hs, %P⟩
  obtain ⟨Hlen, Hlast, Hf, Hcl, Hal⟩ := P
  iexists l, m
  iframe Hl
  isplitr
  · unfold confAtU
    iexists l
    iframe Hl
    ipureintro
    exact ⟨Nat.le_refl _, r, c0, hm, by rw [List.take_length]; exact Hf⟩
  isplitr
  · unfold snapMadeU; iexists r, c0; iframe Hs; ipureintro; exact hm
  ipureintro; exact ⟨Hlen, Hlast, Hcl, Hal⟩

end names

end ApiImpl
end EtcdGrove
end Perennial
