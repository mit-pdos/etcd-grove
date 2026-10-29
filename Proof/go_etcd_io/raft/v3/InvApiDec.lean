/-
# Raft's node API: a cluster of client-written conf-change decisions, with snapshots (2026-10-28)

The definitions behind `InvNodeRule.lean`'s sealed predicates, and the proofs of their laws
(`*_impl`), for the conf-change decision switch (`notes/spec-first-study/raft-decisions-spec.md`, §1):
raft's dynamic mode of the base decoder that decides nothing (`noDec`) from the initial membership
`c0`, over the client's decision map (`RaftNames.reDec = some g`, a ghost map of persistent
elements), outside the no-snapshot mode, with the registry of the snapshots the client made.

- **The names** (`ModeDec γ c0 g`): `c0` and `g` are the cluster's, unique (`ModeDec.uniq`).
- **The configuration** (`confAtU γ k m`): the membership after the first `k` committed entries is
  the fold of some recorded decisions (`decLb`, `decFold`); two agree (`confAt_agree_impl`: the
  decisions are lower bounds of one map, `decLb_compat`).
- **Decisions** (`confDecidedU γ k d`): the map's element at `k` (`d.toOpt`), at a committed conf
  entry, with its step defined at the membership before it. `ownConfDecisionsU γ D`: the map's
  authority at `D` and every binding's `confDecidedU`; `confDecide_impl` inserts an undecided one.
- **Snapshots** (TaDa style): the registry of the snapshots made, each record's configuration a
  `confAtU` (`ownSnapsMadeU`, `snapMadeU`); `snapshotCert_make_impl`, `snapshotCert_made_impl`.

(Replaces `InvApiRule.lean`, stage U4a's interim cluster of a rule fixed at allocation.)
-/
module

public import Proof.go_etcd_io.raft.v3.DecFold
public import Proof.go_etcd_io.raft.v3.SnapsMade
public import Proof.go_etcd_io.raft.v3.Protocol.SnapCertDyn
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section names
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The cluster's names -/

/-- What the laws need of the cluster's names: raft's dynamic mode of the base decoder that decides
nothing from `c0` (`noDec`), snapshots on, every data admitted, a registry of the snapshots made,
and the client's decision map `g`. -/
def DecNames (γ : Cluster) (c0 : Membership) (g : GName) : Prop :=
  ∃ (h0 : CfgOk (stOf c0)), c0.Valid ∧
    γ.raft.dyn = some (DynCfg.ofFold noDec (stOf c0) h0) ∧
    γ.raft.reNoSnap = false ∧ (∀ L d, γ.raft.reSnapOkRaw L d) ∧ γ.raft.reSnapReg ≠ none ∧
    γ.raft.reDec = some g

/-- The cluster's names, and its nodes' mode the names' (`RNMode.all`). -/
def ModeDec (γ : Cluster) (c0 : Membership) (g : GName) : Prop :=
  DecNames γ c0 g ∧ ∃ h0 h1, γ.mode = (RNMode.dyn noDec (stOf c0) h0 h1).all

theorem ModeDec.mode {γ : Cluster} {c0 : Membership} {g : GName} (h : ModeDec γ c0 g) :
    ∃ h0 h1, γ.mode inferInstance = RNMode.dyn noDec (stOf c0) h0 h1 := by
  obtain ⟨-, h0, h1, hm⟩ := h
  exact ⟨h0, h1, by rw [hm, RNMode.all_self]⟩

theorem ModeDec.valid {γ : Cluster} {c0 : Membership} {g : GName} (h : ModeDec γ c0 g) :
    c0.Valid := by
  obtain ⟨⟨-, hv, -⟩, -⟩ := h; exact hv

theorem cfgOf_inj {m1 m2 : Membership} (h : cfgOf m1 = cfgOf m2) : m1 = m2 := by
  rw [← memOf_cfgOf m1, h, memOf_cfgOf]

/-- **The names' initial membership and decision map are the cluster's.** -/
theorem ModeDec.uniq {γ : Cluster} {c1 c2 : Membership} {g1 g2 : GName}
    (h1 : ModeDec γ c1 g1) (h2 : ModeDec γ c2 g2) : c1 = c2 ∧ g1 = g2 := by
  obtain ⟨⟨h01, -, hd1, -, -, -, hg1⟩, -⟩ := h1
  obtain ⟨⟨h02, -, hd2, -, -, -, hg2⟩, -⟩ := h2
  refine ⟨?_, by rw [hg1] at hg2; exact Option.some.inj hg2⟩
  rw [hd1] at hd2
  have e := congrArg (fun D : DynCfg => D.fold ∅ []) (Option.some.inj hd2)
  simp only [DynCfg.ofFold] at e
  have e' : some (stOf c1).cfg = some (stOf c2).cfg := e
  exact cfgOf_inj (Option.some.inj e')

/-- The mode's fold, over the decisions `M`, is `decFold`'s, from a valid `c0`. -/
theorem ModeDec.fold {γ : Cluster} {c0 : Membership} {g : GName} (h : ModeDec γ c0 g)
    (D : DynCfg) (hD : γ.raft.dyn = some D) (M : DecMap) (L : List EntryM) :
    D.fold M L = (decFold M c0 (strip L)).map cfgOf := by
  obtain ⟨⟨h0, hv, hd, -⟩, -⟩ := h
  rw [hd] at hD
  cases hD
  show (cfgFold (effDec noDec M) (stOf c0) L).map (fun s => s.cfg) = _
  rw [cfgFold_decs M c0 hv L, Option.map_map]
  rfl

/-- What a cluster's names say (the `isCluster` of `InvNodeRule`): its nodes in the dynamic mode of
the client's decisions, with snapshots and a registry of them, no snapshot directories, the storages'
certificate registries in `N`. -/
def UniNames (γ : Cluster) (N : Namespace) : Prop :=
  (∃ c0 g, ModeDec γ c0 g) ∧ γ.raft.reSnapLoc = (fun _ => none) ∧ γ.raft.reCertNs = N

/-- **A cluster of client decisions, with snapshots** (`InvNodeRule`'s `isCluster`). -/
def isClusterU (γ : Cluster) (N : Namespace) : IProp GF :=
  iprop(⌜UniNames γ N⌝ ∗ clusterInv γ N)

instance isClusterU_persistent (γ : Cluster) (N : Namespace) :
    Persistent (isClusterU (GF := GF) γ N) := by
  unfold isClusterU; infer_instance

/-! ## The configuration and the decisions -/

/-- **The membership after the first `k` committed entries is `m`** (`InvNodeRule`'s `confAt`): the
fold of some recorded decisions over a committed prefix. -/
def confAtU (γ : Cluster) (k : Nat) (m : Membership) : IProp GF :=
  iprop(∃ (l : List LogEntry) (M : DecMap), isCommittedLogLb γ l ∗ decLb γ.raft M ∗
    ⌜k ≤ l.length ∧ ∃ c0 g, ModeDec γ c0 g ∧ decFold M c0 (l.take k) = some m⌝)

instance confAtU_persistent (γ : Cluster) (k : Nat) (m : Membership) :
    Persistent (confAtU (GF := GF) γ k m) := by
  unfold confAtU; infer_instance

instance confAtU_timeless (γ : Cluster) (k : Nat) (m : Membership) :
    Timeless (confAtU (GF := GF) γ k m) := by
  unfold confAtU; infer_instance

/-- The decision map's element at `k`. -/
def decElem (γ : Cluster) (k : Nat) (v : Option ConfChangeIM) : IProp GF :=
  iprop(∃ g : GName, ⌜γ.raft.reDec = some g⌝ ∗ k ↪[g]□ v)

instance decElem_persistent (γ : Cluster) (k : Nat) (v : Option ConfChangeIM) :
    Persistent (decElem (GF := GF) γ k v) := by
  unfold decElem; infer_instance

instance decElem_timeless (γ : Cluster) (k : Nat) (v : Option ConfChangeIM) :
    Timeless (decElem (GF := GF) γ k v) := by
  unfold decElem; infer_instance

/-- An element is a lower bound of the map. -/
theorem decElem_decLb (γ : Cluster) (k : Nat) (v : Option ConfChangeIM) :
    decElem (GF := GF) γ k v ⊢ decLb γ.raft (GMap.singleton k v) := by
  unfold decElem decLb
  iintro ⟨%g, %Hg, #He⟩
  isplitr
  · ipureintro; intro h; rw [Hg] at h; cases h
  imodintro
  iintro %g' %Hg' %k' %v' %Hl
  rw [Hg] at Hg'
  cases Hg'
  have Hl' : (GMap.singleton k v : DecMap) !! k' = some v' := Hl
  simp only [GMap.singleton, GMap.lookup_insert_eq_iff, GMap.lookup_empty] at Hl'
  split at Hl'
  · rename_i hk; subst hk; cases Hl'; iexact He
  · cases Hl'

theorem decElem_agree (γ : Cluster) (k : Nat) (v1 v2 : Option ConfChangeIM) :
    decElem (GF := GF) γ k v1 ∗ decElem γ k v2 ⊢ ⌜v1 = v2⌝ := by
  unfold decElem
  iintro ⟨⟨%g1, %H1, #E1⟩, ⟨%g2, %H2, #E2⟩⟩
  rw [H1] at H2
  cases H2
  iapply ghostMapElem_agree $$ E1 E2

/-- **The conf entry at position `k` of the committed log was decided `d`** (`InvNodeRule`'s
`confDecided`): the decision map's element there, at a committed conf entry, its step defined at the
membership before it. -/
def confDecidedU (γ : Cluster) (k : Nat) (d : ConfDecision) : IProp GF :=
  iprop(∃ (l : List LogEntry) (e : LogEntry) (m m' : Membership),
    isCommittedLogLb γ l ∗ decElem γ k d.toOpt ∗ confAtU γ k m ∗
    ⌜l[k]? = some e ∧ e.isConfChange ∧ d.step m = some m'⌝)

instance confDecidedU_persistent (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Persistent (confDecidedU (GF := GF) γ k d) := by
  unfold confDecidedU; infer_instance

instance confDecidedU_timeless (γ : Cluster) (k : Nat) (d : ConfDecision) :
    Timeless (confDecidedU (GF := GF) γ k d) := by
  unfold confDecidedU; infer_instance

/-- **The decisions recorded so far** (`InvNodeRule`'s `ownConfDecisions`, exclusive): the decision
map's authority at `D`, and each binding decided. -/
def ownConfDecisionsU (γ : Cluster) (D : GMap Nat ConfDecision) : IProp GF :=
  iprop(∃ (c0 : Membership) (g : GName), ⌜ModeDec γ c0 g⌝ ∗
    ghostMapAuth g 1 (D.fmap ConfDecision.toOpt) ∗
    □ (∀ (k : Nat) (d : ConfDecision), ⌜D !! k = some d⌝ -∗ confDecidedU γ k d))

instance ownConfDecisionsU_timeless (γ : Cluster) (D : GMap Nat ConfDecision) :
    Timeless (ownConfDecisionsU (GF := GF) γ D) := by
  unfold ownConfDecisionsU; infer_instance

/-! ## The snapshots made -/

/-- **The snapshots the client made** (`InvNodeRule`'s `ownSnapsMade`, exclusive): the registry's
authority at the records `S`, each at the membership after its prefix. -/
def ownSnapsMadeU (γ : Cluster) (S : List SnapRec) : IProp GF :=
  iprop(∃ (g : GName) (K : List (w64 × List w8)),
    ⌜γ.raft.reSnapReg = some g ∧ List.Forall₂ SnapRec.Matches S K⌝ ∗ monoListAuthOwn g 1 K ∗
    □ [∗list] s ∈ S, confAtU γ s.index s.conf)

instance ownSnapsMadeU_timeless (γ : Cluster) (S : List SnapRec) :
    Timeless (ownSnapsMadeU (GF := GF) γ S) := by
  unfold ownSnapsMadeU; infer_instance

/-- **The snapshot `s` was made** (`InvNodeRule`'s `snapMade`; persistent). -/
def snapMadeU (γ : Cluster) (s : SnapRec) : IProp GF :=
  iprop(∃ (g : GName) (K : List (w64 × List w8)) (key : w64 × List w8),
    ⌜γ.raft.reSnapReg = some g ∧ key ∈ K ∧ s.Matches key⌝ ∗ monoListLbOwn g K ∗
    confAtU γ s.index s.conf)

instance snapMadeU_persistent (γ : Cluster) (s : SnapRec) :
    Persistent (snapMadeU (GF := GF) γ s) := by
  unfold snapMadeU; infer_instance

/-- **A founder's boot token** (`InvNodeRule`'s `nodeFounder`): node `id` of a cluster of the voters
`vs` (its initial membership theirs), raft's ghost state at the initial state, the empty log
committed, the term budget, and the node's table, empty. What its `RestartNode` takes. -/
def nodeFounderU (γ : Cluster) (N : Namespace) (vs : List w64) (id : w64) : IProp GF :=
  iprop(isClusterU γ N ∗
    ⌜γ.raft.reCfg = GMap.listToSet vs ∧ (∃ g, ModeDec γ (Membership.simple (GMap.listToSet vs)) g) ∧
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

/-- Two folds over lower bounds of one map, of comparable committed logs, agree. -/
theorem fold_agree {γ : Cluster} {c1 c2 : Membership} {g1 g2 : GName} {M1 M2 : DecMap}
    {l1 l2 : List LogEntry} {k : Nat} {m1 m2 : Membership}
    (hm1 : ModeDec γ c1 g1) (hm2 : ModeDec γ c2 g2) (Hc : DecCompat M1 M2)
    (Hl : l1 <+: l2 ∨ l2 <+: l1) (hk1 : k ≤ l1.length) (hk2 : k ≤ l2.length)
    (hf1 : decFold M1 c1 (l1.take k) = some m1) (hf2 : decFold M2 c2 (l2.take k) = some m2) :
    m1 = m2 := by
  obtain ⟨rfl, -⟩ := hm1.uniq hm2
  rw [take_eq_of_cmp l1 l2 k Hl hk1 hk2] at hf1
  have e1 := decFold_mono (DecCompat.sub_left M1 M2) _ _ _ hf1
  have e2 := decFold_mono (DecCompat.sub_right Hc) _ _ _ hf2
  rw [e1] at e2
  exact Option.some.inj e2

theorem confAt_agree_impl (γ : Cluster) (k : Nat) (m1 m2 : Membership) :
    confAtU (GF := GF) γ k m1 ∗ confAtU γ k m2 ⊢ ⌜m1 = m2⌝ := by
  unfold confAtU
  iintro ⟨⟨%l1, %M1, #H1, #D1, %P1⟩, ⟨%l2, %M2, #H2, #D2, %P2⟩⟩
  icases isCommittedLogLb_agree_impl γ l1 l2 $$ [H1 H2] with %Hl
  · iframe H1 H2
  icases decLb_compat γ.raft M1 M2 $$ [D1 D2] with %Hc
  · iframe D1 D2
  ipureintro
  obtain ⟨hk1, c1, g1, hm1, hf1⟩ := P1
  obtain ⟨hk2, c2, g2, hm2, hf2⟩ := P2
  exact fold_agree hm1 hm2 Hc Hl hk1 hk2 hf1 hf2

theorem confAt_valid_impl (γ : Cluster) (k : Nat) (m : Membership) :
    confAtU (GF := GF) γ k m ⊢ ⌜m.Valid⌝ := by
  unfold confAtU
  iintro ⟨%l, %M, -, -, %P⟩
  ipureintro
  obtain ⟨-, c0, g, hm, hf⟩ := P
  exact decFold_valid M c0 m _ hm.valid hf

theorem confAt_noConf_impl (γ : Cluster) (l : List LogEntry) (a b : Nat) (m : Membership) :
    NoConfChangeIn l a b → a ≤ b → b ≤ l.length →
    isCommittedLogLb (GF := GF) γ l ∗ confAtU γ a m ⊢ confAtU γ b m := by
  intro hn hab hb
  unfold confAtU
  iintro ⟨#Hl, %l1, %M, #H1, #HM, %P1⟩
  icases isCommittedLogLb_agree_impl γ l l1 $$ [Hl H1] with %Hc
  · iframe Hl H1
  iexists l, M
  iframe Hl HM
  ipureintro
  obtain ⟨hk1, c0, g, hm, hf⟩ := P1
  refine ⟨hb, c0, g, hm, ?_⟩
  rw [decFold_take_noConf M c0 l a b hn hab hb, take_eq_of_cmp l l1 a Hc (by omega) hk1]
  exact hf

/-- Past a decided entry, with the decisions of a `confAtU` at it: the decision's result. -/
theorem confAt_succ (γ : Cluster) (k : Nat) (m m' : Membership) (d : ConfDecision)
    (l : List LogEntry) (e : LogEntry) (he : l[k]? = some e) (hc : e.isConfChange)
    (hs : d.step m = some m') :
    isCommittedLogLb (GF := GF) γ l ∗ decElem γ k d.toOpt ∗ confAtU γ k m ⊢ confAtU γ (k + 1) m' := by
  iintro ⟨#Hl, #He, #Ha⟩
  ihave #HS := decElem_decLb γ k d.toOpt $$ He
  unfold confAtU
  icases Ha with ⟨%l1, %M1, #H1, #HM1, %P1⟩
  icases isCommittedLogLb_agree_impl γ l l1 $$ [Hl H1] with %Hcm
  · iframe Hl H1
  icases decLb_compat γ.raft M1 (GMap.singleton k d.toOpt) $$ [HM1 HS] with %Hcp
  · iframe HM1 HS
  ihave #HU := decLb_union γ.raft M1 (GMap.singleton k d.toOpt) $$ [HM1 HS]
  · iframe HM1 HS
  iexists l, M1 ∪ GMap.singleton k d.toOpt
  iframe Hl HU
  ipureintro
  obtain ⟨hk1, c0, g, hm, hf⟩ := P1
  have hkl : k < l.length := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨hkl, c0, g, hm, ?_⟩
  rw [take_succ_of_getElem? l k e he, decFold_snoc]
  rw [← take_eq_of_cmp l l1 k Hcm (by omega) hk1] at hf
  rw [decFold_mono (DecCompat.sub_left M1 _) _ _ _ hf, Option.bind_some]
  have hlk : (l.take k).length = k := by rw [List.length_take]; omega
  rw [hlk]
  have hL : (M1 ∪ GMap.singleton k d.toOpt).lookup k = some d.toOpt := by
    apply DecCompat.sub_right Hcp
    show (GMap.singleton k d.toOpt : DecMap) !! k = some d.toOpt
    simp [GMap.singleton, GMap.lookup_insert_eq_iff]
  rw [decStep_decided _ k m e d hc hL]
  exact hs

theorem confAt_decided_impl (γ : Cluster) (k : Nat) (m : Membership) (d : ConfDecision) :
    confAtU (GF := GF) γ k m ∗ confDecidedU γ k d ⊢
      ∃ m', ⌜d.step m = some m'⌝ ∗ confAtU γ (k + 1) m' := by
  iintro ⟨#Ha, #Hd⟩
  unfold confDecidedU
  icases Hd with ⟨%l, %e, %m0, %m', #Hl, #He, #Ha0, %P⟩
  icases confAt_agree_impl γ k m m0 $$ [Ha Ha0] with %Hm
  · iframe Ha Ha0
  subst Hm
  obtain ⟨he, hc, hs⟩ := P
  iexists m'
  isplitr; · ipureintro; exact hs
  iapply confAt_succ γ k m m' d l e he hc hs
  iframe Hl He Ha

theorem confDecided_agree_impl (γ : Cluster) (k : Nat) (d1 d2 : ConfDecision) :
    confDecidedU (GF := GF) γ k d1 ∗ confDecidedU γ k d2 ⊢ ⌜d1 = d2⌝ := by
  unfold confDecidedU
  iintro ⟨⟨%l1, %e1, %m1, %m1', -, #E1, -⟩, ⟨%l2, %e2, %m2, %m2', -, #E2, -⟩⟩
  icases decElem_agree γ k d1.toOpt d2.toOpt $$ [E1 E2] with %H
  · iframe E1 E2
  ipureintro; exact ConfDecision.toOpt_inj H

theorem ownConfDecisions_excl_impl (γ : Cluster) (D1 D2 : GMap Nat ConfDecision) :
    ownConfDecisionsU (GF := GF) γ D1 ∗ ownConfDecisionsU γ D2 ⊢ False := by
  unfold ownConfDecisionsU
  iintro ⟨⟨%c1, %g1, %H1, A1, -⟩, ⟨%c2, %g2, %H2, A2, -⟩⟩
  obtain ⟨-, rfl⟩ := H1.uniq H2
  ihave %Hv := ghostMapAuth_valid_2 _ _ _ _ _ $$ A1 A2
  exact absurd Hv.1 (Qp_one_add_not_le _)

theorem ownConfDecisions_lookup_impl (γ : Cluster) (D : GMap Nat ConfDecision) (k : Nat)
    (d : ConfDecision) :
    ownConfDecisionsU (GF := GF) γ D ∗ confDecidedU γ k d ⊢ ⌜D !! k = some d⌝ := by
  unfold ownConfDecisionsU confDecidedU
  iintro ⟨⟨%c0, %g, %Hm, A, -⟩, ⟨%l, %e, %m, %m', -, #E, -⟩⟩
  iunfold decElem at E
  icases E with ⟨%g', %Hg', #E⟩
  have Hg : g' = g := by
    obtain ⟨⟨-, -, -, -, -, -, hg⟩, -⟩ := Hm
    rw [hg] at Hg'; exact (Option.some.inj Hg').symm
  subst Hg
  icases ghost_map_lookup $$ A E with %Hl
  ipureintro
  have Hl' : (D !! k).map ConfDecision.toOpt = some d.toOpt := Hl
  cases hd : D !! k with
  | none => rw [hd] at Hl'; cases Hl'
  | some d' =>
    rw [hd] at Hl'
    exact congrArg some (ConfDecision.toOpt_inj (Option.some.inj Hl'))

theorem ownConfDecisions_witness_impl (γ : Cluster) (D : GMap Nat ConfDecision) (k : Nat)
    (d : ConfDecision) :
    D !! k = some d →
    ownConfDecisionsU (GF := GF) γ D ⊢ ownConfDecisionsU γ D ∗ confDecidedU γ k d := by
  intro hk
  unfold ownConfDecisionsU
  iintro ⟨%c0, %g, %Hm, A, #Hall⟩
  ihave #Hd := Hall $$ %k %d %hk
  iframe Hd
  iexists c0, g
  iframe A Hall
  ipureintro; exact Hm

theorem fmap_insert_toOpt (D : GMap Nat ConfDecision) (k : Nat) (d : ConfDecision) :
    (D.insert k d).fmap ConfDecision.toOpt = (D.fmap ConfDecision.toOpt).insert k d.toOpt := by
  apply GMap.ext; intro k'
  show ((D.insert k d) !! k').map ConfDecision.toOpt = (GMap.insert k d.toOpt (D.fmap ConfDecision.toOpt)) !! k'
  rw [GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff]
  split
  · rfl
  · rfl

/-- **Deciding an undecided committed conf entry** (`InvNodeRule`'s `confDecide`). -/
theorem confDecide_impl (γ : Cluster) (N : Namespace) (D : GMap Nat ConfDecision)
    (l : List LogEntry) (k : Nat) (e : LogEntry) (m m' : Membership) (d : ConfDecision) :
    D !! k = none → l[k]? = some e → e.isConfChange → d.step m = some m' →
    isClusterU (GF := GF) γ N ∗ isCommittedLogLb γ l ∗ confAtU γ k m ∗ ownConfDecisionsU γ D ==∗
      ownConfDecisionsU γ (D.insert k d) ∗ confDecidedU γ k d ∗ confAtU γ (k + 1) m' := by
  intro hD he hc hs
  iintro ⟨-, #Hl, #Ha, Hown⟩
  unfold ownConfDecisionsU
  icases Hown with ⟨%c0, %g, %Hm, A, #Hall⟩
  have Hg : γ.raft.reDec = some g := by obtain ⟨⟨-, -, -, -, -, -, hg⟩, -⟩ := Hm; exact hg
  have hD' : (D.fmap ConfDecision.toOpt).lookup k = none := by
    show (D !! k).map ConfDecision.toOpt = none
    rw [hD]; rfl
  imod ghost_map_insert_persist k d.toOpt hD' $$ A with ⟨A, #E⟩
  ihave #He : decElem γ k d.toOpt $$ []
  · unfold decElem; iexists g; iframe E; ipureintro; exact Hg
  ihave #Hd : confDecidedU γ k d $$ []
  · unfold confDecidedU
    iexists l, e, m, m'
    iframe Hl He Ha
    ipureintro; exact ⟨he, hc, hs⟩
  ihave #Ha' := confAt_succ γ k m m' d l e he hc hs $$ [Hl He Ha]
  · iframe Hl He Ha
  imodintro
  iframe Hd Ha'
  iexists c0, g
  isplitr; · ipureintro; exact Hm
  rw [fmap_insert_toOpt]
  iframe A
  imodintro
  iintro %k' %d' %hk'
  by_cases hkk : k = k'
  · subst hkk
    have : d' = d := by
      have h2 : (D.insert k d) !! k = some d' := hk'
      rw [GMap.lookup_insert] at h2; exact (Option.some.inj h2).symm
    subst this; iexact Hd
  · have h2 : (D.insert k d) !! k' = some d' := hk'
    rw [GMap.lookup_insert_ne _ _ hkk] at h2
    iapply Hall $$ %k' %d' %h2

/-- **Skipped entries' decisions** (what `node.ApplyConfChange`'s and `node.Advance`'s `skippedIn`
gives raft): a lower bound of the map recording a skip at every conf entry of `l` at the positions
`xs`. -/
theorem skipped_decLb (γ : Cluster) (l : List LogEntry) (xs : List Nat) :
    ([∗list] j ∈ xs, iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ →
        confDecidedU (GF := GF) γ j .skip)) ⊢
      ∃ M : DecMap, decLb γ.raft M ∗
        ⌜∀ j e, j ∈ xs → l[j]? = some e → e.isConfChange → M.lookup j = some none⌝ := by
  induction xs with
  | nil =>
    iintro -
    iexists ∅
    isplitr; · iapply decLb_empty
    ipureintro; intro j e hj; cases hj
  | cons j xs ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#Hj, #Hr⟩
    icases ih $$ Hr with ⟨%M2, #HM2, %P2⟩
    by_cases hc : ∃ e, l[j]? = some e ∧ e.isConfChange
    · obtain ⟨e, he, hce⟩ := hc
      ihave #Hd := Hj $$ %e %(And.intro he hce)
      unfold confDecidedU
      icases Hd with ⟨%l', %e', %m, %m', -, #He, -⟩
      ihave #HS := decElem_decLb γ j _ $$ He
      ihave #HU := decLb_union γ.raft _ M2 $$ [HS HM2]
      · iframe HS HM2
      iexists GMap.singleton j ConfDecision.skip.toOpt ∪ M2
      iframe HU
      ipureintro
      intro j' e'' hj' he'' hc''
      show ((GMap.singleton j ConfDecision.skip.toOpt : DecMap) !! j').or (M2 !! j') = some none
      by_cases hjj : j = j'
      · subst hjj; simp [GMap.singleton, GMap.lookup_insert_eq_iff, ConfDecision.toOpt]
      · have hm : j' ∈ xs := by
          rcases List.mem_cons.1 hj' with h | h
          · exact absurd h.symm hjj
          · exact h
        have := P2 j' e'' hm he'' hc''
        simp only [GMap.singleton, GMap.lookup_insert_eq_iff, hjj, ↓reduceIte, GMap.lookup_empty,
          Option.none_or]
        exact this
    · iexists M2
      iframe HM2
      ipureintro
      intro j' e'' hj' he'' hc''
      rcases List.mem_cons.1 hj' with h | h
      · subst h; exact absurd ⟨e'', he'', hc''⟩ hc
      · exact P2 j' e'' h he'' hc''

/-- `skipped_decLb` over a range of positions. -/
theorem skipped_range_decLb (γ : Cluster) (l : List LogEntry) (a b : Nat) :
    ([∗list] j ∈ List.range' a (b - a), iprop(∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ →
        confDecidedU (GF := GF) γ j .skip)) ⊢
      ∃ M : DecMap, decLb γ.raft M ∗
        ⌜∀ j e, a ≤ j → j < b → l[j]? = some e → e.isConfChange → M.lookup j = some none⌝ := by
  iintro H
  icases skipped_decLb γ l _ $$ H with ⟨%M, #HM, %P⟩
  iexists M
  iframe HM
  ipureintro
  intro j e h1 h2 he hc
  exact P j e (List.mem_range'_1.2 ⟨h1, by omega⟩) he hc

/-! ## Snapshots -/

theorem snapMade_elem_impl (γ : Cluster) (S : List SnapRec) (s : SnapRec) :
    ownSnapsMadeU (GF := GF) γ S ∗ snapMadeU γ s ⊢ ⌜s ∈ S⌝ := by
  unfold ownSnapsMadeU snapMadeU
  iintro ⟨⟨%g, %K, %Hk, Ha, #HS⟩, ⟨%g', %K', %key, %Hk', #Hlb, #Hs⟩⟩
  have Hg : g' = g := by rw [Hk.1] at Hk'; exact (Option.some.inj Hk'.1).symm
  subst Hg
  icases mono_list_auth_lb_valid g' 1 K K' $$ Ha Hlb with %Hv
  have HkK : key ∈ K := Hv.2.subset Hk'.2.1
  obtain ⟨s', Hs'S, Hm'⟩ := forall₂_mem_right Hk.2 HkK
  ihave #Hs' := (BigSepL.bigSepL_mem (Φ := fun x => confAtU (GF := GF) γ x.index x.conf) Hs'S) $$ HS
  have Hi : s.index = s'.index := by rw [← Hk'.2.2.1, Hm'.1]
  have Hd : s.data = s'.data := by rw [← Hk'.2.2.2, Hm'.2]
  ihave #Hs'' : confAtU γ s.index s'.conf $$ []
  · rw [Hi]; iexact Hs'
  icases confAt_agree_impl γ s.index s.conf s'.conf $$ [Hs Hs''] with %Hc
  · iframe Hs Hs''
  ipureintro
  have : s = s' := by cases s; cases s'; simp only at Hi Hd Hc; subst Hi Hd Hc; rfl
  rw [this]; exact Hs'S

/-- **Certifying a snapshot of a committed prefix** (`InvNodeRule`'s `snapshotCert_make`): its
configuration the membership after the prefix (`confAtU`), over the decisions that fold it. -/
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
  iintro #Hc #Hlb #Ha Hown
  ihave #Ha' := Ha
  iunfold confAtU at Ha'
  icases Ha' with ⟨%l1, %M, #H1, #HM, %P1⟩
  icases isCommittedLogLb_agree_impl γ l l1 $$ [Hlb H1] with %Hcm
  · iframe Hlb H1
  obtain ⟨hk1, c0, g, hm, hf1⟩ := P1
  have Hfold : decFold M c0 l = some m := by
    rw [← List.take_length (l := l), take_eq_of_cmp l l1 l.length Hcm (Nat.le_refl _) hk1]
    exact hf1
  unfold isClusterU
  icases Hc with ⟨-, #Hci⟩
  have hm' := hm
  obtain ⟨⟨h0, hv0, hd, Hns, Hsok, Hreg, -⟩, -⟩ := hm'
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  have HlogN : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
    intro p hp
    unfold raftLogN raftN at hp; rw [HNs] at hp
    exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%L, %HL, #HLc⟩
  imod api_committed_lb γ N E HE L $$ Hci HLc with ⟨-, %Hidx⟩
  have Hal : cs.VotersOutgoing' = [] → m.autoLeave = false := fun h => Hok.2.2.2.2.2.2.1 h
  have Hcfg := cfgM_of_confStateIs cs m t i d Hcs Hal
  have HD : (DynCfg.ofFold noDec (stOf c0) h0).fold M L =
      some (SnapTrip.cfgM ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩) := by
    rw [hm.fold _ hd M L, HL, Hfold, Hcfg]; rfl
  have HLlen : L.length = uint.nat i := by rw [← Hlen, ← HL, strip_length]
  have HLlast : L.getLast?.map EntryM.Term' = some t := by
    rw [← Hlast, ← HL]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  imod raftSnapCert_make_dyn γ.raft E L ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ _ M HlogN hd HLlen
    HLlast Hok HD $$ Hcinv HLc HM with #Hcert
  unfold ownSnapsMadeU
  icases Hown with ⟨%gr, %K, %HK, Hau, #HS⟩
  imod monoListAuthOwn_update_app [(i, d)] $$ Hau with ⟨Hau, #Hlb'⟩
  imodintro
  isplitl [Hau]
  · iexists gr, K ++ [(i, d)]
    iframe Hau
    isplitr
    · ipureintro
      refine ⟨HK.1, forall₂_snoc HK.2 ?_⟩
      exact ⟨by rw [Hlen], rfl⟩
    · imodintro
      iapply BigSepL.bigSepL_snoc.2
      iframe HS Ha
  unfold snapshotCert
  iframe Hcert
  isplitr; · ipureintro; exact Hns
  iexists L, M
  rw [HL]
  iframe Hlb HM
  isplitr
  · ipureintro
    refine ⟨Hidx, HLlen, Hsok _ _, fun _ => ⟨HLlast, Hok, fun D' HD' => ?_⟩⟩
    rw [hd] at HD'; cases HD'; exact HD
  unfold snapRegOk
  rw [HK.1]
  iexists K ++ [(i, d)]
  iframe Hlb'
  ipureintro; exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **What a certificate says** (`InvNodeRule`'s `snapshotCert_made`). -/
theorem snapshotCert_made_impl (γ : Cluster) (N : Namespace) (k : SnapTrip) :
    isClusterU (GF := GF) γ N ∗ snapshotCert γ N k ⊢
      ∃ (l : List LogEntry) (m : Membership), isCommittedLogLb γ l ∗ confAtU γ l.length m ∗
        snapMadeU γ ⟨l.length, m, k.dat⟩ ∗
        ⌜l.length = uint.nat k.sid.index' ∧ Option.map LogEntry.term l.getLast? = some k.sid.term' ∧
          k.cl.Is m ∧ k.al = m.autoLeave⌝ := by
  unfold isClusterU
  iintro ⟨⟨%Hu, -⟩, #Hk⟩
  obtain ⟨⟨c0, g, hm⟩, -⟩ := Hu
  have hm' := hm
  obtain ⟨⟨h0, hv0, hd, -, -, Hreg, -⟩, -⟩ := hm'
  unfold snapshotCert
  icases Hk with ⟨-, -, %L, %M, #Hlb, #HM, %HL, #Hr⟩
  obtain ⟨-, Hlen, -, Hat⟩ := HL
  obtain ⟨Hlast, Hok, Hfd⟩ := Hat Hreg
  have HD := Hfd _ hd
  rw [hm.fold _ hd M L] at HD
  cases Hf : decFold M c0 (strip L) with
  | none => rw [Hf] at HD; cases HD
  | some m =>
    rw [Hf] at HD
    have Hm : k.cfgM = cfgOf m := (Option.some.inj HD).symm
    obtain ⟨Hcl, Hal⟩ := lists_of_cfgM k m Hok Hm
    have Hsl : (strip L).length = uint.nat k.sid.index' := by rw [strip_length, Hlen]
    ihave #Ha : confAtU γ (strip L).length m $$ []
    · unfold confAtU
      iexists strip L, M
      iframe Hlb HM
      ipureintro
      exact ⟨Nat.le_refl _, c0, g, hm, by rw [List.take_length]; exact Hf⟩
    cases Hg : γ.raft.reSnapReg with
    | none => exact absurd Hg Hreg
    | some gr =>
      unfold snapRegOk
      rw [Hg]
      icases Hr with ⟨%K, #HK, %Hin⟩
      iexists strip L, m
      iframe Hlb Ha
      isplitr
      · unfold snapMadeU
        iexists gr, K, (k.sid.index', k.dat)
        iframe HK Ha
        ipureintro; exact ⟨Hg, Hin, Hsl.symm, rfl⟩
      ipureintro
      refine ⟨Hsl, ?_, Hcl, Hal⟩
      rw [← Hlast]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl

end names

end ApiImpl
end EtcdGrove
end Perennial
