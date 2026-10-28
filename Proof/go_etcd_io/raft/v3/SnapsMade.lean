/-
# The snapshots the application made, and their certificates (2026-10-28, stage U2)

Stage U2 of `notes/raft-unified-plan.md`: candidate 12's snapshot laws
(`notes/spec-first-study/raft-node-unified-candidate.md`, section 2) over the dynamic clause of
raft's certificate, internal until the node API's public specs switch (U9).

- **The registry** (TaDa style): `ownSnapsMade γ r c0 S`, the client's, the list `S` of the
  snapshots it made (`SnapRec`: index, configuration, data), in the cluster's registry
  (`RaftNames.reSnapReg`, a `mono_list` of `(index, data)` keys); `snapMade γ r c0 s`, persistent,
  that `s` is one of them (`snapMade_elem`). Each record's configuration is the rule's fold of the
  committed prefix of its length (`snapConfAt`).
- **`snapshotCert_make`**: a committed prefix `l` (its length `i`, last term `t`) whose fold is `m`,
  a `ConfState` `cs` reporting `m`, give a certificate of the snapshot `(t, i, cs, d)` and record
  `⟨|l|, m, d⟩` in the registry. Its dynamic clause from `raftSnapCert_make_dyn`.
- **`snapshotCert_made`**: a certificate of a cluster with the registry names a committed prefix of
  its length and last term, its configuration the fold of it, recorded as made.

The rule `r` and the initial membership `c0` are explicit here; U9 makes them the cluster's
(`γ.rule`, `γ.c0`). `RuleNames γ r c0` is what the laws need of the cluster's names: its dynamic
mode the rule's (`ConfRule.toDec`), snapshots on, every data admitted, a registry. Departures from
the candidate's text (`notes/decisions.md`, "Stages U2, U3"): `snapshotCert_make` is a fancy update
inside `N` (it opens raft's commit invariant for the dynamic clause) and takes the snapshot's
`SnapListsOk` (the lists' well-formedness raft's `restore` needs: ids nonzero, at most `2^62`
entries in all, which `Membership.Valid` does not imply).
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRuleDec
public import Proof.go_etcd_io.raft.v3.Protocol.SnapCertDyn
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 ApiImpl

section pure
variable [GooseExts]

/-- A snapshot's record matches a registry key: its index and data. -/
def _root_.Perennial.EtcdGrove.SnapRec.Matches (s : SnapRec) (key : w64 × List w8) : Prop :=
  uint.nat key.1 = s.index ∧ key.2 = s.data

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {S : List α} {K : List β} {b : β}
    (h : List.Forall₂ R S K) (hb : b ∈ K) : ∃ a ∈ S, R a b := by
  induction h with
  | nil => cases hb
  | @cons a b' S K hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hab⟩
    · obtain ⟨a', ha', h'⟩ := ih hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} {S : List α} {K : List β} {a : α} {b : β}
    (h : List.Forall₂ R S K) (hab : R a b) : List.Forall₂ R (S ++ [a]) (K ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab .nil
  | cons h _ ih => exact List.Forall₂.cons h ih

theorem perm_elements_nodup (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem listToSet_of_perm (l : List w64) (X : GSet w64) (h : l ≡ₚ GMap.elements X) :
    GMap.listToSet l = X := by
  rw [← GMap.listToSet_elements X]
  apply GMap.set_eq
  intro x
  rw [GMap.elem_of_list_to_set, GMap.elem_of_list_to_set]
  exact h.mem_iff

/-- The configuration of a `ConfState` reporting a membership is the membership's. -/
theorem cfgM_of_confStateIs (cs : ConfStateM) (m : Membership) (t i : w64) (d : List w8)
    (hc : confStateIs cs m)
    (hal : cs.VotersOutgoing' = [] → m.autoLeave = false) :
    SnapTrip.cfgM ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ = cfgOf m := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hc
  unfold SnapTrip.cfgM csCfgM cfgOf
  simp only [ConfStateM.lists]
  rw [listToSet_of_perm _ _ h1, listToSet_of_perm _ _ h2, listToSet_of_perm _ _ h3,
    listToSet_of_perm _ _ h4]
  congr 1
  by_cases h : cs.VotersOutgoing' = []
  · simp [h, hal h]
  · simp [h]

/-- The lists of a snapshot whose configuration is a membership's report it, given no repeats. -/
theorem lists_of_cfgM (k : SnapTrip) (m : Membership) (hk : SnapListsOk k)
    (hm : k.cfgM = cfgOf m) : k.cl.Is m ∧ k.al = m.autoLeave := by
  obtain ⟨-, hv, hl, ho, hn, -, hal, -⟩ := hk
  unfold SnapTrip.cfgM csCfgM cfgOf at hm
  simp only [CfgM.mk.injEq] at hm
  obtain ⟨e1, e2, e3, e4, e5⟩ := hm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← e1]; exact perm_elements_nodup _ hv
  · rw [← e2]; exact perm_elements_nodup _ ho
  · rw [← e3]; exact perm_elements_nodup _ hl
  · rw [← e4]; exact perm_elements_nodup _ hn
  · by_cases h : k.cl.outgoing = []
    · simp [h] at e5; rw [hal h, ← e5]
    · simp [h] at e5; exact e5

end pure

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What the snapshot laws need of the cluster's names: its dynamic mode the rule `r`'s from `c0`
(`ConfRule.toDec`), snapshots on, every data admitted, and a registry of the snapshots made. -/
def RuleNames (γ : Cluster) (r : ConfRule) (c0 : Membership) : Prop :=
  ∃ (h0 : CfgOk (stOf c0)), c0.Valid ∧
    γ.raft.dyn = some (DynCfg.ofFold (r.toDec c0) (stOf c0) h0) ∧
    γ.raft.reNoSnap = false ∧ (∀ L d, γ.raft.reSnapOkRaw L d) ∧ γ.raft.reSnapReg ≠ none

/-- The record `s`'s configuration is the rule's fold of the committed prefix of its length. -/
def snapConfAt (γ : Cluster) (r : ConfRule) (c0 : Membership) (s : SnapRec) : IProp GF :=
  iprop(∃ l : List LogEntry, isCommittedLogLb γ l ∗
    ⌜l.length = s.index ∧ Membership.fold r c0 l = some s.conf⌝)

instance snapConfAt_persistent (γ : Cluster) (r : ConfRule) (c0 : Membership) (s : SnapRec) :
    Persistent (snapConfAt (GF := GF) γ r c0 s) := by
  unfold snapConfAt; infer_instance

/-- **The snapshots the client made** (exclusive): the registry's authority, at the records `S`. -/
def ownSnapsMade (γ : Cluster) (r : ConfRule) (c0 : Membership) (S : List SnapRec) : IProp GF :=
  iprop(∃ (g : GName) (K : List (w64 × List w8)),
    ⌜γ.raft.reSnapReg = some g ∧ List.Forall₂ SnapRec.Matches S K⌝ ∗ monoListAuthOwn g 1 K ∗
    □ [∗list] s ∈ S, snapConfAt γ r c0 s)

instance snapConfAt_timeless (γ : Cluster) (r : ConfRule) (c0 : Membership) (s : SnapRec) :
    Timeless (snapConfAt (GF := GF) γ r c0 s) := by
  unfold snapConfAt; infer_instance

instance ownSnapsMade_timeless (γ : Cluster) (r : ConfRule) (c0 : Membership) (S : List SnapRec) :
    Timeless (ownSnapsMade (GF := GF) γ r c0 S) := by
  unfold ownSnapsMade; infer_instance

/-- **The snapshot `s` was made** (persistent). -/
def snapMade (γ : Cluster) (r : ConfRule) (c0 : Membership) (s : SnapRec) : IProp GF :=
  iprop(∃ (g : GName) (K : List (w64 × List w8)) (key : w64 × List w8),
    ⌜γ.raft.reSnapReg = some g ∧ key ∈ K ∧ s.Matches key⌝ ∗ monoListLbOwn g K ∗
    snapConfAt γ r c0 s)

instance snapMade_persistent (γ : Cluster) (r : ConfRule) (c0 : Membership) (s : SnapRec) :
    Persistent (snapMade (GF := GF) γ r c0 s) := by
  unfold snapMade; infer_instance

/-- Two records of committed prefixes of one length have one configuration. -/
theorem snapConfAt_agree (γ : Cluster) (r : ConfRule) (c0 : Membership) (s s' : SnapRec)
    (hi : s.index = s'.index) :
    snapConfAt (GF := GF) γ r c0 s ∗ snapConfAt γ r c0 s' ⊢ ⌜s.conf = s'.conf⌝ := by
  unfold snapConfAt
  iintro ⟨⟨%l, #Hl, %Hp⟩, ⟨%l', #Hl', %Hp'⟩⟩
  icases isCommittedLogLb_agree_impl γ l l' $$ [Hl Hl'] with %Hpre
  · iframe Hl Hl'
  have Hlen : l.length = l'.length := by rw [Hp.1, Hp'.1, hi]
  have Heq : l = l' := by
    rcases Hpre with h | h
    · exact h.eq_of_length Hlen
    · exact (h.eq_of_length Hlen.symm).symm
  subst Heq
  ipureintro
  rw [Hp.2] at Hp'
  exact Option.some.inj Hp'.2

/-- **A snapshot made is one of the client's** (the candidate's `snapMade_elem`). -/
theorem snapMade_elem (γ : Cluster) (r : ConfRule) (c0 : Membership) (S : List SnapRec)
    (s : SnapRec) :
    ownSnapsMade (GF := GF) γ r c0 S ∗ snapMade γ r c0 s ⊢ ⌜s ∈ S⌝ := by
  unfold ownSnapsMade snapMade
  iintro ⟨⟨%g, %K, %Hk, Ha, #HS⟩, ⟨%g', %K', %key, %Hk', #Hlb, #Hs⟩⟩
  have Hg : g' = g := by rw [Hk.1] at Hk'; exact (Option.some.inj Hk'.1).symm
  subst Hg
  icases mono_list_auth_lb_valid g' 1 K K' $$ Ha Hlb with %Hv
  have HkK : key ∈ K := Hv.2.subset Hk'.2.1
  obtain ⟨s', Hs'S, Hm'⟩ := forall₂_mem_right Hk.2 HkK
  ihave #Hs' := (BigSepL.bigSepL_mem (Φ := fun x => snapConfAt (GF := GF) γ r c0 x) Hs'S) $$ HS
  have Hi : s.index = s'.index := by rw [← Hk'.2.2.1, Hm'.1]
  have Hd : s.data = s'.data := by rw [← Hk'.2.2.2, Hm'.2]
  icases snapConfAt_agree γ r c0 s s' Hi $$ [Hs Hs'] with %Hc
  · iframe Hs Hs'
  ipureintro
  have : s = s' := by cases s; cases s'; simp only at Hi Hd Hc; subst Hi Hd Hc; rfl
  rw [this]; exact Hs'S

/-- The rule's mode folds a raft log as the rule folds it. -/
theorem RuleNames.fold {γ : Cluster} {r : ConfRule} {c0 : Membership} (h : RuleNames γ r c0)
    (D : DynCfg) (hD : γ.raft.dyn = some D) (L : List EntryM) :
    D.fold L = (Membership.fold r c0 (strip L)).map cfgOf := by
  obtain ⟨h0, hv, hd, -⟩ := h
  rw [hd] at hD
  cases hD
  show (cfgFold (r.toDec c0) (stOf c0) L).map (fun s => s.cfg) = _
  rw [cfgFold_toDec r c0 hv L, Option.map_map]
  rfl

/-- **Certifying a snapshot of a committed prefix** (the candidate's `snapshotCert_make`, stage U2;
a fancy update inside `N`, and with the lists' `SnapListsOk`: see the file header). -/
theorem snapshotCert_make (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (r : ConfRule) (c0 : Membership) (l : List LogEntry) (i t : w64) (d : List w8)
    (m : Membership) (cs : ConfStateM) (S : List SnapRec) :
    RuleNames γ r c0 →
    l.length = uint.nat i → Option.map LogEntry.term l.getLast? = some t →
    SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ →
    Membership.fold r c0 l = some m → confStateIs cs m →
    ⊢ clusterInv (GF := GF) γ N -∗ isCommittedLogLb γ l -∗ ownSnapsMade γ r c0 S ={E}=∗
      ownSnapsMade γ r c0 (S ++ [⟨l.length, m, d⟩]) ∗
      snapshotCert γ N ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ := by
  intro Hrn Hlen Hlast Hok Hfold Hcs
  have Hrn' := Hrn
  obtain ⟨h0, hv0, hd, Hns, Hsok, Hreg⟩ := Hrn'
  iintro #Hci #Hlb Hown
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  have HlogN : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
    intro p hp
    unfold raftLogN raftN at hp; rw [HNs] at hp
    exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%L, %HL, #HLc⟩
  imod api_committed_lb γ N E HE L $$ Hci HLc with ⟨-, %Hidx⟩
  -- the membership is valid: a fold from a valid one
  have Hal : cs.VotersOutgoing' = [] → m.autoLeave = false := fun h => Hok.2.2.2.2.2.2.1 h
  have Hcfg := cfgM_of_confStateIs cs m t i d Hcs Hal
  have HD : (DynCfg.ofFold (r.toDec c0) (stOf c0) h0).fold L =
      some (SnapTrip.cfgM ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩) := by
    rw [Hrn.fold _ hd L, HL, Hfold, Hcfg]; rfl
  have HLlen : L.length = uint.nat i := by rw [← Hlen, ← HL, strip_length]
  have HLlast : L.getLast?.map EntryM.Term' = some t := by
    rw [← Hlast, ← HL]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  imod raftSnapCert_make_dyn γ.raft E L ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ _ HlogN hd HLlen
    HLlast Hok HD $$ Hcinv HLc with #Hc
  -- the registry
  unfold ownSnapsMade
  icases Hown with ⟨%g, %K, %HK, Ha, #HS⟩
  imod monoListAuthOwn_update_app [(i, d)] $$ Ha with ⟨Ha, #Hlb'⟩
  ihave #Hnew : snapConfAt (GF := GF) γ r c0 ⟨l.length, m, d⟩ $$ []
  · unfold snapConfAt; iexists l; iframe Hlb; ipureintro; exact ⟨rfl, Hfold⟩
  imodintro
  isplitl [Ha]
  · iexists g, K ++ [(i, d)]
    iframe Ha
    isplitr
    · ipureintro
      refine ⟨HK.1, forall₂_snoc HK.2 ?_⟩
      exact ⟨by rw [Hlen], rfl⟩
    · imodintro
      iapply BigSepL.bigSepL_snoc.2
      iframe HS Hnew
  unfold snapshotCert
  iframe Hc
  isplitr; · ipureintro; exact Hns
  iexists L
  rw [HL]
  iframe Hlb
  isplitr
  · ipureintro
    refine ⟨Hidx, HLlen, Hsok _ _, fun _ => ⟨HLlast, Hok, fun D' HD' => ?_⟩⟩
    rw [hd] at HD'; cases HD'; exact HD
  unfold snapRegOk
  rw [HK.1]
  iexists K ++ [(i, d)]
  iframe Hlb'
  ipureintro; exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **What a certificate says** (the candidate's `snapshotCert_made`, stage U2): in a cluster of the
rule `r`, a certified snapshot is at a committed prefix of its length and last term, its
configuration the rule's fold of it, and made by the client. -/
theorem snapshotCert_made (γ : Cluster) (N : Namespace) (r : ConfRule) (c0 : Membership)
    (k : SnapTrip) :
    RuleNames γ r c0 →
    snapshotCert (GF := GF) γ N k ⊢
      ∃ (l : List LogEntry) (m : Membership), isCommittedLogLb γ l ∗
        snapMade γ r c0 ⟨l.length, m, k.dat⟩ ∗
        ⌜l.length = uint.nat k.sid.index' ∧ Option.map LogEntry.term l.getLast? = some k.sid.term' ∧
          Membership.fold r c0 l = some m ∧ k.cl.Is m ∧ k.al = m.autoLeave⌝ := by
  intro Hrn
  have Hrn' := Hrn
  obtain ⟨h0, hv0, hd, -, -, Hreg⟩ := Hrn'
  unfold snapshotCert
  iintro ⟨-, -, %L, #Hlb, %HL, #Hr⟩
  obtain ⟨-, Hlen, -, Hat⟩ := HL
  obtain ⟨Hlast, Hok, Hfd⟩ := Hat Hreg
  have HD := Hfd _ hd
  rw [Hrn.fold _ hd L] at HD
  cases Hf : Membership.fold r c0 (strip L) with
  | none => rw [Hf] at HD; cases HD
  | some m =>
    rw [Hf] at HD
    have Hm : k.cfgM = cfgOf m := (Option.some.inj HD).symm
    obtain ⟨Hcl, Hal⟩ := lists_of_cfgM k m Hok Hm
    cases Hg : γ.raft.reSnapReg with
    | none => exact absurd Hg Hreg
    | some g =>
      unfold snapRegOk
      rw [Hg]
      icases Hr with ⟨%K, #HK, %Hin⟩
      iexists strip L, m
      iframe Hlb
      have Hsl : (strip L).length = uint.nat k.sid.index' := by rw [strip_length, Hlen]
      isplitr
      · unfold snapMade
        iexists g, K, (k.sid.index', k.dat)
        iframe HK
        isplitr
        · ipureintro; exact ⟨Hg, Hin, Hsl.symm, rfl⟩
        unfold snapConfAt
        iexists strip L
        iframe Hlb
        ipureintro; exact ⟨rfl, Hf⟩
      ipureintro
      refine ⟨Hsl, ?_, Hf, Hcl, Hal⟩
      rw [← Hlast]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl

end reg

end ApiImpl
end EtcdGrove
end Perennial
