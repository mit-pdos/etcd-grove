/-
Lean-first (no Rocq counterpart). U8 v2, step 4 (2026-10-29): a valid snapshot's certificates.

The API's `snapshotValid γ sv` (`InvNodeRule.lean`: a committed prefix of the snapshot's index and
last term, its `ConfState` reporting the membership after it, and the snapshot made) gives raft's
certificates of the snapshot, `raftSnapCertD γ.raft (snapTrip sv sv.Metadata'.ConfState'.lists)`.
This module proves it at the protocol level, over the pieces the API's definitions unfold to:

- `snapListsOk_of_cfg` (pure): lists that are permutations of a configuration's sets
  (`confStateIs`) are well formed (`SnapListsOk`) and denote it (`SnapTrip.cfgM`), given what a
  membership of the cluster has (`CfgOk`; no id `0` and no staged learner an incoming voter, the
  API's `Membership.Restorable`), the snapshot's index below `2^61`, and -- a premise nothing in
  the membership gives -- the lists' total length within `2^62` (`SnapListsOk`'s bound: a valid
  membership's tracked ids are below `2^62`, but its incoming and outgoing voters may overlap);
- `raftSnapCertD_of_reg`: a snapshot at a committed prefix, its lists well formed and denoting the
  mode's fold of the prefix over recorded decisions, its key in the registry of the snapshots made:
  both certificates (`raftSnapCert_make_dyn`, and the data's: every data admitted);
- `raftSnapCertD_snapTrip`: the two together, for a `SnapshotM`.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.SnapCertDyn
public import Proof.go_etcd_io.raft.v3.Protocol.CfgOverlap
public import Proof.go_etcd_io.raft.v3.CCApplyC
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A list that is a permutation of a set's elements has the set's members. -/
theorem snapValid_mem_of_perm {l : List w64} {X : GSet w64} (h : l ≡ₚ GMap.elements X) (x : w64) :
    x ∈ l ↔ x ∈ X := by
  rw [h.mem_iff, GMap.elem_of_elements]

theorem snapValid_listToSet_of_perm {l : List w64} {X : GSet w64} (h : l ≡ₚ GMap.elements X) :
    GMap.listToSet l = X :=
  GMap.set_eq fun x => by rw [GMap.elem_of_list_to_set]; exact snapValid_mem_of_perm h x

theorem snapValid_nil_of_perm {l : List w64} {X : GSet w64} (h : l ≡ₚ GMap.elements X)
    (hX : ∀ x, x ∉ X) : l = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun x hx => hX x ((snapValid_mem_of_perm h x).1 hx)

/-- **The lists of a membership's `ConfState` are well formed and denote it**: lists that are
permutations of the configuration `c`'s sets (as `confStateIs` says of a membership `m`, with
`c = cfgOf m`), its `AutoLeave` `c`'s, at a configuration a node can be in (`CfgOk`, the first half
of `Membership.Valid`), with no id `0` and no staged learner an incoming voter (the API's
`Membership.Restorable`), the lists within `SnapListsOk`'s length bound and the index below
`2^61`. -/
theorem snapListsOk_of_cfg (sid : entryID) (cl : CSLists) (al : Bool) (dat : List w8) (c : CfgM)
    (hv : cl.voters ≡ₚ GMap.elements c.incoming) (ho : cl.outgoing ≡ₚ GMap.elements c.outgoing)
    (hl : cl.learners ≡ₚ GMap.elements c.learners)
    (hn : cl.learnersNext ≡ₚ GMap.elements c.learnersNext) (hal : al = c.autoLeave)
    (hok : CfgOk (cfgStateC c))
    (h0 : ∀ x, x ∈ c.incoming ∨ x ∈ c.outgoing ∨ x ∈ c.learners ∨ x ∈ c.learnersNext →
      x ≠ W64 0)
    (hni : ∀ x, x ∈ c.learnersNext → x ∉ c.incoming)
    (hsz : (cl.voters.length + cl.learners.length + cl.outgoing.length +
      cl.learnersNext.length : Int) ≤ 2 ^ 62)
    (hi : uint.Z sid.index' < 2 ^ 61) :
    SnapListsOk ⟨sid, cl, al, dat⟩ ∧ SnapTrip.cfgM ⟨sid, cl, al, dat⟩ = c := by
  obtain ⟨⟨-, hlnI, hlrI, hjI⟩, hne, -⟩ := hok
  -- `cfgStateC c`'s configuration is `c`
  change (∀ id, id ∈ c.learnersNext → id ∈ c.outgoing ∧ _) at hlnI
  change (∀ id, id ∈ c.learners → id ∉ c.outgoing ∧ id ∉ c.incoming ∧ _) at hlrI
  change (c.outgoing = ∅ → c.learnersNext = ∅ ∧ c.autoLeave = false) at hjI
  change c.incoming ≠ ∅ at hne
  have hvm := snapValid_mem_of_perm hv
  have hom := snapValid_mem_of_perm ho
  have hlm := snapValid_mem_of_perm hl
  have hnm := snapValid_mem_of_perm hn
  have hout : cl.outgoing = [] → c.outgoing = ∅ := by
    intro h
    refine GMap.set_eq (X := c.outgoing) (Y := ∅) fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hom, h] at hx; cases hx
    · exact absurd hx (GMap.not_elem_of_empty x)
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, hv.nodup_iff.2 (GMap.NoDup_elements _),
    hl.nodup_iff.2 (GMap.NoDup_elements _), ho.nodup_iff.2 (GMap.NoDup_elements _),
    hn.nodup_iff.2 (GMap.NoDup_elements _), hsz, ?_, hi⟩, ?_⟩
  · intro h
    simp only at h
    apply hne
    refine GMap.set_eq (X := c.incoming) (Y := ∅) fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hvm, h] at hx; cases hx
    · exact absurd hx (GMap.not_elem_of_empty x)
  · intro x hx
    apply h0 x
    rcases hx with h | h | h | h
    · exact .inr (.inl ((hom x).1 h))
    · exact .inl ((hvm x).1 h)
    · exact .inr (.inr (.inl ((hlm x).1 h)))
    · exact .inr (.inr (.inr ((hnm x).1 h)))
  · intro x hx
    obtain ⟨h1, h2, -⟩ := hlrI x ((hlm x).1 hx)
    exact ⟨fun h => h2 ((hvm x).1 h), fun h => h1 ((hom x).1 h)⟩
  · intro x hx
    have hx' := (hnm x).1 hx
    have hxo := (hlnI x hx').1
    refine ⟨(hom x).2 hxo, fun h => hni x hx' ((hvm x).1 h), fun h => ?_⟩
    exact (hlrI x ((hlm x).1 h)).1 hxo
  · intro h
    have := (hjI (hout h)).1
    exact snapValid_nil_of_perm hn fun x hx => by rw [this] at hx; exact GMap.not_elem_of_empty x hx
  · intro h
    show al = false
    rw [hal]; exact (hjI (hout h)).2
  · unfold SnapTrip.cfgM csCfgM
    simp only
    rw [snapValid_listToSet_of_perm hv, snapValid_listToSet_of_perm ho,
      snapValid_listToSet_of_perm hl, snapValid_listToSet_of_perm hn]
    cases c with
    | mk ci co cl' cn ca =>
      simp only [CfgM.mk.injEq, _root_.true_and]
      by_cases h : cl.outgoing = []
      · rw [ite_eq_left h]; exact ((hjI (hout h)).2).symm
      · rw [ite_eq_right h]; exact hal

end pure

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **Both certificates of a snapshot made at a committed prefix**: the snapshot `k` at the id of the
committed prefix `L` (its length and last term), its lists well formed (`SnapListsOk`) and denoting
the mode's fold of `L` over decisions recorded (`decLb`), and its key -- its index and data -- in the
registry of the snapshots made (`γ.reSnapReg = some g`), in a cluster that admits every data: its
configuration's certificate (`raftSnapCert`) and its data's (`snapDataOk`). -/
theorem raftSnapCertD_of_reg (γ : RaftNames) (E : CoPset) (L : List EntryM) (k : SnapTrip)
    (D : DynCfg) (M : DecMap) (g : GName) (K : List (w64 × List w8)) (key : w64 × List w8) :
    ↑(raftLogN γ) ⊆ E → γ.dyn = some D → γ.reSnapReg = some g → (∀ L d, γ.reSnapOkRaw L d) →
    L.length = uint.nat k.sid.index' → L.getLast?.map EntryM.Term' = some k.sid.term' →
    SnapListsOk k → D.fold M L = some k.cfgM →
    key ∈ K → uint.nat key.1 = uint.nat k.sid.index' → key.2 = k.dat →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L -∗ decLb γ M -∗ monoListLbOwn g K ={E}=∗
      raftSnapCertD γ k := by
  intro HE HD Hreg Hsok HlenN Hlast Hok Hfold HkK Hk1 Hk2
  iintro #Hinv #HL #HM #HK
  imod raftSnapCert_make_dyn γ E L k D M HE HD HlenN Hlast Hok Hfold $$ Hinv HL HM with #Hc
  imodintro
  unfold raftSnapCertD
  iframe Hc
  unfold snapDataOk
  iexists L
  iframe HL
  isplitr; · ipureintro; exact ⟨HlenN, Hsok _ _⟩
  unfold snapRegOk
  rw [Hreg]
  iexists K
  iframe HK
  ipureintro
  have Hk1' : key.1 = k.sid.index' := by word
  have : (k.sid.index', k.dat) = key := by rw [← Hk1', ← Hk2]
  rw [this]; exact HkK

/-- **A valid snapshot's certificates**, for a `SnapshotM` `sv` (what the API's `snapshotValid`
unfolds to, with `c = cfgOf m` for the membership `m` its `ConfState` reports): `sv` at the committed
prefix `L` (its index and last term, below `2^61`), its `ConfState`'s lists permutations of `c`'s
sets with its `AutoLeave`, `c` a configuration of the cluster (`CfgOk`, no id `0`, no staged learner
an incoming voter) and the mode's fold of `L` over decisions recorded, the lists' total length
within `2^62`, and its key in the registry of the snapshots made. -/
theorem raftSnapCertD_snapTrip (γ : RaftNames) (E : CoPset) (L : List EntryM) (sv : SnapshotM)
    (c : CfgM) (D : DynCfg) (M : DecMap) (g : GName) (K : List (w64 × List w8))
    (key : w64 × List w8) :
    ↑(raftLogN γ) ⊆ E → γ.dyn = some D → γ.reSnapReg = some g → (∀ L d, γ.reSnapOkRaw L d) →
    L.length = uint.nat sv.Metadata'.Index' → L.length < 2 ^ 61 →
    L.getLast?.map EntryM.Term' = some sv.Metadata'.Term' →
    sv.Metadata'.ConfState'.Voters' ≡ₚ GMap.elements c.incoming →
    sv.Metadata'.ConfState'.VotersOutgoing' ≡ₚ GMap.elements c.outgoing →
    sv.Metadata'.ConfState'.Learners' ≡ₚ GMap.elements c.learners →
    sv.Metadata'.ConfState'.LearnersNext' ≡ₚ GMap.elements c.learnersNext →
    sv.Metadata'.ConfState'.AutoLeave' = c.autoLeave →
    CfgOk (cfgStateC c) →
    (∀ x, x ∈ c.incoming ∨ x ∈ c.outgoing ∨ x ∈ c.learners ∨ x ∈ c.learnersNext → x ≠ W64 0) →
    (∀ x, x ∈ c.learnersNext → x ∉ c.incoming) →
    (sv.Metadata'.ConfState'.Voters'.length + sv.Metadata'.ConfState'.Learners'.length +
      sv.Metadata'.ConfState'.VotersOutgoing'.length +
      sv.Metadata'.ConfState'.LearnersNext'.length : Int) ≤ 2 ^ 62 →
    D.fold M L = some c →
    key ∈ K → uint.nat key.1 = L.length → key.2 = sv.Data' →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L -∗ decLb γ M -∗ monoListLbOwn g K ={E}=∗
      raftSnapCertD γ (snapTrip sv sv.Metadata'.ConfState'.lists) := by
  intro HE HD Hreg Hsok HlenN Hlt Hlast hv ho hl hn hal hok h0 hni hsz Hfold HkK Hk1 Hk2
  have hi : uint.Z sv.Metadata'.Index' < 2 ^ 61 := by
    have : (uint.nat sv.Metadata'.Index' : Int) = uint.Z sv.Metadata'.Index' := by word
    omega
  obtain ⟨Hok, Hcfg⟩ := snapListsOk_of_cfg (snapId sv) sv.Metadata'.ConfState'.lists
    sv.Metadata'.ConfState'.AutoLeave' sv.Data' c hv ho hl hn hal hok h0 hni hsz hi
  exact raftSnapCertD_of_reg γ E L (snapTrip sv sv.Metadata'.ConfState'.lists) D M g K key HE HD
    Hreg Hsok HlenN Hlast Hok (Hfold.trans (congrArg some Hcfg.symm)) HkK (Hk1.trans HlenN) Hk2

end ghost

end EtcdGrove
end Perennial
