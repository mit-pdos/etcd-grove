/-
# Raft's node API: allocating a cluster of client decisions, with snapshots (2026-10-28)

`cluster_alloc_dec_impl`, behind `InvNodeRule.lean`'s `cluster_alloc` (the conf-change decision switch;
until then `cluster_alloc_rule_impl`, of a rule fixed at allocation): raft's ghost state for the
voters `vs` with an empty log (`ownRaftGhost_alloc_core_reg`), in the dynamic mode of the base decoder
that decides nothing (`noDec`) from the voters' membership, over the client's decision map (an empty
ghost map, allocated first: `RaftNames.reDec`), outside the no-snapshot mode (`ns = false`, which the
empty log allows), with every snapshot's data admitted and a registry of the snapshots made (an empty
`mono_list`, allocated first); leader transfer on (the no-transfer mode needs a bootstrap log).
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiDec
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A new cluster of client decisions**, of the voters `vs`, with snapshots (`InvNodeRule`'s
`cluster_alloc`). -/
theorem cluster_alloc_dec_impl (N : Namespace) (vs : List w64) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ownCommittedOps (GF := GF) γ [] ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isClusterU γ N ∗ ownConfDecisionsU γ ∅ ∗
        confAtU γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMadeU γ [] ∗
        leaderTransferOn γ N ∗
        [∗list] id ∈ vs, nodeFounderU γ N vs id := by
  intro Hrb Hne Hnd Hnz Hlen
  imod budget_alloc (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  imod alloc_maps (GF := GF) (K := w64) (V := CfgNames) (GMap.listToSet vs) with ⟨%tab, -, Htab⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (w64 × List w8)) with ⟨%g, Hreg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option ConfChangeIM) with ⟨%gd, Hdm⟩
  have HB : BootLog ([] : List w64) [] [] := ⟨rfl, by simp, fun k e h => by simp at h⟩
  have Hcne := listToSet_ne_empty vs Hne
  have Hnz' : W64 0 ∉ GMap.listToSet vs := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have Hsz : GMap.size (GMap.listToSet vs) < 2 ^ 62 := by
    rw [GMap.size_list_to_set vs Hnd]; omega
  have Hv := memValid_simple (GMap.listToSet vs) Hcne Hsz
  let c0 := Membership.simple (GMap.listToSet vs)
  let md : RNMode := .dyn noDec (stOf c0) Hv.1 Hv.2
  let dc := DynCfg.ofFold noDec (stOf c0) Hv.1
  have H0 : LogEntry.toEntries ([] : List LogEntry) 0 = [] := rfl
  have Hcl0 := api_alloc_client (GF := GF) N E (GMap.listToSet vs) [] [] [] bud md tab
    (some (DynCfg.all dc)) HB
  rw [H0] at Hcl0
  ihave Hcl := Hcl0
  imod ownRaftGhost_alloc_core_reg E (GMap.listToSet vs) (GMap.listToSet vs) (some (DynCfg.all dc))
    (fun _ _ => True) [] (W64 0) (allocOut N [] bud md tab) none (fun _ h => by cases h)
    false (fun h => by cases h) false (fun h => by cases h) (fun _ _ => True) (fun _ => none)
    (N .@ "raft") N (some g) (some gd) Hcne Hnz' BootWf_nil (fun h => absurd rfl h)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, -, -, Hns, Hnx, Hsok, Hsl, HNs, Hcert, Hrg, Hrd⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb, Hγm, Hγt⟩ := Hγr
  subst Hγr
  have Hrn : DecNames γ c0 gd := by
    refine ⟨Hv.1, Hv, ?_, Hns, ?_, ?_, Hrd⟩
    · unfold RaftNames.dyn; rw [Hdyn]; simp [DynCfg.all_self, dc]
    · intro L d; rw [Hsok]; trivial
    · rw [Hrg]; simp
  have Hmr : ModeDec γ c0 gd := ⟨Hrn, Hv.1, Hv.2, Hγm⟩
  ihave #Hdc : isClusterU (GF := GF) γ N $$ []
  · unfold isClusterU clusterInv
    iframe Hcinv Hinv HspT
    ipureintro
    exact ⟨⟨⟨c0, gd, Hmr⟩, Hsl, Hcert⟩, HNs⟩
  imodintro
  iexists γ
  iframe Hops Hctx Hdc
  isplitl [Hcr]
  · unfold readCredits; iexact Hcr
  isplitl [Hdm]
  · unfold ownConfDecisionsU
    iexists c0, gd
    isplitr; · ipureintro; exact Hmr
    rw [show (∅ : GMap Nat ConfDecision).fmap ConfDecision.toOpt = ∅ from GMap.ext fun _ => rfl]
    iframe Hdm
    imodintro
    iintro %k %d %h
    exact absurd h (by simp)
  isplitr
  · unfold confAtU
    iexists [], ∅
    isplitr; · iapply isCommittedLogLb_nil_impl
    isplitr; · iapply decLb_empty
    ipureintro
    exact ⟨Nat.le_refl _, c0, gd, Hmr, rfl⟩
  isplitl [Hreg]
  · unfold ownSnapsMadeU
    iexists g, []
    iframe Hreg
    isplitr; · ipureintro; exact ⟨Hrg, .nil⟩
    imodintro
    iapply (BigSepL.bigSepL_nil).2; iempintro
  isplitr
  · unfold leaderTransferOn; ipureintro; exact Hnx
  simp only [Option.isSome_some]
  ihave Hn := bigSepM_listToSet _ vs Hnd $$ Hnodes
  ihave Ht := bigSepM_listToSet (fun x => iprop(∃ γx, ⌜tab !! x = some γx⌝ ∗
    ghostMapAuth (GF := GF) γx 1 (∅ : GMap w64 CfgNames))) vs Hnd $$ Htab
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [Hn Ht]
  · iframe Hn Ht
  iapply BigSepL.bigSepL_impl $$ H
  imodintro
  iintro %k %id %_ ⟨Hg, ⟨%g', %Hg0, Ha⟩⟩
  unfold nodeFounderU
  rw [initPState_eq, Hγb, Hγt]
  iframe Hdc Hg Hc0 Hbinv Htlb
  isplitr
  · ipureintro; exact ⟨Hcfg, ⟨gd, Hmr⟩, Hne, Hnd, Hnz, Hlen⟩
  iexists g'
  iframe Ha
  ipureintro; exact Hg0

end alloc

end ApiImpl
end EtcdGrove
end Perennial
