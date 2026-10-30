/-
# Raft's node API: a new cluster with a bootstrap log (2026-10-30, stage R5)

The definitions behind `InvNodeRule.lean`'s sealed `nodeBoot`, and `cluster_alloc_boot_impl`, the
bootstrap-log form of `cluster_alloc` (its empty-log form is `cluster_alloc_dec_impl`,
`InvApiDecAlloc.lean`): the cluster of client decisions of `InvApiDec.lean` (raft's dynamic mode of the
base decoder that decides nothing, from the voters' membership, with snapshots and a registry of them),
whose committed log starts with the bootstrap log `boot` -- one `AddNode` per voter, as raft's
`Bootstrap` writes it (`BootLog`) -- and whose nodes start at the bootstrap state (`bootPState`: term
`1`, the log `boot` committed), for `StartNode` (`nodeBootU`: the node's part, the boot log's bytes,
`bootMarshal`, and the term budget at the bootstrap term). The boot conf entries are not decided here:
the client decides them as any committed conf entry (`confDecide`).

No join authority: every node is allocated at the bootstrap state, and raft's protocol keeps the
bootstrap log a prefix of every node's log (`Protocol/Ghost.lean`), which a newcomer's `RestartNode` on
an empty storage would not be.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiJoin
public import Proof.go_etcd_io.raft.v3.InvBoot
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A founder's start token in a cluster with a bootstrap log** (`InvNodeRule`'s `nodeBoot`): node
`id`, one of the voters `ps`, of the cluster; raft's names those of the voters' membership and of the
bootstrap log of the peers `ps` (`BootLogOk`), whose bytes are `Marshal`'s at the peers' changes with
the contexts `ctxs` (`bootMarshal`), committed; the term budget at the bootstrap term; the node's raft
ghost state at the bootstrap state and its (empty) table of views. -/
def nodeBootU (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8)) (id : w64) :
    IProp GF :=
  iprop(isClusterU γ N ∗
    ⌜id ∈ ps ∧ ps.Nodup ∧ W64 0 ∉ ps ∧ (ps.length : Int) < 2 ^ 62 ∧
      γ.raft.reCfg = GMap.listToSet ps ∧
      (∃ g, ModeDec γ (Membership.simple (GMap.listToSet ps)) g) ∧ BootLogOk ps γ.raft.reBoot⌝ ∗
    bootMarshal ps ctxs γ.raft.reBoot ∗ isCommitted γ.raft γ.raft.reBoot ∗
    inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 1) ∗
    ownRaftGhost γ.raft id (bootPState γ.raft.reBoot) true ∗
    (∃ g : GName, ⌜γ.nodeTab !! id = some g⌝ ∗ ghostMapAuth g 1 (∅ : GMap w64 CfgNames)))

/-- No entry of a bootstrap log is an empty `ConfChangeV2` (each is a `ConfChange`, type `1`). -/
theorem bootLogOk_noEmptyV2 {ps : List w64} {L : List EntryM} (H : BootLogOk ps L) :
    ∀ x ∈ L, ¬ IsEmptyV2 x := by
  rintro x hx ⟨_, h⟩
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
  obtain ⟨-, -, Hty, -⟩ := H.2.2 k x hk
  rw [Hty] at h
  have := congrArg (fun x : w32 => uint.Z x) h
  revert this; decide

/-- **A new cluster of client decisions with a bootstrap log**, of the voters `vs` (`InvNodeRule`'s
`cluster_alloc` at a non-empty `boot`). -/
theorem cluster_alloc_boot_impl (N : Namespace) (vs : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (dup : Bool) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → (vs.length : Int) < 2 ^ 62 →
    BootLog vs ctxs boot →
    ⊢ bootMarshal (GF := GF) vs ctxs (LogEntry.toEntries boot 0) ={E}=∗ ∃ γ,
        ⌜γ.raft.dup = dup ∧ γ.raft.reBoot.length = boot.length⌝ ∗ ownCommittedOps (GF := GF) γ boot ∗
        ownReadCtxs γ ∅ ∗ isClusterU γ N ∗ ownConfDecisionsU γ ∅ ∗
        confAtU γ 0 (Membership.simple (GMap.listToSet vs)) ∗ ownSnapsMadeU γ [] ∗
        isCommittedLogLb γ boot ∗
        [∗list] id ∈ vs, nodeBootU γ N vs ctxs id := by
  intro Hrb Hne Hnd Hnz Hlen HB
  iintro #Hm
  imod budget_alloc_boot (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  imod alloc_maps (GF := GF) (K := w64) (V := CfgNames) (GMap.listToSet vs) with ⟨%tab, -, Htab⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (w64 × List w8)) with ⟨%g, Hreg, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option ConfChangeIM) with ⟨%gd, Hdm⟩
  have Hok := BootLog_ok HB
  have Hwf := Hok.wf Hnd
  have Hcne := listToSet_ne_empty vs Hne
  have Hnz' : W64 0 ∉ GMap.listToSet vs := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have Hsz : GMap.size (GMap.listToSet vs) < 2 ^ 62 := by
    rw [GMap.size_list_to_set vs Hnd]; omega
  have Hv := memValid_simple (GMap.listToSet vs) Hcne Hsz
  let c0 := Membership.simple (GMap.listToSet vs)
  let md : RNMode := .dyn noDec (stOf c0) Hv.1 Hv.2
  let dc := DynCfg.ofFold noDec (stOf c0) Hv.1
  ihave Hcl := api_alloc_client (GF := GF) N E (GMap.listToSet vs) vs ctxs boot bud md tab
    (some (DynCfg.all dc)) HB
  imod ownRaftGhost_alloc_core_reg E (GMap.listToSet vs) (GMap.listToSet vs) (some (DynCfg.all dc))
    (fun _ _ => True) (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot bud md tab) none
    (fun _ h => by cases h)
    false (fun h => by cases h) false (fun h => by cases h) (fun _ _ => True) (fun _ => none)
    (N .@ "raft") N (some g) (some gd) dup Hcne Hnz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, HbootL, -, Hns, Hnx, Hsok, Hsl, HNs, Hcert, Hrg, Hrd, Hdup⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx, #Hblb⟩
  obtain ⟨Hγr, Hγb, Hγm, Hγt⟩ := Hγr
  subst Hγr
  have Hrn : DecNames γ c0 gd := by
    refine ⟨Hv.1, Hv, ?_, Hns, ?_, ?_, Hrd⟩
    · unfold RaftNames.dyn; rw [Hdyn]; simp [DynCfg.all_self, dc]
    · intro L d; rw [Hsok]; trivial
    · rw [Hrg]; simp
  have Hr0 : W64 0 ∉ c0.ids ∧ ∀ k, k ∈ c0.learnersNext → k ∉ c0.voters := by
    refine ⟨fun h' => ?_, fun _ h' => absurd h' (GMap.not_elem_of_empty _)⟩
    simp only [c0, Membership.ids, Membership.simple, GMap.elem_of_union] at h'
    rcases h' with ((h' | h') | h') | h'
    · exact Hnz' h'
    all_goals exact GMap.not_elem_of_empty _ h'
  have Hmr : ModeDec γ c0 gd := ⟨Hrn, ⟨Hv.1, Hv.2, Hγm⟩, Hr0⟩
  -- (raft-final, U7) the read credits' exchange, from every read credit and no receipt
  imod receipt_zero (GF := GF) with H0
  imod inv_alloc (N .@ "rdpool") E
    iprop(∃ (k c : Nat), ⧗ k ∗ rdCred γ.raft c ∗ ⌜2 ^ 64 - 2 ≤ k + c⌝) $$ [Hcr H0] with #Hpool
  · inext
    iexists 0, 2 ^ 64 - 2
    iframe H0 Hcr
    ipureintro; omega
  ihave #Hdc : isClusterU (GF := GF) γ N $$ []
  · unfold isClusterU rdPool
    isplitr
    · ipureintro
      refine ⟨⟨c0, gd, Hmr⟩, Hsl, Hcert, ?_⟩
      rw [HbootL]; exact bootLogOk_noEmptyV2 Hok
    isplitr
    · unfold clusterInv
      iframe Hcinv Hinv HspT
      ipureintro; exact HNs
    iframe Hpool
    ipureintro; exact Hrb
  imodintro
  iexists γ
  iframe Hops Hctx Hdc Hblb
  isplitr
  · ipureintro; exact ⟨Hdup, by rw [HbootL, toEntries_length]⟩
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
  -- each voter's part: raft's ghost state at the bootstrap state, its table of views
  isimp only [Option.isSome_some] at Hnodes
  ihave Hboth : ([∗map] x ↦ _u ∈ toMap (GMap.listToSet vs),
      iprop(ownRaftGhost (GF := GF) γ.raft x (initPStateAt (W64 1) (LogEntry.toEntries boot 0)) true ∗
        ∃ gx : GName, ⌜tab !! x = some gx⌝ ∗ ghostMapAuth (GF := GF) gx 1 (∅ : GMap w64 CfgNames))) $$ [Hnodes Htab]
  · rw [BigSepM.bigSepM_sep_eq]; iframe Hnodes Htab
  iapply bigSepM_listToSet _ vs Hnd
  iapply BigSepM.bigSepM_impl $$ Hboth
  imodintro
  iintro %id %u %Hid ⟨Hg, Ht⟩
  have Hin : id ∈ vs := by
    rw [← GMap.elem_of_list_to_set]
    exact (GMap.elem_of_gset _ _).2 (by cases u; exact Hid)
  unfold nodeBootU
  rw [HbootL, Hγb, Hγt, bootPState_eq]
  iframe Hdc Hg Hc0 Hm Hbinv Htlb Ht
  ipureintro
  exact ⟨Hin, Hnd, Hnz, Hlen, Hcfg, ⟨gd, Hmr⟩, Hok⟩

end boot

end ApiImpl
end EtcdGrove
end Perennial
