/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/DeployProof.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The deployment's proofs (`netcluster.go`): `RunServer`, `NewNetCluster`, `NetCluster.Propose`,
from the transport's specs (`Net.lean`) and the agents' (`Agents.lean`), taken as hypotheses.

Internal: `agentAddrs`, `acceptorIds`, `learnerIds`, the ids, `decision`, `runLearner`,
`announce`, and the paxos package's initialization.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Deploy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option linter.unusedSectionVars false

/-! ## Pure facts about the ids -/

theorem w64_le3 (i : w64) (h1 : 1 ≤ uint.nat i) (h : uint.nat i ≤ 3) :
    i = W64 1 ∨ i = W64 2 ∨ i = W64 3 := by
  have : uint.nat i = 1 ∨ uint.nat i = 2 ∨ uint.nat i = 3 := by omega
  rcases this with h | h | h
  · left; word
  · right; left; word
  · right; right; word

theorem w64_lt2 (j : w64) (h : uint.nat j < 2) : j = W64 0 ∨ j = W64 1 := by
  have : uint.nat j = 0 ∨ uint.nat j = 1 := by omega
  rcases this with h | h
  · left; word
  · right; word

theorem w64_lt4 (c : w64) (h : uint.nat c < 4) :
    c = W64 0 ∨ c = W64 1 ∨ c = W64 2 ∨ c = W64 3 := by
  have : uint.nat c = 0 ∨ uint.nat c = 1 ∨ uint.nat c = 2 ∨ uint.nat c = 3 := by omega
  rcases this with h | h | h | h
  · left; word
  · right; left; word
  · right; right; left; word
  · right; right; right; word

theorem box_ids (c : w64) (hc : uint.nat c < 4) :
    W64 3001 + c ∉ accIds ∧ W64 3001 + c ∉ propIds ∧ W64 3001 + c ∉ lrnIds ∧
      W64 3001 + c ∈ boxIds ∧ W64 3001 + c ∈ clientIds c := by
  rcases w64_lt4 c hc with rfl | rfl | rfl | rfl <;> decide

theorem prop_ids (c : w64) (hc : uint.nat c < 4) :
    W64 1001 + c ∈ propIds ∧ W64 1001 + c ∈ clientIds c := by
  rcases w64_lt4 c hc with rfl | rfl | rfl | rfl <;> decide

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions]
  [sync.Assumptions]

local notation "pkg" => pkg_id.github_com.xiang90.paxos

set_option goose.wp.extras true

/-! ## The ids -/

theorem wp_netProposerId (c : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! netProposerId)) (Val #c))
    {{ RET #(W64 1001 + c); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_netLearnerId (j : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! netLearnerId)) (Val #j))
    {{ RET #(W64 2001 + j); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_netBoxId (c : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! netBoxId)) (Val #c))
    {{ RET #(W64 3001 + c); True }} := by
  wp_start
  wp_auto
  wp_end

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] 
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

/-- What a message to client `c`'s box means. -/
theorem msgOK_box (Γ : Names) (c : w64) (hc : uint.nat c < 4) (m : message)
    (hto : m.to' = W64 3001 + c) :
    msgOK (GF := GF) Γ m ⊣⊢ ⌜m.typ' = W64 5⌝ ∗ chosenW Γ m.value' := by
  obtain ⟨h1, h2, h3, h4, -⟩ := box_ids c hc
  unfold msgOK
  rw [hto, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  exact .rfl

instance allProtos_persistent' (Γ : Names) : Persistent (allProtos (GF := GF) Γ) := by
  unfold allProtos; infer_instance


end ghost

/-! ## `acceptorIds`, `learnerIds` -/

theorem wp_acceptorIds :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! acceptorIds)) (Val #(W64 3)))
    {{ (sl : GoSlice), RET #sl; sl ↦* accIds }} := by
  wp_start
  wp_auto
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 3) (by word)) as %sl ⟨Hsl, Hcap, -⟩
  ihave HI : (∃ (i : w64) (ids : GoSlice), "i" ∷ i_ptr ↦ i ∗ "ids" ∷ ids_ptr ↦ ids ∗
      "Hsl" ∷ ids ↦* accIds.take (uint.nat i - 1) ∗ "Hcap" ∷ ownSliceCap w64 ids (DFrac.own 1) ∗
      "%Hi" ∷ ⌜1 ≤ uint.nat i ∧ uint.nat i ≤ 4⌝ : IProp GF) $$ [i ids Hsl Hcap]
  · iexists W64 1, sl
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Htmp, -⟩
    wp_auto
    wp_apply wp_slice_append (V := w64) $$ [$Hsl $Hcap $Htmp] as %ids' ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, ids'
    iframe
    have h3 : uint.nat i ≤ 3 := by word
    rcases w64_le3 i Hi.1 h3 with rfl | rfl | rfl
    all_goals (iframe; ipureintro; decide)
  have h4 : i = W64 4 := by word
  subst h4
  wp_end

theorem wp_learnerIds :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! learnerIds)) (Val #(W64 2)))
    {{ (sl : GoSlice), RET #sl; sl ↦* lrnIds }} := by
  wp_start
  wp_auto
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 2) (by word)) as %sl ⟨Hsl, Hcap, -⟩
  ihave HI : (∃ (j : w64) (ids : GoSlice), "j" ∷ j_ptr ↦ j ∗ "ids" ∷ ids_ptr ↦ ids ∗
      "Hsl" ∷ ids ↦* lrnIds.take (uint.nat j) ∗ "Hcap" ∷ ownSliceCap w64 ids (DFrac.own 1) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ 2⌝ : IProp GF) $$ [j ids Hsl Hcap]
  · iexists W64 0, sl
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · wp_apply wp_netLearnerId
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Htmp, -⟩
    wp_auto
    wp_apply wp_slice_append (V := w64) $$ [$Hsl $Hcap $Htmp] as %ids' ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, ids'
    iframe
    have h2 : uint.nat j < 2 := by word
    rcases w64_lt2 j h2 with rfl | rfl
    all_goals (iframe; ipureintro; decide)
  have h2 : j = W64 2 := by word
  subst h2
  wp_end

/-! ## `agentAddrs` -/

/-- The map after the acceptors' loop up to `n`. -/
def accM : Nat → GMap w64 GoString
  | 0 => ∅
  | n + 1 => <[W64 ((n + 1 : Nat) : Int) := addrs.getD n []]> (accM n)

/-- The map after the learners' loop up to `n`. -/
def lrnM : Nat → GMap w64 GoString
  | 0 => accM 3
  | n + 1 => <[W64 (2001 + (n : Nat)) := addrs.getD (3 + n) []]> (lrnM n)

/-- The map after the clients' loop up to `n`. -/
def cliM : Nat → GMap w64 GoString
  | 0 => lrnM 2
  | n + 1 => <[W64 (3001 + (n : Nat)) := addrs.getD (5 + n) []]>
      (<[W64 (1001 + (n : Nat)) := addrs.getD (5 + n) []]> (cliM n))

theorem accM_step (i : w64) (a : GoString) (h1 : 1 ≤ uint.nat i) (h3 : uint.nat i ≤ 3)
    (ha : addrs[uint.nat i - 1]? = some a) :
    <[i := a]> (accM (uint.nat i - 1)) = accM (uint.nat (i + W64 1) - 1) := by
  rcases w64_le3 i h1 h3 with rfl | rfl | rfl <;> simp [addrs] at ha <;> subst ha <;> rfl

theorem lrnM_step (j : w64) (h : uint.nat j < 2) :
    <[W64 2001 + j := addrs.getD (3 + uint.nat j) []]> (lrnM (uint.nat j)) =
      lrnM (uint.nat (j + W64 1)) := by
  rcases w64_lt2 j h with rfl | rfl <;> rfl

theorem cliM_step (c : w64) (h : uint.nat c < 4) :
    <[W64 3001 + c := addrs.getD (5 + uint.nat c) []]>
      (<[W64 1001 + c := addrs.getD (5 + uint.nat c) []]> (cliM (uint.nat c))) =
      cliM (uint.nat (c + W64 1)) := by
  rcases w64_lt4 c h with rfl | rfl | rfl | rfl <;> rfl

theorem cliM_agentMap : cliM 4 = agentMap := by
  refine GMap.ext fun k => ?_
  simp only [cliM, lrnM, accM, agentMap, GMap.lookup_insert_eq_iff, GMap.lookup_empty,
    Nat.reduceAdd]
  simp only [show W64 (3001 + ((0 : Nat) : Int)) = W64 3001 from rfl,
    show W64 (3001 + ((1 : Nat) : Int)) = W64 3002 from rfl,
    show W64 (3001 + ((2 : Nat) : Int)) = W64 3003 from rfl,
    show W64 (3001 + ((3 : Nat) : Int)) = W64 3004 from rfl,
    show W64 (1001 + ((0 : Nat) : Int)) = W64 1001 from rfl,
    show W64 (1001 + ((1 : Nat) : Int)) = W64 1002 from rfl,
    show W64 (1001 + ((2 : Nat) : Int)) = W64 1003 from rfl,
    show W64 (1001 + ((3 : Nat) : Int)) = W64 1004 from rfl,
    show W64 (2001 + ((0 : Nat) : Int)) = W64 2001 from rfl,
    show W64 (2001 + ((1 : Nat) : Int)) = W64 2002 from rfl,
    show W64 ((1 : Nat) : Int) = W64 1 from rfl,
    show W64 ((2 : Nat) : Int) = W64 2 from rfl,
    show W64 ((3 : Nat) : Int) = W64 3 from rfl]
  by_cases h : W64 1 = k ∨ W64 2 = k ∨ W64 3 = k ∨ W64 2001 = k ∨ W64 2002 = k ∨ W64 1001 = k ∨ W64 1002 = k ∨ W64 1003 = k ∨ W64 1004 = k ∨ W64 3001 = k ∨ W64 3002 = k ∨ W64 3003 = k ∨ W64 3004 = k
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  · simp only [not_or] at h
    simp only [h, if_false]

theorem wp_agentAddrs (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ sl ↦*□ addrs }}
      (App (App (App (App (Val (@! agentAddrs)) (Val #sl)) (Val #(W64 3))) (Val #(W64 2)))
        (Val #(W64 4)))
    {{ (m : Loc), RET #m; m ↦$ agentMap }} := by
  wp_start as #Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoString)) as %m Hm
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hm" ∷ m ↦$ accM (uint.nat i - 1) ∗
      "%Hi" ∷ ⌜1 ≤ uint.nat i ∧ uint.nat i ≤ 4⌝ : IProp GF) $$ [i Hm]
  · iexists W64 1
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hal : addrs.length = 9 := rfl
    have hb : 0 ≤ sint.Z (i - W64 1) ∧ sint.Z (i - W64 1) < sint.Z sl.len := by word
    simp only [hb, _root_.and_self, ↓reduceIte]
    list_elem addrs (uint.nat i - 1) as a
    wp_apply wp_load_slice_index sl (sint.Z (i - W64 1)) addrs DFrac.discard a hb.1 $$ [$Hsl] with -
    · ipureintro; rw [show (sint.Z (i - W64 1)).toNat = uint.nat i - 1 by word]; exact Ha_lookup
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_for_post
    iframe
    iexists i + W64 1
    rw [← accM_step i a Hi.1 (by word) Ha_lookup]
    iframe
    ipureintro; word
  have h4 : i = W64 4 := by word
  subst h4
  ihave HJ : (∃ (j : w64), "j" ∷ j_ptr ↦ j ∗ "Hm" ∷ m ↦$ lrnM (uint.nat j) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ 2⌝ : IProp GF) $$ [j Hm]
  · iexists W64 0
    rw [show lrnM (uint.nat (W64 0)) = accM (uint.nat (W64 4) - 1) from rfl]
    iframe
    ipureintro; word
  wp_for HJ
  wp_if_destruct
  · have hal : addrs.length = 9 := rfl
    have hb : 0 ≤ sint.Z (W64 3 + j) ∧ sint.Z (W64 3 + j) < sint.Z sl.len := by
      word
    simp only [hb, _root_.and_self, ↓reduceIte]
    list_elem addrs (3 + uint.nat j) as a
    wp_apply wp_load_slice_index sl (sint.Z (W64 3 + j)) addrs DFrac.discard a hb.1
      $$ [$Hsl] with -
    · ipureintro; rw [show (sint.Z (W64 3 + j)).toNat = 3 + uint.nat j by word]
      exact Ha_lookup
    wp_apply wp_netLearnerId
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_for_post
    iframe
    iexists j + W64 1
    have ha : a = addrs.getD (3 + uint.nat j) [] := by
      simp [List.getD_eq_getElem?_getD, Ha_lookup]
    subst ha
    rw [← lrnM_step j (by word)]
    iframe
    ipureintro; word
  have h2 : j = W64 2 := by word
  subst h2
  ihave HC : (∃ (c : w64), "c" ∷ c_ptr ↦ c ∗ "Hm" ∷ m ↦$ cliM (uint.nat c) ∗
      "%Hc" ∷ ⌜uint.nat c ≤ 4⌝ : IProp GF) $$ [c Hm]
  · iexists W64 0
    rw [show cliM (uint.nat (W64 0)) = lrnM (uint.nat (W64 2)) from rfl]
    iframe
    ipureintro; word
  wp_for HC
  wp_if_destruct
  · have hal : addrs.length = 9 := rfl
    have hb : 0 ≤ sint.Z (W64 3 + W64 2 + c) ∧ sint.Z (W64 3 + W64 2 + c) < sint.Z sl.len := by word
    simp only [hb, _root_.and_self, ↓reduceIte]
    list_elem addrs (5 + uint.nat c) as a
    wp_apply wp_load_slice_index sl (sint.Z (W64 3 + W64 2 + c)) addrs DFrac.discard a hb.1 $$ [$Hsl] with -
    · ipureintro; rw [show (sint.Z (W64 3 + W64 2 + c)).toNat = 5 + uint.nat c by word]
      exact Ha_lookup
    wp_apply wp_netProposerId
    wp_apply wp_mapInsert $$ Hm as Hm
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (W64 3 + W64 2 + c)) addrs DFrac.discard a hb.1 $$ [$Hsl] with -
    · ipureintro; rw [show (sint.Z (W64 3 + W64 2 + c)).toNat = 5 + uint.nat c by word]
      exact Ha_lookup
    wp_apply wp_netBoxId
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_for_post
    iframe
    iexists c + W64 1
    have ha : a = addrs.getD (5 + uint.nat c) [] := by
      simp [List.getD_eq_getElem?_getD, Ha_lookup]
    subst ha
    rw [← cliM_step c (by word)]
    iframe
    ipureintro; word
  have h4 : c = W64 4 := by word
  subst h4
  rw [show uint.nat (W64 4) = 4 from rfl, cliM_agentMap]
  wp_end

/-! ## The address protocols of the agents' map -/

/-- Every value of `m` is a configured address. -/
def MapIn (m : GMap w64 GoString) : Prop := ∀ k a, m !! k = some a → a ∈ addrs

theorem mapIn_empty : MapIn ∅ := by
  intro k a h; simp at h

theorem mapIn_insert {m : GMap w64 GoString} (hm : MapIn m) (i : w64) {x : GoString}
    (hx : x ∈ addrs) : MapIn (<[i := x]> m) := by
  intro k a h
  rw [GMap.lookup_insert_Some] at h
  rcases h with ⟨-, rfl⟩ | ⟨-, h⟩
  · exact hx
  · exact hm k a h

theorem agentMap_in : MapIn agentMap := by
  unfold agentMap
  repeat (first | exact mapIn_empty | refine mapIn_insert ?_ _ (by decide))

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] 
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

theorem allProtos_map (Γ : Names) (m : GMap w64 GoString) (hm : MapIn m) :
    allProtos (GF := GF) Γ ⊢ [∗map] _id ↦ a ∈ m, addrProto a (wireProto (msgOK Γ)) noProto := by
  iintro #H
  iapply BigSepM.bigSepM_forall_elim
  iintro %k %a %h
  unfold allProtos
  iapply BigSepL.bigSepL_mem (hm k a h) $$ H

theorem allProtos_addr (Γ : Names) (a : GoString) (ha : a ∈ addrs) :
    allProtos (GF := GF) Γ ⊢ addrProto a (wireProto (msgOK Γ)) noProto := by
  iintro #H
  unfold allProtos
  iapply BigSepL.bigSepL_mem ha $$ H

theorem clientTok_lock (Γ : Names) (c : w64) (hc : uint.nat c < 4) :
    clientTok (GF := GF) Γ c ⊢
      if [false, false, false, false][uint.nat c]? = some false then clientTok Γ c else iprop(True) := by
  rw [show [false, false, false, false][uint.nat c]? = some false by
    rcases w64_lt4 c hc with rfl | rfl | rfl | rfl <;> rfl]
  simp only [↓reduceIte]
  exact .rfl

end ghost

/-! ## `NewNetCluster` -/

theorem NewNetCluster.wp_proof
    (wp_newTCPNode : newTCPNode.spec (GF := GF) (hG := hG))
    (wp_serve : tcpNode.serve.spec (GF := GF) (hG := hG)) :
    NewNetCluster.spec (GF := GF) (hG := hG) := fun Γ sl c hc => by
  wp_start as ⟨#Hpx, #Hsl, #Hprotos, Htoks⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_netProposerId
  wp_apply wp_netBoxId
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %ids ⟨Hlsl, -⟩
  rw [show ([W64 1001 + c, zero_val w64].set (sint.nat (W64 (0 + 1))) (W64 3001 + c)) = clientIds c
    from rfl]
  wp_auto
  wp_apply wp_agentAddrs sl $$ [$Hsl] as %am Ham
  ihave #Hmap := allProtos_map Γ agentMap agentMap_in $$ Hprotos
  wp_apply wp_newTCPNode (msgOK Γ) am agentMap _ (clientIds c) (DFrac.own 1) $$ [$Ham $Hlsl $Hmap]
    as %nd ⟨#Hnode, Hlsl⟩
  have hal : addrs.length = 9 := rfl
  have hb : 0 ≤ sint.Z (W64 3 + W64 2 + c) ∧ sint.Z (W64 3 + W64 2 + c) < sint.Z sl.len := by word
  simp only [hb, _root_.and_self, ↓reduceIte]
  list_elem addrs (5 + uint.nat c) as a
  wp_apply wp_load_slice_index sl (sint.Z (W64 3 + W64 2 + c)) addrs DFrac.discard a hb.1 $$ [$Hsl] with -
  · ipureintro; rw [show (sint.Z (W64 3 + W64 2 + c)).toNat = 5 + uint.nat c by word]
    exact Ha_lookup
  ihave #Hp0 := allProtos_addr Γ a (List.mem_of_getElem? Ha_lookup) $$ Hprotos
  wp_apply wp_serve (msgOK Γ) nd agentMap (clientIds c) a (W64 50) $$ [$Hnode $Hp0] as %ok -
  wp_apply wp_acceptorIds as %asl Hasl
  wp_apply +noauto (wp_slice_make2 (V := Bool) (W64 4)) as %usl ⟨Husl, -⟩
  · ipureintro; word
  iapply fupd_wp
  imod sync.init_Mutex (clusterLock Γ c usl) ⊤ «$v2_ptr» $$ «$v2» [Husl Htoks] with #Hlock
  · inext
    unfold clusterLock
    iexists _
    iframe Husl
    isplitr
    · ipureintro; rfl
    rw [show List.replicate 4 (zero_val Bool) = [false, false, false, false] from rfl]
    iapply clientTok_lock Γ c hc $$ Htoks
  imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
  imodintro
  wp_pures
  wp_alloc cl as Hcl
  iStructNamed Hcl
  ipersist node
  ipersist acceptors
  ipersist mu
  ipersist used
  wp_auto
  iapply HΦ
  unfold is_cluster
  iexists nd, asl, «$v2_ptr», usl
  iframe Hpx Hnode Hlock Hasl node acceptors mu used

/-! ## `decision` -/

/-- `decision`'s lock invariant: the latest learned value, if known, is chosen. -/
def decisionInv (Γ : Names) (dp : Loc) : IProp GF :=
  iprop(∃ (v : GoString) (k : Bool) (n : w64),
    dp.[decision, go!"value"] ↦ v ∗ dp.[decision, go!"known"] ↦ k ∗
    dp.[decision, go!"changes"] ↦ n ∗
    (if k then chosenW Γ v ∗ ⌜(v.length : Int) < 2 ^ 48⌝ else True))

/-- A learner's decision (persistent). -/
def is_decision (Γ : Names) (dp : Loc) : IProp GF :=
  iprop(∃ mu : Loc, dp.[decision, go!"mu"] ↦□ mu ∗ sync.isMutex mu (decisionInv Γ dp))

instance is_decision_persistent (Γ : Names) (dp : Loc) :
    Persistent (is_decision (GF := GF) Γ dp) := by
  unfold is_decision; infer_instance

theorem wp_decision_set (Γ : Names) (dp : Loc) (v : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ is_decision Γ dp ∗ chosenW Γ v ∗
        ⌜(v.length : Int) < 2 ^ 48⌝ }}
      (App (Val (dp @!! go.GoType.PointerType decision.ty @!! go!"set")) (Val #v))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hd, #Hch, %Hv⟩
  unfold is_decision
  icases Hd with ⟨%mu, #Hmu, #Hlock⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  unfold decisionInv
  icases HR with ⟨%v0, %k, %n, Hval, Hknown, Hch0, -⟩
  wp_auto
  cases k
  all_goals (wp_auto)
  all_goals (try wp_if_destruct)
  all_goals (
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hval Hknown Hch0]
    · iexists _, _, _; iframe; simp only [↓reduceIte]; iframe Hch; ipureintro; exact Hv
    wp_end)

theorem wp_decision_get (Γ : Names) (dp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ is_decision Γ dp }}
      (App (Val (dp @!! go.GoType.PointerType decision.ty @!! go!"get")) (Val #()))
    {{ (v : GoString) (k : Bool) (n : w64), RET (PairV (PairV #v #k) #n);
        if k then chosenW Γ v ∗ ⌜(v.length : Int) < 2 ^ 48⌝ else True }} := by
  wp_start as #Hd
  unfold is_decision
  icases Hd with ⟨%mu, #Hmu, #Hlock⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  unfold decisionInv
  icases HR with ⟨%v0, %k, %n, Hval, Hknown, Hch0, Hif⟩
  wp_auto
  ihave Hdup : (if k then chosenW Γ v0 ∗ ⌜(v0.length : Int) < 2 ^ 48⌝ else True) ∗
      (if k then chosenW Γ v0 ∗ ⌜(v0.length : Int) < 2 ^ 48⌝ else True) $$ [Hif]
  · cases k
    · simp only [Bool.false_eq_true, ↓reduceIte]; iframe
    · simp only [↓reduceIte]; icases Hif with ⟨#Hc, %Hl⟩; iframe Hc; ipureintro; exact ⟨Hl, Hl⟩
  icases Hdup with ⟨Hif, Hif2⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hval Hknown Hch0 Hif]
  · iexists _, _, _; iframe
  wp_end

/-! ## `announce`, `runLearner` -/

theorem own_net_me (nt : Loc) (Φ : message → IProp GF) (nd : Loc) (me : w64) :
    own_net nt Φ nd me ⊢ own_net nt Φ nd me ∗ nt.[tcpNetwork, go!"me"] ↦□ me := by
  iintro H
  unfold own_net
  icases H with ⟨%cm, %conns, #H1, #H2, #H3, Hcm, Hconns⟩
  isplitl [Hcm Hconns]
  · iexists cm, conns
    isplitr; · iexact H1
    isplitr; · iexact H2
    isplitr; · iexact H3
    iframe
  · iexact H2

theorem wp_announce (wp_send : tcpNetwork.send.spec (GF := GF) (hG := hG)) (Γ : Names)
    (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (dp : Loc) (meId : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ is_node nd (msgOK Γ) amap ids ∗
        own_net nt (msgOK Γ) nd meId ∗ is_decision Γ dp }}
      (App (App (App (Val (@! announce)) (Val #nt)) (Val #dp)) (Val #(W64 4)))
    {{ RET #(); False }} := by
  wp_start as ⟨#Hnode, Hnet, #Hd⟩
  icases own_net_me nt _ nd meId $$ Hnet with ⟨Hnet, #Hme⟩
  wp_auto
  ihave HI : (∃ (s t : w64), "sent" ∷ sent_ptr ↦ s ∗ "ticks" ∷ ticks_ptr ↦ t : IProp GF)
    $$ [sent ticks]
  · iexists _, _; iframe
  wp_for HI
  wp_apply wp_decision_get Γ dp $$ [$Hd] as %v %k %n Hif
  cases k
  case false =>
    wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe; iexists _, _; iframe
  simp only [↓reduceIte]
  icases Hif with ⟨#Hch, %Hvl⟩
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · ihave HC : (∃ c : w64, "c" ∷ c_ptr ↦ c ∗ "%Hc" ∷ ⌜uint.nat c ≤ 4⌝ : IProp GF) $$ [c]
      · iexists _; iframe; ipureintro; word
      wp_for HC
      wp_if_destruct
      · wp_apply wp_netBoxId
        have hc4 : uint.nat c < 4 := by word
        wp_apply wp_send (msgOK Γ) nt nd amap ids meId _ $$ [$Hnode $Hnet] as Hnet
        · isplitr
          · iapply (msgOK_box Γ c hc4
              { from' := meId, to' := W64 3001 + c, typ' := W64 5, n' := 0, prevn' := 0,
                value' := v } rfl).2
            iframe Hch
            ipureintro; rfl
          · ipureintro; exact Hvl
        wp_for_post
        iframe
        iexists _; iframe; ipureintro; word
      wp_apply time.wp_Sleep
      wp_for_post
      iframe; iexists _, _; iframe
    · wp_apply time.wp_Sleep
      wp_for_post
      iframe; iexists _, _; iframe
  · ihave HC : (∃ c : w64, "c" ∷ c_ptr ↦ c ∗ "%Hc" ∷ ⌜uint.nat c ≤ 4⌝ : IProp GF) $$ [c]
    · iexists _; iframe; ipureintro; word
    wp_for HC
    wp_if_destruct
    · wp_apply wp_netBoxId
      have hc4 : uint.nat c < 4 := by word
      wp_apply wp_send (msgOK Γ) nt nd amap ids meId _ $$ [$Hnode $Hnet] as Hnet
      · isplitr
        · iapply (msgOK_box Γ c hc4
            { from' := meId, to' := W64 3001 + c, typ' := W64 5, n' := 0, prevn' := 0,
              value' := v } rfl).2
          iframe Hch
          ipureintro; rfl
        · ipureintro; exact Hvl
      wp_for_post
      iframe
      iexists _; iframe; ipureintro; word
    wp_apply time.wp_Sleep
    wp_for_post
    iframe; iexists _, _; iframe

theorem wp_runLearner (wp_send : tcpNetwork.send.spec (GF := GF) (hG := hG))
    (wp_learn : learner.learn.spec (GF := GF) (hG := hG)) (Γ : Names)
    (lp nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (id : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ own_learner Γ lp id ∗ is_node nd (msgOK Γ) amap ids ∗
        own_net nt (msgOK Γ) nd id }}
      (App (App (App (Val (@! runLearner)) (Val #lp)) (Val #nt)) (Val #(W64 4)))
    {{ RET #(); False }} := by
  wp_start as ⟨Hl, #Hnode, Hnet⟩
  wp_auto
  iStructNamed «$r0»
  iapply fupd_wp
  imod sync.init_Mutex (decisionInv Γ «$r0_ptr») ⊤ «$v0_ptr» $$ «$v0» [value known changes] with #Hlock
  · inext
    unfold decisionInv
    iexists _, _, _
    iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  ipersist mu
  imodintro
  ihave #Hd : is_decision Γ «$r0_ptr» $$ []
  · unfold is_decision; iexists «$v0_ptr»; iframe mu Hlock
  irename : (iprop("_" ∷ True) : IProp GF) => Hjunk
  iclear Hjunk
  wp_apply wp_fork $$ [Hnet]
  · wp_apply wp_announce wp_send Γ nt nd amap ids «$r0_ptr» id $$ [$Hnode $Hnet $Hd] as %hf
    exact hf.elim
  wp_for
  wp_apply wp_learn Γ lp id $$ [$Hl] as %v ⟨Hl, #Hch, %Hv⟩
  wp_apply wp_decision_set Γ «$r0_ptr» v $$ [$Hd $Hch]
  · ipureintro; exact Hv
  wp_for_post
  iframe

/-! ## `RunServer` -/

theorem RunServer.wp_proof
    (wp_newTCPNode : newTCPNode.spec (GF := GF) (hG := hG))
    (wp_serve : tcpNode.serve.spec (GF := GF) (hG := hG))
    (wp_network : tcpNode.network.spec (GF := GF) (hG := hG))
    (wp_send : tcpNetwork.send.spec (GF := GF) (hG := hG))
    (wp_newAcceptor : newAcceptor.spec (GF := GF) (hG := hG))
    (wp_acc_run : acceptor.run.spec (GF := GF) (hG := hG))
    (wp_newLearner : newLearner.spec (GF := GF) (hG := hG))
    (wp_learn : learner.learn.spec (GF := GF) (hG := hG)) :
    RunServer.spec (GF := GF) (hG := hG) := fun Γ sl me hme => by
  wp_start as ⟨#Hpx, #Hsl, #Hprotos, Hst⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_agentAddrs sl $$ [$Hsl] as %am Ham
  ihave #Hmap := allProtos_map Γ agentMap agentMap_in $$ Hprotos
  have hal : addrs.length = 9 := rfl
  wp_if_destruct
  · -- an acceptor
    have h3 : uint.nat me ≤ 3 := by word
    simp only [h3, ↓reduceIte]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %isl ⟨Hisl, -⟩
    wp_auto
    wp_apply wp_newTCPNode (msgOK Γ) am agentMap _ [me] (DFrac.own 1) $$ [$Ham $Hisl $Hmap]
      as %nd ⟨#Hnode, -⟩
    have hb : 0 ≤ sint.Z (me - W64 1) ∧ sint.Z (me - W64 1) < sint.Z sl.len := by word
    have ham : addrs[(sint.Z (me - W64 1)).toNat]? = some (addrs.getD (uint.nat me - 1) []) := by
      rw [show (sint.Z (me - W64 1)).toNat = uint.nat me - 1 by word]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show uint.nat me - 1 < addrs.length by word)]
    have hmem : addrs.getD (uint.nat me - 1) [] ∈ addrs := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show uint.nat me - 1 < addrs.length by word)]
    ihave #Hpme := allProtos_addr Γ _ hmem $$ Hprotos
    wp_for
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (me - W64 1)) addrs DFrac.discard _ hb.1 $$ [$Hsl] with -
    · ipureintro; exact ham
    wp_apply wp_serve (msgOK Γ) nd agentMap [me] _ (W64 10) $$ [$Hnode $Hpme] as %ok -
    cases ok
    case false =>
      simp only [Bool.not_false]
      cleanup_bool_decide
      wp_auto
      wp_for_post
      iframe
    simp only [Bool.not_true]
    cleanup_bool_decide
    wp_auto
    wp_apply wp_network (msgOK Γ) nd agentMap [me] me $$ [$Hnode] as %nt Hnt
    wp_apply wp_learnerIds as %lsl Hlsl
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hlsl with #Hlsl
    imodintro
    have hacc : me ∈ accIds := by
      rcases w64_le3 me hme.1 h3 with rfl | rfl | rfl <;> decide
    wp_apply wp_newAcceptor Γ me nt nd agentMap [me] lsl hacc $$ [Hnt Hst] as %ap Hap
    · unfold agentEnv
      iframe Hpx Hnode Hnt Hst Hlsl
      ipureintro; simp
    wp_apply wp_acc_run Γ ap me $$ [$Hap] as %hf
    exact hf.elim
  -- a learner
  have h45 : 3 < uint.nat me := by word
  simp only [show ¬ uint.nat me ≤ 3 by omega, ↓reduceIte]
  wp_if_destruct
  · wp_if_destruct
    ·
      have hj : uint.nat me = 4 ∨ uint.nat me = 5 := by omega
      have hlid : W64 2001 + (me - W64 3 - W64 1) ∈ lrnIds := by
        rcases hj with h | h
        · rw [show me = W64 4 by word]; decide
        · rw [show me = W64 5 by word]; decide
      wp_apply wp_netLearnerId
      generalize hl : W64 2001 + (me - W64 3 - W64 1) = lid at hlid
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %isl ⟨Hisl, -⟩
      wp_auto
      wp_apply wp_newTCPNode (msgOK Γ) am agentMap _ [lid] (DFrac.own 1) $$ [$Ham $Hisl $Hmap]
        as %nd ⟨#Hnode, -⟩
      have hb : 0 ≤ sint.Z (me - W64 1) ∧ sint.Z (me - W64 1) < sint.Z sl.len := by word
      have ham : addrs[(sint.Z (me - W64 1)).toNat]? = some (addrs.getD (uint.nat me - 1) []) := by
        rw [show (sint.Z (me - W64 1)).toNat = uint.nat me - 1 by word]
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show uint.nat me - 1 < addrs.length by word)]
      have hmem : addrs.getD (uint.nat me - 1) [] ∈ addrs := by
        simp [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show uint.nat me - 1 < addrs.length by word)]
      ihave #Hpme := allProtos_addr Γ _ hmem $$ Hprotos
      wp_for
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z (me - W64 1)) addrs DFrac.discard _ hb.1 $$ [$Hsl] with -
      · ipureintro; exact ham
      wp_apply wp_serve (msgOK Γ) nd agentMap [lid] _ (W64 10) $$ [$Hnode $Hpme]
        as %ok -
      cases ok
      case false =>
        simp only [Bool.not_false]
        cleanup_bool_decide
        wp_auto
        wp_for_post
        iframe
      simp only [Bool.not_true]
      cleanup_bool_decide
      wp_auto
      wp_apply wp_network (msgOK Γ) nd agentMap [lid] lid $$ [$Hnode] as %nt Hnt
      wp_apply wp_acceptorIds as %asl Hasl
      iapply fupd_wp
      imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
      imodintro
      wp_apply wp_newLearner Γ lid nt nd agentMap [lid] asl hlid $$ [Hnt] as %lp Hlp
      · unfold agentEnv
        iframe Hpx Hnode Hnt Hasl
        ipureintro; simp
      wp_apply wp_network (msgOK Γ) nd agentMap [lid] lid $$ [$Hnode] as %nt2 Hnt2
      wp_apply wp_runLearner wp_send wp_learn Γ lp nt2 nd agentMap [lid] lid
        $$ [$Hlp $Hnode $Hnt2] as %hf
      exact hf.elim
    · exfalso; word
  · exfalso; word

/-! ## `Propose` -/

theorem NetCluster.Propose.wp_proof
    (wp_network : tcpNode.network.spec (GF := GF) (hG := hG))
    (wp_poll : tcpNetwork.poll.spec (GF := GF) (hG := hG))
    (wp_recv : tcpNetwork.recv.spec (GF := GF) (hG := hG))
    (wp_newProposer : newProposer.spec (GF := GF) (hG := hG))
    (wp_run : proposer.run.spec (GF := GF) (hG := hG)) :
    NetCluster.Propose.spec (GF := GF) (hG := hG) := fun Γ clp c waitMs v Q hc hv => by
  iintro #Hpkg #Hcl HAU
  unfold is_cluster
  icases Hcl with ⟨%nd, %asl, %mu, %usl, #Hnd, #Hasl, #Hmu, #Hu, #Haccs, #Hpx, #Hnode, #Hlock⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  unfold clusterLock
  icases HR with ⟨%used, Husl, %Hlen, Htoks⟩
  ihave %HuslLen := ownSlice_len _ _ _ $$ Husl
  have hb : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z usl.len := by word
  simp only [hb, _root_.and_self, ↓reduceIte]
  list_elem used (uint.nat c) as u
  wp_apply wp_load_slice_index usl (sint.Z c) used _ u hb.1 $$ [Husl] with Husl
  · iframe; ipureintro; rw [show (sint.Z c).toNat = uint.nat c by word]; exact Hu_lookup
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_store_slice_index usl (sint.Z c) used true $$ [Husl] with Husl
  · iframe; ipureintro; word
  rw [show (sint.Z c).toNat = uint.nat c by word]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Husl]
  · iexists _
    iframe Husl
    isplitr
    · ipureintro; simpa using Hlen
    rw [List.getElem?_set_self (by omega)]
    simp only [Option.some.injEq, Bool.true_eq_false, ↓reduceIte]
    itrivial
  rw [Hu_lookup]
  cases u
  case true =>
    wp_auto
    iright; ipureintro; exact ⟨_, rfl⟩
  simp only [↓reduceIte]
  unfold clientTok
  icases Htoks with ⟨Hrtok, Hptok, Hdtok⟩
  wp_auto
  wp_apply wp_netBoxId
  wp_apply wp_network (msgOK Γ) nd agentMap (clientIds c) (W64 3001 + c) $$ [$Hnode] as %box Hbox
  have hbox : W64 3001 + c ∈ clientIds c := (box_ids c hc).2.2.2.2
  wp_for
  wp_apply wp_poll (msgOK Γ) box nd agentMap (clientIds c) (W64 3001 + c) hbox $$ [$Hnode $Hbox]
    as %m %ok ⟨Hbox, -⟩
  cases ok
  case true =>
    wp_auto
    wp_for_post
    iframe
  wp_auto
  wp_for_post
  wp_apply wp_netProposerId
  wp_apply wp_netProposerId
  wp_apply wp_network (msgOK Γ) nd agentMap (clientIds c) (W64 1001 + c) $$ [$Hnode] as %nt Hnt
  obtain ⟨hpid, hpc⟩ := prop_ids c hc
  wp_apply wp_newProposer Γ (W64 1001 + c) v nt nd agentMap (clientIds c) asl hpid hv
    $$ [Hnt] as %pp Hpp
  · unfold agentEnv
    iframe Hpx Hnode Hnt Haccs
    ipureintro; exact hpc
  iapply fupd_wp
  imod inv_alloc (slotN c) ⊤ (slotContent Γ c v Q) $$ [HAU] with #Hslot
  · inext; unfold slotContent; ileft; iexact HAU
  imod inv_register Γ ⊤ c v Q CoPset.subseteq_top $$ Hpx Hrtok Hslot with #Hreg
  imodintro
  wp_apply wp_fork $$ [Hpp Hptok]
  · wp_apply wp_run Γ pp (W64 1001 + c) v c $$ [$Hpp $Hptok $Hreg]
    itrivial
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j : IProp GF) $$ [i]
  · iexists _; iframe
  wp_for HI
  wp_if_destruct
  · wp_apply (lc := 2) wp_recv (msgOK Γ) box nd agentMap (clientIds c) (W64 3001 + c) _ hbox
      $$ [$Hnode $Hbox] as %m %ok ⟨Hbox, Hm⟩
    cases ok
    case false =>
      wp_auto
      wp_for_post
      iframe
      iexists _; iframe
    simp only [↓reduceIte]
    unfold inboxP
    icases Hm with ⟨Hok, %Hto, %Hwf⟩
    ihave Hok := (msgOK_box Γ c hc m Hto).1 $$ Hok
    icases Hok with ⟨%Htyp, #Hch⟩
    iapply fupd_wp
    ihave Hlc := lc_split.2 $$ [$Hlc1 $Hlc2]
    imod inv_return Γ c v m.value' Q $$ Hpx Hlc Hslot Hdtok Hch with HQ
    imodintro
    wp_auto
    simp only [Htyp, _root_.decide_true]
    wp_auto
    wp_for_post
    ileft
    iexists m.value'
    isplitr
    · ipureintro; exact ⟨rfl, Hwf⟩
    iexact HQ
  iright; ipureintro; exact ⟨_, rfl⟩

end proofs

end github_com.xiang90.paxos

end Perennial
