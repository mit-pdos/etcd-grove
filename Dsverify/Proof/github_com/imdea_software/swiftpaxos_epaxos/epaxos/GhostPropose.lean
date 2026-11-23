/-
`handlePropose`'s ghost step over the bodies (`ep_propose`): the batch's fresh proposals enter
the model (`clientPropose`, their op tokens go into the invariant), the re-proposals' tokens are
consumed, and the model's `propose` step is taken on the whole batch (fix B5: a sub-multiset of
the channel).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostExec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Replica

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Multisets as lists -/

theorem count_diff {α : Type} [DecidableEq α] (a : α) :
    ∀ (l t : List α), (l.diff t).count a = l.count a - t.count a
  | l, [] => by simp
  | l, b :: t => by
    rw [List.diff_cons, count_diff a (l.erase b) t, List.count_erase, List.count_cons]
    by_cases h : b = a
    · subst h; simp; omega
    · have : (b == a) = false := by simp [h]
      simp [this]

theorem subperm_of_count {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h : ∀ a, l₁.count a ≤ l₂.count a) : l₁.Subperm l₂ :=
  List.subperm_ext_iff.mpr (fun a _ => h a)

theorem count_le_of_subperm {α : Type} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.Subperm l₂)
    (a : α) : l₁.count a ≤ l₂.count a := h.count_le a

/-- The lookup of a list without repeated keys, one entry erased. -/
theorem lookup_erase_nodup : ∀ (l : List (Nat × Proposal)) (k : Nat) (p : Proposal),
    (l.map Prod.fst).Nodup → (k, p) ∈ l → ∀ k',
      (l.erase (k, p)).lookup k' = if k' = k then none else l.lookup k'
  | [], _, _, _, h, _ => by simp at h
  | (a, b) :: l0, k, p, hnd, hmem, k' => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases e : (a, b) = (k, p)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      rw [List.erase_cons_head]
      by_cases hk : k' = a
      · subst hk; rw [if_pos rfl]; exact lookup_none_of_not_mem hnd.1
      · rw [if_neg hk]
        have : (k' == a) = false := by simp [hk]
        show List.lookup k' l0 = List.lookup k' ((a, b) :: l0)
        rw [List.lookup_cons, this]
    · have hmem' : (k, p) ∈ l0 := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm e
        · exact h
      rw [List.erase_cons_tail (by
        intro h; exact e (by simpa using h))]
      have ih := lookup_erase_nodup l0 k p hnd.2 hmem' k'
      have hak : a ≠ k := fun h => hnd.1 (h ▸ List.mem_map_of_mem hmem')
      by_cases hk : k' = a
      · subst hk
        rw [if_neg hak]
        unfold List.lookup; simp
      · have : (k' == a) = false := by simp [hk]
        rw [List.lookup_cons, this]
        simp only []
        rw [ih]
        by_cases h2 : k' = k
        · simp [h2]
        · rw [if_neg h2, if_neg h2, List.lookup_cons, this]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Consume one re-proposal token. -/
theorem chan_consume1 (γ : EpNames) (i : Nat) (c : List Proposal) (p : Proposal) :
    chanAuthB (GF := GF) γ i c -∗ chanTok γ i p ==∗ chanAuthB γ i (c.erase p) := by
  unfold chanAuthB
  iintro ⟨%M, %l, HM, %hM⟩ ⟨%k, Hk⟩
  obtain ⟨hlk, hnd, hsub⟩ := hM
  ihave %hl := ghost_map_lookup $$ HM Hk
  have hmem : (k, p) ∈ l := lookup_mem (by rw [← hlk]; exact hl)
  imod ghost_map_delete $$ HM Hk with HM
  imodintro
  iexists _, l.erase (k, p)
  iframe HM
  ipureintro
  refine ⟨?_, ?_, ?_⟩
  · intro k'
    rw [GMap.lookup_delete_iff, lookup_erase_nodup l k p hnd hmem k', hlk]
    by_cases h : k = k'
    · subst h; simp
    · simp [h, Ne.symm h]
  · exact hnd.sublist ((List.erase_sublist).map _)
  · have hl : l.Perm ((k, p) :: l.erase (k, p)) := List.perm_cons_erase hmem
    have hm := hl.map Prod.snd
    simp only [List.map_cons] at hm
    have h1 : ((l.erase (k, p)).map Prod.snd).Perm ((l.map Prod.snd).erase p) := by
      have := hm.erase p
      simpa using this.symm
    exact h1.subperm.trans (hsub.erase p)

theorem chan_consume (γ : EpNames) (i : Nat) (T : List Proposal) :
    ∀ c, chanAuthB (GF := GF) γ i c -∗ ([∗list] p ∈ T, chanTok γ i p) ==∗ chanAuthB γ i (c.diff T) := by
  induction T with
  | nil => intro c; iintro H -; imodintro; simp; iexact H
  | cons p T ih =>
    intro c
    iintro H Ht
    ihave ⟨Hp, Ht⟩ := BigSepL.bigSepL_cons.1 $$ Ht
    imod chan_consume1 γ i c p $$ H Hp with H
    rw [List.diff_cons]
    iapply ih $$ H Ht

/-- The batch, split into its fresh proposals and its re-proposals. -/
theorem batch_split (γ : EpNames) (i : Nat) (A : Proposal → IProp GF) :
    ∀ (batch : List Proposal), ([∗list] p ∈ batch, A p ∨ inChanB γ i p) ⊢
      ∃ F T : List Proposal, ⌜batch.Perm (F ++ T)⌝ ∗ ([∗list] p ∈ F, A p) ∗
        [∗list] p ∈ T, inChanB γ i p
  | [] => by
    iintro -; iexists [], []
    isplitr; · ipureintro; simp
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | p :: ps => by
    iintro H
    ihave ⟨Hp, Hs⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave ⟨%F, %T, %hp, HF, HT⟩ := batch_split γ i A ps $$ Hs
    icases Hp with (Hp | Hp)
    · iexists p :: F, T
      isplitr; · ipureintro; exact List.Perm.cons p hp
      iframe HT
      iapply BigSepL.bigSepL_cons.2
      iframe
    · iexists F, p :: T
      isplitr
      · ipureintro
        exact (List.Perm.cons p hp).trans List.perm_middle.symm
      iframe HF
      iapply BigSepL.bigSepL_cons.2
      iframe

/-- The fresh proposals' commands are their connections' inputs', which meet the premise. -/
theorem fresh_vals (γ : EpNames) (F : List Proposal) :
    ([∗list] p ∈ F, opTok (GF := GF) γ p.cid ∗ ∃ (c : w64) (inp : KvI), clientConn γ p.cid c inp ∗
      ⌜p.cmd = cmdOf inp⌝) -∗
    ⌜∀ p ∈ F, ∃ inp : KvI, inPre inp ∧ p.cmd = cmdOf inp⌝ := by
  induction F with
  | nil => iintro -; ipureintro; simp
  | cons p F ih =>
    iintro H
    ihave ⟨⟨-, %c, %inp, Hc, %hc⟩, Hs⟩ := BigSepL.bigSepL_cons.1 $$ H
    iunfold clientConn at Hc
    icases Hc with ⟨%hpre, -⟩
    ihave %hs := ih $$ Hs
    ipureintro
    intro p' hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact ⟨inp, hpre, hc⟩
    · exact hs p' hp'

/-- The fresh proposals' op tokens: their ids are new and distinct. -/
theorem fresh_ids (γ : EpNames) (S : Sys) (F : List Proposal) (B : Proposal → IProp GF) :
    ([∗list] o ∈ S.ops, connFresh o.2.cid true ∗
      ∃ (c : w64) (inp : KvI), clientConn γ o.2.cid c inp ∗ ⌜o.2.cmd = cmdOf inp⌝) -∗
    ([∗list] p ∈ F, opTok γ p.cid ∗ B p) -∗
    ⌜(∀ p ∈ F, p.cid ∉ S.ops.map (·.2.cid)) ∧ (F.map (·.cid)).Nodup⌝ := by
  induction F with
  | nil => iintro - -; ipureintro; simp
  | cons p F ih =>
    iintro Hops H
    ihave ⟨⟨Hp, -⟩, Hs⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave %hs := ih $$ Hops Hs
    ihave %h1 : ⌜p.cid ∉ S.ops.map (·.2.cid)⌝ $$ [Hops Hp]
    · iintro %hm
      obtain ⟨o, ho, hoc⟩ := List.mem_map.mp hm
      ihave ⟨⟨Ho, -⟩, -⟩ := BigSepL.bigSepL_mem_acc ho $$ Hops
      rw [hoc, opTok_unseal]; unfold opTokDef
      iapply (connFresh_excl (Gg := G) p.cid true)
      iframe
    ihave %h2 : ⌜p.cid ∉ F.map (·.cid)⌝ $$ [Hs Hp]
    · iintro %hm
      obtain ⟨q, hq, hqc⟩ := List.mem_map.mp hm
      ihave ⟨⟨Hq, -⟩, -⟩ := BigSepL.bigSepL_mem_acc hq $$ Hs
      rw [hqc]
      iapply opTok_excl $$ Hp Hq
    ipureintro
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact h1
      · exact hs.1 q hq
    · simp only [List.map_cons]; exact List.nodup_cons.mpr ⟨h2, hs.2⟩

end ghost

/-! ## The model's steps -/

/-- The `clientPropose` steps of the fresh proposals `F` at replica `i`. -/
def addOps (S : Sys) (i : Nat) (F : List Proposal) : Sys :=
  { S with ops := S.ops ++ F.map (fun p => (i, p)),
           proposeChan := upd S.proposeChan i (S.proposeChan i ++ F) }

theorem addOps_inv (i : Nat) (hi : i < nR) : ∀ (F : List Proposal) (S : Sys), Inv S →
    (∀ p ∈ F, p.cid ∉ S.ops.map (·.2.cid)) → (F.map (·.cid)).Nodup → Inv (addOps S i F)
  | [], S, hS, _, _ => by
    have : addOps S i [] = S := by simp [addOps]
    rw [this]; exact hS
  | p :: F, S, hS, hf, hnd => by
    have h1 : Inv (addOps S i [p]) := inv_step_clientPropose S i p hS hi (hf p (by simp))
    have e : addOps S i (p :: F) = addOps (addOps S i [p]) i F := by
      simp [addOps]
    rw [e]
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine addOps_inv i hi F _ h1 (fun q hq => ?_) hnd.2
    simp only [addOps, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton, not_or]
    refine ⟨hf q (List.mem_cons_of_mem _ hq), fun h => hnd.1 ?_⟩
    rw [← h]; exact List.mem_map_of_mem hq

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Replace replica `i`'s channel in the authority. -/
theorem sysAuthB_chan_set (γ : EpNames) (S S' : Sys) (i : Nat) (hi : i < nR)
    (hrest : ∀ j, j ≠ i → sameAt S S' j) (hrep : S'.rep i = S.rep i)
    (hob : S'.outbox i = S.outbox i) (hpd : S'.pending i = S.pending i)
    (hcur : S'.execCur i = S.execCur i) (hidx : S'.execIdx i = S.execIdx i) :
    sysAuthB (GF := GF) γ S -∗ (chanAuthB γ i (S.proposeChan i) ==∗ chanAuthB γ i (S'.proposeChan i)) ==∗
      sysAuthB γ S' := by
  iintro Ha Hupd
  ihave ⟨Hi, Hclose⟩ := sysAuthB_acc γ S i hi $$ Ha
  iunfold sysAuthRepB at Hi
  icases Hi with ⟨HL, Hob, Hpd, Hcu, Hch⟩
  imod Hupd $$ Hch with Hch
  imodintro
  iapply Hclose $$ %S' %hrest
  iunfold sysAuthRepB
  rw [hrep, hob, hpd, hcur, hidx]
  iframe

theorem ep_proposeB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (batch : List Proposal) (hE : ↑N ⊆ E) (hi : i < nR) (hb : batch ≠ [])
    (hfull : rowFull σ = true → batch.length = 1) (hlen : batch.length < 2 ^ 62) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ repIdleB γ i -∗
      ([∗list] p ∈ batch, iprop((opTok γ p.cid ∗ ∃ (c : w64) (inp : KvI),
        clientConn γ p.cid c inp ∗ ⌜p.cmd = cmdOf inp⌝) ∨ inChanB γ i p)) -∗ £ 1 ={E}=∗
      ⌜(∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ) ∧
        ∀ p ∈ batch, ∃ inp : KvI, inPre inp ∧ p.cmd = cmdOf inp⌝ ∗
      repFragB γ i (hPropose σ batch).1 ∗ outsOkB γ i (hPropose σ batch).2 := by
  iintro #Hinv Hf Hidle Hbatch Hlc
  ihave ⟨%F, %T, %hperm, HF, HT⟩ := batch_split γ i _ batch $$ Hbatch
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hid := sysAuthB_idle γ S i hi $$ Ha Hidle
  ihave %hT := inChan_subB γ S i T $$ Ha HT
  ihave %hfr := fresh_ids γ S F _ $$ Hops HF
  ihave %hopsS := ops_preD γ S $$ Hops
  ihave %hFv := fresh_vals γ F $$ HF
  have hvals : ∀ p ∈ batch, ∃ inp : KvI, inPre inp ∧ p.cmd = cmdOf inp := by
    intro p hp
    rcases List.mem_append.mp (hperm.mem_iff.mp hp) with hp | hp
    · exact hFv p hp
    · exact hopsS _ (hS.2.exec.chanOps i p (hT.subset hp))
  subst hσ
  -- the model
  have hSm := addOps_inv i hi F S hS hfr.1 hfr.2
  let Sm := addOps S i F
  have hcnt : ∀ a, batch.count a = F.count a + T.count a := fun a => by
    rw [hperm.count_eq, List.count_append]
  have hsub : batch.Subperm (Sm.proposeChan i) := by
    apply subperm_of_count; intro a
    simp only [Sm, addOps, upd_same, List.count_append]
    have := count_le_of_subperm hT a
    rw [hcnt]; omega
  have hidleM : Sm.idle i := ⟨hid.1, hid.2.1⟩
  have hstep : Step Sm (Sm.propose i batch) := Step.propose Sm i batch hi hidleM hb hsub hfull
  have hS' := inv_step_propose Sm i batch hSm hi hidleM hb hsub hfull
  have hXm : InvX Sm := InvX_rep_eq hX rfl rfl
  have hX' : InvX (Sm.propose i batch) := by
    refine ⟨NR_step hstep hXm.1, fun y ps hy => ?_⟩
    unfold Sys.propose at hy; rw [applyStep_owner'] at hy
    dsimp only at hy
    split at hy
    · exact hXm.2 y ps hy
    · simp only [upd] at hy
      split at hy
      · cases hy; exact hlen
      · exact hXm.2 y ps hy
  have hcrt := step_crt_mono Sm _ hSm hstep i
  -- the channel: the re-proposals' tokens consumed
  let c' := (Sm.proposeChan i).diff batch
  let S2 : Sys := if rowFull (S.rep i) then { Sm with proposeChan := upd Sm.proposeChan i c' }
    else { Sm with proposeChan := upd Sm.proposeChan i c',
                   owner := upd Sm.owner ⟨i, toN ((S.rep i).crtInstance i + 1)⟩ (some batch) }
  have hS2 : S2.rep = S.rep ∧ S2.outbox = S.outbox ∧ S2.pending = S.pending ∧
      S2.execCur = S.execCur ∧ S2.execIdx = S.execIdx ∧ S2.proposeChan = upd S.proposeChan i c' ∧
      S2.kv = S.kv ∧ S2.fired = S.fired ∧ S2.sent = S.sent ∧ S2.delivered = S.delivered ∧
      S2.ops = S.ops ++ F.map (fun p => (i, p)) := by
    simp only [S2]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, by simp [Sm, addOps], rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hS2
  have eS' : Sm.propose i batch = S2.applyStep i ((hPropose (S.rep i) batch).1,
      (hPropose (S.rep i) batch).2) := rfl
  ihave HT := inChan_toks (GF := GF) γ i T $$ HT
  imod sysAuthB_chan_set γ S S2 i hi (fun j hj => ⟨by rw [e1], by rw [e2], by rw [e3], by rw [e4],
      by rw [e5], by rw [e6]; simp [upd_other _ _ _ _ hj]⟩) (by rw [e1]) (by rw [e2]) (by rw [e3])
      (by rw [e4]) (by rw [e5]) $$ Ha [HT] with Ha
  · iintro Hch
    imod chan_consume γ i T _ $$ Hch HT with Hch
    imodintro
    iapply chanAuthB_mono γ i _ _ ?_ $$ Hch
    rw [e6, upd_same]
    apply subperm_of_count; intro a
    simp only [c', Sm, addOps, upd_same, count_diff, List.count_append]
    rw [hcnt]; omega
  -- the replica's step
  generalize hS'def : Sm.propose i batch = S' at hstep hS' hX' hcrt eS'
  have hrest : ∀ j, j ≠ i → sameAt S2 S' j := fun j hj => by
    rw [eS']; exact applyStep_sameAt _ _ i j _ hj ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hrep : S'.rep i = (hPropose (S.rep i) batch).1 := by rw [eS']; simp
  have hcrt' : ∀ q, zz ((S.rep i).crtInstance q) ≤ zz ((hPropose (S.rep i) batch).1.crtInstance q) :=
    fun q => by have := hcrt q; rwa [hrep] at this
  have hout : ∀ to, S'.outbox i to = S2.outbox i to ++ sendsToB (hPropose (S.rep i) batch).2 to :=
    fun to => by rw [eS', sendsToB_eq]; simp
  have hpend : S'.pending i = pendOf (hPropose (S.rep i) batch).2 := by
    rw [eS', pendOf_eq]; simp [e3, hid.1]
  have hcur : S'.execCur i = S2.execCur i ∧ S'.execIdx i = S2.execIdx i := by rw [eS']; simp
  have hchan : S'.proposeChan i = S2.proposeChan i ++
      (hPropose (S.rep i) batch).2.filterMap Out.reprop := by rw [eS']; simp
  ihave Hidle : repIdleB γ i $$ [Hidle]
  · iexact Hidle
  imod ghost_step_idle γ i S2 S' (S.rep i) _ _ hi hrest hrep hcrt' hout hpend hcur hchan
    $$ Ha Hf Hidle with ⟨-, Ha, Hf, Hob, Hpd, Hcu, Htoks⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops HF] with -
  · inext
    iunfold epInvB
    iexists S'
    iframe Ha
    isplitr; · ipureintro; exact hS'
    isplitr; · ipureintro; exact hX'
    have ekv : S'.kv = S.kv := by rw [eS', ← e7]; unfold Sys.kv; simp
    have efd : S'.fired = S.fired := by rw [eS', ← e8]; simp
    have esn : S'.sent = S.sent := by rw [eS', ← e9]; simp
    have edl : S'.delivered = S.delivered := by rw [eS', ← e10]; simp
    have eop : S'.ops = S.ops ++ F.map (fun p => (i, p)) := by rw [eS', ← e11]; simp
    rw [ekv, efd, esn, edl, eop]
    iframe Hkv Hfired Hsents Hdel
    iapply BigSepL.bigSepL_append.2
    iframe Hops
    rw [BigSepL.bigSepL_map]
    iapply BigSepL.bigSepL_mono ?_ $$ HF
    intro _ p _
    rw [opTok_unseal]; unfold opTokDef
    exact .rfl
  imodintro
  iframe Hf
  isplitr
  · ipureintro; exact ⟨⟨S, hS, hi, rfl⟩, hvals⟩
  iunfold outsOkB
  iframe Hob Hpd Hcu
  iapply outOkB_of_toks γ i hi _ (hPropose_noRep (S.rep i) batch) $$ Htoks

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
