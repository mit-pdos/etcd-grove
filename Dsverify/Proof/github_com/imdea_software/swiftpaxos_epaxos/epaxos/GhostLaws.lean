/-
The laws of the protocol's ghost state over its bodies (`GhostDefs.lean`): the authority's parts
by replica, agreement and update of each fragment, the re-proposal tokens, and the common step of
a replica from idle (`ghost_step_idle`: its state, outboxes, pending broadcast and channel move
with the authority).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure helpers -/

/-- The fields of replica `j` the authority tracks are the same in `S` and `S'`. -/
def sameAt (S S' : Sys) (j : Nat) : Prop :=
  S'.rep j = S.rep j ∧ S'.outbox j = S.outbox j ∧ S'.pending j = S.pending j ∧
    S'.execCur j = S.execCur j ∧ S'.execIdx j = S.execIdx j ∧ S'.proposeChan j = S.proposeChan j

theorem range_getElem? {n i : Nat} (h : i < n) : (List.range n)[i]? = some i := by
  simp [h]

theorem range_getElem?_eq {n k j : Nat} (h : (List.range n)[k]? = some j) : j = k ∧ k < n := by
  have hk : k < n := by have := (List.getElem?_eq_some_iff.mp h).1; simpa using this
  rw [List.getElem?_range hk] at h
  exact ⟨(Option.some.inj h).symm, hk⟩

theorem crtBelow_snoc {L : List RState} {σ σ' : RState} (hL : crtBelow L σ)
    (hlast : L.getLast? = some σ)
    (hcrt : ∀ q, zz (σ.crtInstance q) ≤ zz (σ'.crtInstance q)) : crtBelow (L ++ [σ']) σ' := by
  intro σ0 h q
  rcases List.mem_append.mp h with h | h
  · exact Int.le_trans (hL σ0 h q) (hcrt q)
  · simp at h; subst h; exact Int.le_refl _

theorem subperm_map {A B : Type} (f : A → B) {l1 l2 : List A} (h : l1.Subperm l2) :
    (l1.map f).Subperm (l2.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

theorem lookup_mem {l : List (Nat × Proposal)} {k : Nat} {p : Proposal}
    (h : l.lookup k = some p) : (k, p) ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    obtain ⟨a1, a2⟩ := a
    unfold List.lookup at h
    by_cases hk : k = a1
    · subst hk; simp at h; subst h; simp
    · have : (k == a1) = false := by simp [hk]
      rw [this] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_none_of_not_mem {l : List (Nat × Proposal)} {k : Nat}
    (h : k ∉ l.map Prod.fst) : l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup_cons]
    have : (k == a1) = false := by simp [h.1]
    rw [this]; exact ih h.2

theorem fresh_key (l : List (Nat × Proposal)) :
    (l.map Prod.fst).foldr max 0 + 1 ∉ l.map Prod.fst := by
  intro h
  have : ∀ (xs : List Nat) (k : Nat), k ∈ xs → k ≤ xs.foldr max 0 := by
    intro xs; induction xs with
    | nil => intro k h; simp at h
    | cons x xs ih =>
      intro k h
      simp only [List.mem_cons] at h
      simp only [List.foldr_cons]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih k h) (Nat.le_max_right _ _)
  have := this _ _ h; omega

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-! ## Big separating conjunctions under an update -/

theorem bigSepL_bupd_mono {A : Type} (l : List A) (P Q : A → IProp GF)
    (h : ∀ a ∈ l, P a ⊢ |==> Q a) : ([∗list] a ∈ l, P a) ⊢ |==> [∗list] a ∈ l, Q a := by
  induction l with
  | nil => iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a l ih =>
    iintro H
    ihave ⟨Ha, Hl⟩ := BigSepL.bigSepL_cons.1 $$ H
    imod (h a (by simp)) $$ Ha with Ha
    imod (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))) $$ Hl with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe

/-! ## The authority by replica -/

theorem sysAuthRepB_congr (γ : EpNames) {S S' : Sys} {j : Nat} (h : sameAt S S' j) :
    sysAuthRepB (GF := GF) γ S' j = sysAuthRepB γ S j := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold sysAuthRepB; rw [h1, h2, h3, h4, h5, h6]

theorem sysAuthB_acc (γ : EpNames) (S : Sys) (i : Nat) (hi : i < nR) :
    sysAuthB (GF := GF) γ S ⊢ sysAuthRepB γ S i ∗ ∀ S' : Sys, ⌜∀ j, j ≠ i → sameAt S S' j⌝ -∗
      sysAuthRepB γ S' i -∗ sysAuthB γ S' := by
  unfold sysAuthB
  refine (BigSepL.bigSepL_lookup_acc_impl (range_getElem? hi)).trans (sep_mono_right ?_)
  iintro H %S' %Hs Hi
  ispecialize H $$ %(fun _ j => sysAuthRepB γ S' j)
  iapply H $$ [] Hi
  imodintro
  iintro %k %y %hk %hne Hy
  obtain ⟨rfl, -⟩ := range_getElem?_eq hk
  rw [show (fun (_ : Nat) (j : Nat) => sysAuthRepB γ S' j) y y = sysAuthRepB γ S y from
    sysAuthRepB_congr γ (Hs y hne)]
  iexact Hy

/-! ## Replica states -/

theorem rep_agree (γ : EpNames) (S : Sys) (i : Nat) (σ : RState) :
    sysAuthRepB (GF := GF) γ S i -∗ repFragB γ i σ -∗ ⌜S.rep i = σ⌝ := by
  unfold sysAuthRepB repFragB
  iintro ⟨⟨%L, HL, %hL⟩, -⟩ ⟨%hi, %L', HL', %hL', -⟩
  ihave %h := rsAuth_agree _ _ _ _ _ $$ HL HL'
  ipureintro
  obtain ⟨_, rfl⟩ := h
  rw [hL] at hL'; exact Option.some.inj hL'

theorem repFragB_excl (γ : EpNames) (i : Nat) (σ σ' : RState) :
    repFragB (GF := GF) γ i σ -∗ repFragB γ i σ' -∗ False := by
  unfold repFragB
  iintro ⟨%hi, %L, HL, -⟩ ⟨-, %L', HL', -⟩
  ihave %h := rsAuth_agree _ _ _ _ _ $$ HL HL'
  exfalso
  have h1 := h.1
  simp only [Qp.threeQuarters] at h1
  have : ((⟨3 / 4, by grind⟩ : Qp) + ⟨3 / 4, by grind⟩).val ≤ (1 : Qp).val := h1
  simp at this
  have h2 : (3 / 4 + 3 / 4 : Rat) ≤ 1 := this
  exact absurd h2 (by grind)

/-- The state part moves: quarter and three quarters make the whole list, which grows by the
new state. -/
theorem rep_update (γ : EpNames) (i : Nat) (L : List RState) (σ σ' : RState)
    (hi : i < nR) (hlast : L.getLast? = some σ) (hL : crtBelow L σ)
    (hcrt : ∀ q, zz (σ.crtInstance q) ≤ zz (σ'.crtInstance q)) :
    rsAuth (GF := GF) (γ.proto.rep i) Qp.quarter L -∗ rsAuth (γ.proto.rep i) Qp.threeQuarters L ==∗
      (∃ L' : List RState, rsAuth (γ.proto.rep i) Qp.quarter L' ∗ ⌜L'.getLast? = some σ'⌝) ∗
      repFragB γ i σ' := by
  iintro H1 H2
  ihave H := (rsAuth_op _ Qp.quarter Qp.threeQuarters L).2 $$ [H1 H2]
  · iframe
  have e : Qp.quarter + Qp.threeQuarters = 1 := by
    apply Subtype.ext; show (1 / 4 + 3 / 4 : Rat) = 1; grind
  rw [e]
  imod rsAuth_update_app _ L [σ'] $$ H with H
  rw [← e]
  ihave ⟨H1, H2⟩ := (rsAuth_op _ Qp.quarter Qp.threeQuarters _).1 $$ H
  imodintro
  isplitl [H1]
  · iexists L ++ [σ']; iframe H1; ipureintro; simp
  · unfold repFragB
    isplitr; · ipureintro; exact hi
    iexists L ++ [σ']; iframe H2
    ipureintro
    exact ⟨by simp, crtBelow_snoc hL hlast hcrt⟩

/-! ## The ghost variables -/

theorem gvar_agree {A : Type} [Pos.Countable A] (γ : GName) (a b : A) :
    ghostVar (GF := GF) γ (1 : Qp).half a -∗ ghostVar γ (1 : Qp).half b -∗ ⌜a = b⌝ := by
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

theorem gvar_update {A : Type} [Pos.Countable A] (γ : GName) (a b c : A) :
    ghostVar (GF := GF) γ (1 : Qp).half a -∗ ghostVar γ (1 : Qp).half b ==∗
      ghostVar γ (1 : Qp).half c ∗ ghostVar γ (1 : Qp).half c := by
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

/-! ## Re-proposal tokens -/

/-- A held token, without its replica bound. -/
abbrev chanTok (γ : EpNames) (i : Nat) (p : Proposal) : IProp GF :=
  iprop(∃ k : Nat, ghostMapElem (γ.proto.chan i) k (DFrac.own 1) p)

theorem chan_mint1 (γ : EpNames) (i : Nat) (chan : List Proposal) (p : Proposal) :
    chanAuthB (GF := GF) γ i chan ==∗ chanAuthB γ i (chan ++ [p]) ∗ chanTok γ i p := by
  unfold chanAuthB
  iintro ⟨%M, %l, HM, %hM⟩
  obtain ⟨hlk, hnd, hsub⟩ := hM
  have hk := fresh_key l
  imod ghost_map_insert ((l.map Prod.fst).foldr max 0 + 1) p
    (by rw [hlk]; exact lookup_none_of_not_mem hk) $$ HM with ⟨HM, Hk⟩
  imodintro
  isplitl [HM]
  · iexists _, ((l.map Prod.fst).foldr max 0 + 1, p) :: l
    iframe HM
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · intro k
      rw [GMap.lookup_insert_eq_iff, List.lookup_cons]
      by_cases e : (l.map Prod.fst).foldr max 0 + 1 = k
      · subst e; simp
      · rw [if_neg e]
        have : (k == (l.map Prod.fst).foldr max 0 + 1) = false := by
          simp; exact Ne.symm e
        rw [this]; exact hlk k
    · simp only [List.map_cons]; exact List.nodup_cons.mpr ⟨hk, hnd⟩
    · simp only [List.map_cons]
      exact ((List.subperm_cons p).mpr hsub).trans (List.perm_append_singleton p chan).symm.subperm
  · iexists _; iexact Hk

theorem chan_mint (γ : EpNames) (i : Nat) (ps : List Proposal) :
    ∀ chan : List Proposal, chanAuthB (GF := GF) γ i chan ==∗
      chanAuthB γ i (chan ++ ps) ∗ [∗list] p ∈ ps, chanTok γ i p := by
  induction ps with
  | nil => intro chan; iintro H; imodintro; rw [List.append_nil]; iframe; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons p ps ih =>
    intro chan
    iintro H
    imod chan_mint1 γ i chan p $$ H with ⟨H, Hp⟩
    imod ih (chan ++ [p]) $$ H with ⟨H, Hps⟩
    imodintro
    rw [List.append_assoc, List.singleton_append]
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- Held tokens, with their keys (distinct). -/
theorem chanToks_keys (γ : EpNames) (i : Nat) (ps : List Proposal) :
    ([∗list] p ∈ ps, chanTok (GF := GF) γ i p) ⊢ ∃ kps : List (Nat × Proposal),
      ⌜kps.map Prod.snd = ps ∧ (kps.map Prod.fst).Nodup⌝ ∗
      [∗list] kp ∈ kps, ghostMapElem (γ.proto.chan i) kp.1 (DFrac.own 1) kp.2 := by
  induction ps with
  | nil => iintro -; iexists []; isplitr; · ipureintro; simp
           iapply BigSepL.bigSepL_nil.2; iempintro
  | cons p ps ih =>
    iintro H
    ihave ⟨⟨%k, Hk⟩, Hps⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave ⟨%kps, %hkps, Hkps⟩ := ih $$ Hps
    ihave %hnot : ⌜k ∉ kps.map Prod.fst⌝ $$ [Hk Hkps]
    · iintro %hmem
      obtain ⟨kp, hkp, hkpk⟩ := List.mem_map.mp hmem
      ihave ⟨Hkp, -⟩ := BigSepL.bigSepL_mem_acc hkp $$ Hkps
      ihave %hne := ghostMapElem_ne _ _ _ _ _ _ $$ Hk Hkp
      exact absurd hkpk.symm hne
    iexists (k, p) :: kps
    isplitr
    · ipureintro
      exact ⟨by simp [hkps.1], List.nodup_cons.mpr ⟨hnot, hkps.2⟩⟩
    iapply BigSepL.bigSepL_cons.2
    iframe

theorem chan_lookups (γ : EpNames) (i : Nat) (M : GMap Nat Proposal)
    (kps : List (Nat × Proposal)) :
    ghostMapAuth (γ.proto.chan i) 1 M -∗
      ([∗list] kp ∈ kps, ghostMapElem (γ.proto.chan i) kp.1 (DFrac.own 1) kp.2) -∗
      ⌜∀ kp ∈ kps, M.lookup kp.1 = some kp.2⌝ := by
  induction kps with
  | nil => iintro - -; ipureintro; simp
  | cons kp kps ih =>
    iintro HM H
    ihave ⟨H1, Hs⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave %h1 := ghost_map_lookup $$ HM H1
    ihave %hs := ih $$ HM Hs
    ipureintro
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact hs x hx

theorem chan_sub (γ : EpNames) (i : Nat) (chan ps : List Proposal) :
    chanAuthB (GF := GF) γ i chan -∗ ([∗list] p ∈ ps, chanTok γ i p) -∗ ⌜ps.Subperm chan⌝ := by
  unfold chanAuthB
  iintro ⟨%M, %l, HM, %hM⟩ H
  obtain ⟨hlk, hnd, hsub⟩ := hM
  ihave ⟨%kps, %hkps, Hkps⟩ := chanToks_keys γ i ps $$ H
  ihave %hl := chan_lookups γ i M kps $$ HM Hkps
  ipureintro
  have hin : ∀ kp ∈ kps, kp ∈ l := fun kp hkp => by
    have := hl kp hkp; rw [hlk] at this; exact lookup_mem this
  have hndk : kps.Nodup := List.Pairwise.of_map Prod.fst (fun a b h e => h (e ▸ rfl)) hkps.2
  have : kps.Subperm l := List.subperm_of_subset hndk hin
  rw [← hkps.1]
  exact (subperm_map Prod.snd this).trans hsub

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
