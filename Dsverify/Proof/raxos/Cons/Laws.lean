/-
The configuration's and the consensus ghost state's laws (interface statements of stage 2,
`notes/stage2-plan.md`; proofs: package `cons`. Stage 1's proofs, for the invariant over 3
replicas, are at the project's tag `mode1-final`).
-/
module

public import Dsverify.Proof.raxos.Ghost
public import Dsverify.Proof.raxos.Cons.Lemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS
open consLemmas

/-! ### The configuration -/

/-- The client node chooses the configuration `c`, once. -/
theorem conf_choose (γ : QNames) (c : QConf) :
    ⊢@{IProp GF} confTok γ ==∗ confIs γ c := by
  iintro Ht
  unfold confTok confIs
  imod ghost_map_insert_persist () c (by rfl) $$ Ht with ⟨-, #Hel⟩
  imodintro
  iexact Hel

/-- Every replica runs the one configuration chosen. -/
theorem conf_agree (γ : QNames) (c1 c2 : QConf) :
    ⊢@{IProp GF} confIs γ c1 -∗ confIs γ c2 -∗ ⌜c1 = c2⌝ := by
  exact confIs_agree γ c1 c2

/-- Before the choice, nothing is chosen. -/
theorem conf_tok_excl (γ : QNames) (c : QConf) :
    ⊢@{IProp GF} confTok γ -∗ confIs γ c -∗ False := by
  unfold confTok confIs
  iintro Ht Hc
  ihave %h := ghost_map_lookup $$ Ht Hc
  exact absurd h (by simp)

/-! ### The leader's evidence (introduction laws, so that clients need not unfold `leadEv`) -/

/-- The round-robin leader of the first `2n` epochs. -/
theorem leadEv_rr (γ : QNames) (c : QConf) (i me : Int) (h : i.tdiv c.ep ≤ 2 * c.n)
    (hme : me = rrLeader c.n c.ep i) :
    ⊢@{IProp GF} leadEv γ c i me := by
  unfold leadEv
  ileft
  ipureintro
  exact ⟨h, hme⟩

/-- The first replica of the summary decided in the previous epoch's first slot. -/
theorem leadEv_sum (γ : QNames) (c : QConf) (i me : Int) (p : List Nat)
    (h : 2 * (c.n : Int) < i.tdiv c.ep) (hp : isPerm c.n p)
    (hme : p.head?.map (fun k : Nat => (k : Int)) = some me) :
    ⊢@{IProp GF} decided γ ((i.tdiv c.ep - 1) * c.ep) [summaryId p] -∗ leadEv γ c i me := by
  iintro Hd
  unfold leadEv
  iright
  iexists p
  iframe Hd
  ipureintro
  exact ⟨h, hp, hme⟩

/-! ### Consensus laws -/

/-- Decisions of a slot agree. -/
theorem decided_agree (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (i : Int) (a b : List GoString) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ decided γ i a -∗ decided γ i b ={E}=∗ ⌜a = b⌝ := by
  iintro #Hinv Ha Hb
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, Hrest⟩ Hclose
  unfold decided
  ihave %hma := evIn_mem γ 1 W _ $$ Hhist Ha
  ihave %hmb := evIn_mem γ 1 W _ $$ Hhist Hb
  ihave ⟨%c, #Hc, %hc⟩ := hist_reach_mem γ W _ hma $$ Hh
  have hab := (agreement (conf_n_pos hc.1) hc.2).1 i a b hma hmb
  imod Hclose $$ [Hhist Hrest] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr, Rd, S
    iframe
    iright
    iexists c
    iframe Hc
    ipureintro; exact hc
  imodintro
  ipureintro; exact hab

/-- A decision is nonempty. -/
theorem decided_nonempty (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (i : Int) (a : List GoString) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ decided γ i a ={E}=∗ ⌜a ≠ []⌝ := by
  iintro #Hinv Ha
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, Hrest⟩ Hclose
  unfold decided
  ihave %hma := evIn_mem γ 1 W _ $$ Hhist Ha
  ihave ⟨%c, #Hc, %hc⟩ := hist_reach_mem γ W _ hma $$ Hh
  have hab := (agreement (conf_n_pos hc.1) hc.2).2.1 i a hma
  imod Hclose $$ [Hhist Hrest] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr, Rd, S
    iframe
    iright
    iexists c
    iframe Hc
    ipureintro; exact hc
  imodintro
  ipureintro; exact hab

/-- A decision of an epoch's first slot from epoch `2n` on is one summary of a permutation of
the replicas (the slot's proposals are: `Step.init`; a decision is a proposal: `agreement`). -/
theorem decided_summary (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (c : QConf) (j : Int)
    (a : List GoString) (hj : sumSlot c.n c.ep j) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ decided γ j a ={E}=∗
      ⌜∃ p, isPerm c.n p ∧ a = [summaryId p]⌝ := by
  iintro #Hinv #Hc0 Ha
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, Hrest⟩ Hclose
  unfold decided
  ihave %hma := evIn_mem γ 1 W _ $$ Hhist Ha
  ihave ⟨%c', #Hc, %hc⟩ := hist_reach_mem γ W _ hma $$ Hh
  ihave %he := confIs_agree γ c c' $$ Hc0 Hc
  subst he
  obtain ⟨me, lead, hin⟩ := (agreement (conf_n_pos hc.1) hc.2).2.2 j a hma
  obtain ⟨p, hp, hpa⟩ := init_summary hc.2 hin hj
  imod Hclose $$ [Hhist Hrest] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr, Rd, S
    iframe
    iright
    iexists c
    iframe Hc
    ipureintro; exact hc
  imodintro
  ipureintro; exact ⟨p, by simpa using hp, hpa⟩

/-- A proxy issues the init token of a slot `i` at or above its frontier `n`, spending a credit;
`i` is at most one past the frontier's slot or past `m` slots known spent (`handleClientBatch`:
`proposeIndex` is `lastProposedIndex + 1`, then past decided slots). Every slot is in `[1, 600]`.
-/
theorem init_issue (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (me n m i : Int) (t : Ticket)
    (hi : n ≤ i ∧ i ≤ max n (m + 1)) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ initFront γ me n -∗ credit γ t -∗ spentLb γ m ={E}=∗
      initFront γ me (i + 1) ∗ initTok γ me i ∗ ⌜1 ≤ i ∧ i ≤ 600⌝ := by
  iintro #Hinv Hfront Hcred Hspent
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold initFront credit spentLb initTok
  icases Hspent with ⟨%L, #HL, %HmL⟩
  ihave %HSL := mono_list_auth_lb_valid γ.spent 1 S L $$ HS HL
  have hmS : m ≤ S.length := by have := HSL.2.length_le; omega
  ihave %HFrl := ghost_map_lookup $$ HFr Hfront
  ihave %HCrl := ghost_map_lookup $$ HCr Hcred
  have HFrl' : Fr !! me = some n := HFrl
  have HCrl' : Cr !! t = some () := HCrl
  by_cases htS : t ∈ S
  case pos =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 htS
    icases (BigSepL.bigSepL_lookup_acc hk).1 $$ HCrs with ⟨Hc', -⟩
    ihave %Hne := ghostMapElem_ne γ.cred t t _ () () $$ Hcred Hc'
    exact absurd rfl Hne
  have hn : 1 ≤ n ∧ n ≤ S.length + 1 := Hpure.2.1 me n HFrl'
  have hiS : i ≤ S.length + 1 := by
    have := hi.2; rcases Int.le_total n (m + 1) with h | h
    · rw [Int.max_eq_right h] at this; omega
    · rw [Int.max_eq_left h] at this; omega
  have hTn : T.lookup (me, i) = none := by
    cases h : T.lookup (me, i) with
    | none => rfl
    | some u =>
      obtain ⟨-, -, n', h1, h2⟩ := Hpure.2.2.1 me i (by show (T.lookup (me, i)).isSome = true; rw [h]; rfl)
      rw [HFrl'] at h1; cases h1; omega
  imod ghost_map_insert (me, i) () hTn $$ HT with ⟨HT, Htok⟩
  icases BigSepM.bigSepM_insert_acc (show get? Fr me = some n from HFrl) $$ HFrs with ⟨Hf', HFrsc⟩
  ihave Hfull : ghostMapElem γ.front me (DFrac.own 1) n $$ [Hfront Hf']
  · iapply (ghostMapElem_halves γ.front me n).2
    isplitl [Hfront]
    · iexact Hfront
    · iexact Hf'
  imod ghost_map_update (i + 1) $$ HFr Hfull with ⟨HFr, Hfull⟩
  icases (ghostMapElem_halves γ.front me (i + 1)).1 $$ Hfull with ⟨Hh1, Hh2⟩
  ihave HFrs := HFrsc $$ %(i + 1) Hh1
  imod monoListAuthOwn_update_app [t] $$ HS with ⟨HS, -⟩
  ihave HCrs : ([∗list] t' ∈ S ++ [t], ghostMapElem γ.cred t' (DFrac.own 1) ()) $$ [HCrs Hcred]
  · iapply BigSepL.bigSepL_snoc.2
    isplitl [HCrs]
    · iexact HCrs
    · iexact Hcred
  obtain ⟨hFrd, hFr, hT, hInitT, hTix, hCr, hNd, hSCr⟩ := Hpure
  have hNd' : (S ++ [t]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hNd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb hab => htS ?_⟩
    have hb' : b = t := by simpa using hb
    rw [← hb', ← hab]; exact ha
  have hSCr' : ∀ t' ∈ S ++ [t], (Cr !! t').isSome := by
    intro t' h; rcases List.mem_append.1 h with h | h
    · exact hSCr t' h
    · simp at h; subst h; rw [HCrl']; rfl
  have h600 := spent_le600 hTix hCr hNd' hSCr'
  simp only [List.length_append, List.length_singleton] at h600
  imod Hclose $$ [-Hh2 Htok] with -
  · inext
    iexists W, R, Fr.insert me (i + 1), T.insert (me, i) (), Tix, Cr, Rd, S ++ [t]
    iframe
    isplitr
    · ipureintro; exact HRW
    ipureintro
    refine ⟨?_, ?_, ?_, ?_, hTix, hCr, hNd', hSCr'⟩
    · intro me'
      rw [← hFrd me']
      simp only [GMap.lookup_insert_eq_iff]
      by_cases h : me = me'
      · subst h; simp [HFrl']
      · simp [h]
    · intro me' n' h1
      simp only [GMap.lookup_insert_eq_iff, List.length_append, List.length_singleton] at h1 ⊢
      by_cases h : me = me'
      · simp only [h, ite_true] at h1; cases h1; exact ⟨by omega, by push_cast; omega⟩
      · simp only [h, ite_false] at h1
        obtain ⟨h2, h3⟩ := hFr me' n' h1
        exact ⟨h2, by push_cast; omega⟩
    · intro me' i' hsome
      simp only [GMap.lookup_insert_eq_iff, List.length_append, List.length_singleton] at hsome ⊢
      by_cases h : (me, i) = (me', i')
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp only [ite_true]
        exact ⟨by omega, by push_cast; omega, _, rfl, by omega⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h)] at hsome
        obtain ⟨a1, a2, n', h1, h2⟩ := hT me' i' hsome
        refine ⟨a1, by push_cast; omega, ?_⟩
        by_cases hm : me = me'
        · subst hm; rw [HFrl'] at h1; cases h1
          exact ⟨i + 1, by simp, by omega⟩
        · exact ⟨n', by simp only [hm, ite_false]; exact h1, h2⟩
    · intro i' me' ids' lead' h
      have := hInitT i' me' ids' lead' h
      simp only [GMap.lookup_insert_eq_iff]
      split
      · rfl
      · exact this
  imodintro
  iframe
  ipureintro
  exact ⟨by omega, by omega⟩

/-- The client registers ticket `t` at frame `n` of connection `cid`, once. -/
theorem tix_register (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (t : Ticket) (cid : Nat)
    (n : Nat) (ht : t ∈ tickets) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ ticketTok γ t ={E}=∗ tixAt γ t cid n := by
  iintro #Hinv Htk
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold ticketTok tixAt
  cases hTl : Tix.lookup t with
  | some p =>
    icases BigSepM.bigSepM_lookup_acc (show get? Tix t = some p from hTl) $$ HTixs with ⟨⟨-, Htk'⟩, -⟩
    ihave %Hne := ghostMapElem_ne γ.tick t t _ () () $$ Htk Htk'
    exact absurd rfl Hne
  | none =>
    imod ghost_map_insert_persist t (cid, n) hTl $$ HTix with ⟨HTix, #Hel⟩
    obtain ⟨hFrd, hFr, hT, hInitT, hTix, hCr, hNd, hSCr⟩ := Hpure
    imod Hclose $$ [-] with -
    · inext
      iexists W, R, Fr, T, Tix.insert t (cid, n), Cr, Rd, S
      iframe
      isplitr
      · ipureintro; exact HRW
      isplitl [HTixs Htk]
      · iapply (BigSepM.bigSepM_insert (show get? Tix t = none from hTl)).2
        isplitl [Htk]
        · iframe Hel; iexact Htk
        · iexact HTixs
      ipureintro
      refine ⟨hFrd, hFr, hT, hInitT, ?_, ?_, hNd, hSCr⟩
      · intro t' h
        simp only [GMap.lookup_insert_eq_iff] at h
        by_cases e : t = t'
        · subst e; exact ht
        · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at h; exact hTix t' h
      · intro t' h
        obtain ⟨cid', n', h1, h2⟩ := hCr t' h
        have e : t ≠ t' := by
          intro e; subst e; have : Tix !! t = none := hTl; rw [this] at h1; cases h1
        exact ⟨cid', n', by simp only [GMap.lookup_insert_eq_iff, e, ite_false]; exact h1, h2⟩
    imodintro
    iexact Hel

/-- A proxy starts counting the frames it reads on a connection it accepted. -/
theorem rd_alloc [GoGlobalContext] (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E)
    (cid : Nat) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ connFresh (Gg := G) cid true ={E}=∗ rdCtr γ cid 0 := by
  iintro #Hinv Hfr
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold rdCtr
  cases hRl : Rd.lookup cid with
  | some p =>
    icases BigSepM.bigSepM_lookup_acc (show get? Rd cid = some p from hRl) $$ HRds with ⟨⟨-, Hfr'⟩, -⟩
    iexfalso
    iapply connFresh_excl cid true $$ [$Hfr $Hfr']
  | none =>
    imod ghost_map_insert cid 0 hRl $$ HRd with ⟨HRd, Hel⟩
    icases (ghostMapElem_halves γ.rd cid 0).1 $$ Hel with ⟨Hh1, Hh2⟩
    obtain ⟨hFrd, hFr, hT, hInitT, hTix, hCr, hNd, hSCr⟩ := Hpure
    imod Hclose $$ [-Hh2] with -
    · inext
      iexists W, R, Fr, T, Tix, Cr, Rd.insert cid 0, S
      iframe
      isplitr
      · ipureintro; exact HRW
      isplitl [HRds Hh1 Hfr]
      · iapply (BigSepM.bigSepM_insert (show get? Rd cid = none from hRl)).2
        isplitl [Hh1 Hfr]
        · iframe
        · iexact HRds
      ipureintro
      refine ⟨hFrd, hFr, hT, hInitT, hTix, ?_, hNd, hSCr⟩
      intro t' h
      obtain ⟨cid', n', h1, m', h2, h3⟩ := hCr t' h
      have e : cid ≠ cid' := by
        intro e; subst e; have : Rd !! cid = none := hRl; rw [this] at h2; cases h2
      exact ⟨cid', n', h1, m', by simp only [GMap.lookup_insert_eq_iff, e, ite_false]; exact h2, h3⟩
    imodintro
    iexact Hh2

/-- A proxy reading frame `n` of connection `cid`, which carries ticket `t`, mints its credit. -/
theorem credit_mint (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (t : Ticket) (cid : Nat)
    (n : Nat) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ tixAt γ t cid n -∗ rdCtr γ cid n ={E}=∗
      rdCtr γ cid (n + 1) ∗ credit γ t := by
  iintro #Hinv Htix Hrd
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold rdCtr tixAt credit
  ihave %HTl := ghost_map_lookup $$ HTix Htix
  ihave %HRl := ghost_map_lookup $$ HRd Hrd
  have HTl' : Tix !! t = some (cid, n) := HTl
  have HRl' : Rd !! cid = some n := HRl
  obtain ⟨hFrd, hFr, hT, hInitT, hTix, hCr, hNd, hSCr⟩ := Hpure
  have hCn : Cr.lookup t = none := by
    cases h : Cr.lookup t with
    | none => rfl
    | some u =>
      obtain ⟨cid', n', h1, m', h2, h3⟩ := hCr t (by show (Cr.lookup t).isSome = true; rw [h]; rfl)
      rw [HTl'] at h1; cases h1; rw [HRl'] at h2; cases h2; omega
  imod ghost_map_insert t () hCn $$ HCr with ⟨HCr, Hcred⟩
  icases BigSepM.bigSepM_insert_acc (show get? Rd cid = some n from HRl) $$ HRds with ⟨⟨Hrd', Hfr⟩, HRdsc⟩
  ihave Hfull : ghostMapElem γ.rd cid (DFrac.own 1) n $$ [Hrd Hrd']
  · iapply (ghostMapElem_halves γ.rd cid n).2
    isplitl [Hrd]
    · iexact Hrd
    · iexact Hrd'
  imod ghost_map_update (n + 1) $$ HRd Hfull with ⟨HRd, Hfull⟩
  icases (ghostMapElem_halves γ.rd cid (n + 1)).1 $$ Hfull with ⟨Hh1, Hh2⟩
  ihave HRds := HRdsc $$ %(n + 1) [Hh1 Hfr]
  · iframe
  iclear Htix
  imod Hclose $$ [-Hh2 Hcred] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr.insert t (), Rd.insert cid (n + 1), S
    iframe
    isplitr
    · ipureintro; exact HRW
    ipureintro
    refine ⟨hFrd, hFr, hT, hInitT, hTix, ?_, hNd, ?_⟩
    · intro t' h
      simp only [GMap.lookup_insert_eq_iff] at h ⊢
      by_cases e : t = t'
      · subst e; exact ⟨cid, n, HTl', n + 1, by simp, by omega⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at h
        obtain ⟨cid', n', h1, m', h2, h3⟩ := hCr t' h
        refine ⟨cid', n', h1, ?_⟩
        by_cases ec : cid = cid'
        · subst ec; rw [HRl'] at h2; cases h2; exact ⟨n + 1, by simp, by omega⟩
        · exact ⟨m', by simp only [ec, ite_false]; exact h2, h3⟩
    · intro t' h
      simp only [GMap.lookup_insert_eq_iff]
      split
      · rfl
      · exact hSCr t' h
  imodintro
  iframe

/-- A slot proxy `me` proposed is below its frontier. -/
theorem init_lt_front (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (me n i : Int)
    (ids : List GoString) (lead : Bool) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ evIn γ (.init i me ids lead) -∗ initFront γ me n ={E}=∗
      initFront γ me n ∗ ⌜i < n⌝ := by
  iintro #Hinv Ha Hf
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, HW⟩ Hclose
  unfold initFront
  ihave %hma := evIn_mem γ 1 W _ $$ Hhist Ha
  ihave %Hfr := ghost_map_lookup $$ HFr Hf
  obtain ⟨-, -, n', hn', hlt⟩ := Hpure.2.2.1 me i (Hpure.2.2.2.1 i me ids lead hma)
  have : n' = n := by
    have h2 : Fr.lookup me = some n' := hn'
    rw [Hfr] at h2; exact (Option.some.inj h2).symm
  subst this
  imod Hclose $$ [-Hf] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr, Rd, S
    iframe
    ipureintro; exact ⟨HRW, Hpure⟩
  imodintro
  iframe
  ipureintro; exact hlt

/-- A slot proxy `me` proposed has its init token spent. -/
theorem init_tok_spent (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (me i : Int)
    (ids : List GoString) (lead : Bool) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ evIn γ (.init i me ids lead) -∗ initTok γ me i ={E}=∗
      False := by
  iintro #Hinv Ha Htok
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold initTok
  ihave %hma := evIn_mem γ 1 W _ $$ Hhist Ha
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hma
  icases (BigSepL.bigSepL_lookup_acc hk).1 $$ HW with ⟨Hel, -⟩
  ieval (dsimp only) at Hel
  icases Hel with ⟨Htok', -⟩
  ihave %Hne := ghostMapElem_ne γ.inits (me, i) (me, i) _ () () $$ Htok Htok'
  exact absurd rfl Hne

/-- Every event's slot is in `[1, 600]`, and at least that many credits are spent. -/
theorem evIn_bound (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (e : Ev) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ evIn γ e ={E}=∗
      spentLb γ e.slot ∗ ⌜1 ≤ e.slot ∧ e.slot ≤ 600⌝ := by
  iintro #Hinv Ha
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, HW⟩ Hclose
  ihave %hma := evIn_mem γ 1 W _ $$ Hhist Ha
  ihave ⟨%c, #Hc, %hc⟩ := hist_reach_mem γ W _ hma $$ Hh
  obtain ⟨me, ids, lead, hin⟩ := slots_inited (conf_n_pos hc.1) hc.2 e hma
  obtain ⟨h1, h2, -⟩ := Hpure.2.2.1 me e.slot (Hpure.2.2.2.1 _ _ _ _ hin)
  have h600 := spent_le600 Hpure.2.2.2.2.1 Hpure.2.2.2.2.2.1 Hpure.2.2.2.2.2.2.1 Hpure.2.2.2.2.2.2.2
  ihave #Hlb := monoListLbOwn_get γ.spent 1 S $$ HS
  imod Hclose $$ [-] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr, Rd, S
    iframe
    ipureintro; exact ⟨HRW, Hpure⟩
  imodintro
  unfold spentLb
  isplitl
  · iexists S; iframe Hlb; ipureintro; exact h2
  · ipureintro; omega

/-- `proposeToIndex`/`proposePreviousEpochSummary`: proxy `me` of the configuration `c` proposes
slot `i` with nonempty `ids` (one summary of a permutation at a summary slot), as the slot's
leader only with the evidence, spending its token. -/
theorem cons_init (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (c : QConf) (me i : Int)
    (ids : List GoString) (lead : Bool) (hc : c.ok) (hids : ids ≠ [])
    (hsum : sumSlot c.n c.ep i → ∃ p, isPerm c.n p ∧ ids = [summaryId p]) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ initTok γ me i -∗
      (if lead then leadEv γ c i me else iprop(True)) -∗
      ([∗list] x ∈ ids, ∃ b, batchReg γ x b) ={E}=∗ evIn γ (.init i me ids lead) := by
  iintro #Hinv #Hc Htok Hlead Hreg
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  ihave %hR := hist_reach γ W c $$ Hh Hc
  ihave %hlead := leadEv_ok γ c W i me lead $$ Hhist Hlead
  unfold initTok
  ihave %HTl := ghost_map_lookup $$ HT Htok
  by_cases hfresh : ∀ ids' lead', Ev.init i me ids' lead' ∉ W
  case neg =>
    obtain ⟨ids', lead', hin⟩ : ∃ ids' lead', Ev.init i me ids' lead' ∈ W := by
      apply Classical.byContradiction; intro hn
      exact hfresh (fun ids' lead' h => hn ⟨ids', lead', h⟩)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hin
    icases (BigSepL.bigSepL_lookup_acc hk).1 $$ HW with ⟨Hel, -⟩
    ieval (dsimp only) at Hel
    icases Hel with ⟨Htok', -⟩
    ihave %Hne := ghostMapElem_ne γ.inits (me, i) (me, i) _ () () $$ Htok Htok'
    exact absurd rfl Hne
  have hsum' : sumSlot (c.n : Int) (c.ep : Int) i → ∃ p, isPerm (c.n : Int).toNat p ∧ ids = [summaryId p] := by
    intro h; obtain ⟨p, hp, he⟩ := hsum h; exact ⟨p, by simpa using hp, he⟩
  have hreach' := Reach.step W _ hR (.init i me ids lead hfresh hids hlead hsum')
  imod monoListAuthOwn_update_app [Ev.init i me ids lead] $$ Hhist with ⟨Hhist, #Hlb⟩
  have hnr : ∀ r i' s v st, Ev.init i me ids lead ≠ .record r i' s v st := by intros; simp
  iclear Hh
  imod Hclose $$ [-] with -
  · inext
    iexists W ++ [Ev.init i me ids lead], R, Fr, T, Tix, Cr, Rd, S
    iframe
    isplitr
    · iright
      iexists c
      iframe Hc
      ipureintro; exact ⟨hc, hreach'⟩
    isplitr
    · ipureintro
      exact ⟨HRW.1, fun r m h i => by rw [recState_snoc_nonrec hnr]; exact HRW.2 r m h i⟩
    isplitr
    · ipureintro
      refine ⟨Hpure.1, Hpure.2.1, Hpure.2.2.1, fun i' me' ids' lead' h => ?_, Hpure.2.2.2.2⟩
      rcases List.mem_append.1 h with h | h
      · exact Hpure.2.2.2.1 _ _ _ _ h
      · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        show (T.lookup (me', i')).isSome = true
        rw [HTl]; rfl
    iapply BigSepL.bigSepL_singleton.2
    ieval (dsimp only)
    iframe
  imodintro
  unfold evIn
  iexists W ++ [Ev.init i me ids lead]
  iframe Hlb
  ipureintro; simp

/-- A decision's ids are registered batches' (the ids some proxy proposed). -/
theorem decided_registered (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (i : Int)
    (a : List GoString) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ decided γ i a ={E}=∗ [∗list] x ∈ a, ∃ b, batchReg γ x b := by
  iintro #Hinv Ha
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold decided evIn
  icases Ha with ⟨%Wa, #Hla, %Hma⟩
  ihave %Hpa := mono_list_auth_lb_valid γ.hist 1 W Wa $$ Hhist Hla
  ihave ⟨%c, #Hc, %hc⟩ := hist_reach_mem γ W _ (Hpa.2.subset Hma) $$ Hh
  obtain ⟨me, lead, hme⟩ := (agreement (conf_n_pos hc.1) hc.2).2.2 i a (Hpa.2.subset Hma)
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hme
  icases (BigSepL.bigSepL_lookup_acc hk).1 $$ HW with ⟨Hel, HWc⟩
  ieval (dsimp only) at Hel
  icases Hel with ⟨Htok, #Hreg⟩
  ihave HW := HWc $$ %(Ev.init i me a lead) [Htok]
  · ieval (dsimp only); iframe; iexact Hreg
  have hset : W.set k (Ev.init i me a lead) = W := by
    apply List.ext_getElem?; intro n; rw [List.getElem?_set]
    split
    · rename_i h; subst h; obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hk; simp [h1, h2]
    · rfl
  rw [hset]
  imod Hclose $$ [-] with -
  · inext
    iexists W, R, Fr, T, Tix, Cr, Rd, S
    iframe
    ipureintro; exact ⟨HRW, Hpure⟩
  imodintro
  iexact Hreg

/-- Any step whose justification the caller's facts give (all but `init` and `record`, which
need the token and the recorder's half): `start`, `send`, `fast`, `slow`, `next`, `adopt`. The
caller shows that every reachable history (of the configuration `c`) containing the events it
knows allows the step. -/
theorem cons_step (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (c : QConf) (es : List Ev) (e : Ev)
    (hstep : ∀ W : World, (∀ e' ∈ es, e' ∈ W) → Step c.n c.ep W e)
    (hkind : ∀ i me ids lead, e ≠ .init i me ids lead)
    (hkind' : ∀ r i s v st, e ≠ .record r i s v st) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ ([∗list] e' ∈ es, evIn γ e') ={E}=∗
      evIn γ e := by
  iintro #Hinv #Hc Hes
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  ihave ⟨Hhist, %hes⟩ := evIns_mem γ W es $$ Hhist Hes
  icases Hh with (%hW | ⟨%c', #Hc', %hc⟩)
  · subst hW
    obtain ⟨i, me, ids, lead, he⟩ := step_nil (hstep [] hes)
    exact absurd he (hkind i me ids lead)
  ihave %he := confIs_agree γ c c' $$ Hc Hc'
  subst he
  have hreach' := Reach.step W e hc.2 (hstep W hes)
  imod monoListAuthOwn_update_app [e] $$ Hhist with ⟨Hhist, #Hlb⟩
  imod Hclose $$ [-] with -
  · inext
    iexists W ++ [e], R, Fr, T, Tix, Cr, Rd, S
    iframe
    isplitr
    · iright
      iexists c
      iframe Hc
      ipureintro; exact ⟨hc.1, hreach'⟩
    isplitr
    · ipureintro
      exact ⟨HRW.1, fun r m h i => by rw [recState_snoc_nonrec hkind']; exact HRW.2 r m h i⟩
    isplitr
    · ipureintro
      refine ⟨Hpure.1, Hpure.2.1, Hpure.2.2.1, fun i' me' ids' lead' h => ?_, Hpure.2.2.2.2⟩
      rcases List.mem_append.1 h with h | h
      · exact Hpure.2.2.2.1 _ _ _ _ h
      · simp at h; exact absurd h.symm (hkind _ _ _ _)
    iapply BigSepL.bigSepL_singleton.2
    cases e with
    | init i me ids lead => exact absurd rfl (hkind i me ids lead)
    | _ => ieval (dsimp only); itrivial
  imodintro
  unfold evIn
  iexists W ++ [e]
  iframe Hlb
  ipureintro; simp

/-- `espImpl` at recorder `r` on a sent `(i, s, v)`, under the recorder's lock (its half `m`). -/
theorem cons_record (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (r i me s : Int) (v : pure.Val)
    (m : GMap Int RecSt) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ recHalf γ r m -∗ evIn γ (.send i me s v) ={E}=∗
      recHalf γ r (m.insert i (espStep ((m !! i).getD RecSt.init) s v)) ∗
      evIn γ (.record r i s v (espStep ((m !! i).getD RecSt.init) s v)) := by
  iintro #Hinv Hhalf Hsend
  unfold consInv
  iinv Hinv with ⟨%W, %R, %Fr, %T, %Tix, %Cr, %Rd, %S, >Hhist, >Hh, >HR, >HRs, >%HRW, >HFr, >HFrs,
    >HT, >HTix, >HTixs, >HCr, >HCrs, >HRd, >HRds, >HS, >%Hpure, >HW⟩ Hclose
  unfold recHalf
  ihave %HRl := ghost_map_lookup $$ HR Hhalf
  ihave %hsend := evIn_mem γ 1 W _ $$ Hhist Hsend
  ihave ⟨%c, #Hc, %hc⟩ := hist_reach_mem γ W _ hsend $$ Hh
  have hrs : ∀ i, recState W r i = (m !! i).getD RecSt.init := HRW.2 r m HRl
  generalize hst : espStep ((m !! i).getD RecSt.init) s v = st'
  have hstep : Step (c.n : Int) (c.ep : Int) W (.record r i s v st') := by
    have := Step.record (n := (c.n : Int)) (e := (c.ep : Int)) r i me s v hsend
    rwa [hrs i, hst] at this
  have hreach' := Reach.step _ _ hc.2 hstep
  imod monoListAuthOwn_update_app [Ev.record r i s v st'] $$ Hhist with ⟨Hhist, #Hlb⟩
  icases BigSepM.bigSepM_insert_acc (show get? R r = some m from HRl) $$ HRs with ⟨Hhalf', HRsc⟩
  ihave Hfull : ghostMapElem γ.recs r (DFrac.own 1) m $$ [Hhalf Hhalf']
  · iapply (ghostMapElem_halves γ.recs r m).2
    isplitl [Hhalf]
    · iexact Hhalf
    · iexact Hhalf'
  imod ghost_map_update (m.insert i st') $$ HR Hfull with ⟨HR, Hfull⟩
  icases (ghostMapElem_halves γ.recs r (m.insert i st')).1 $$ Hfull with ⟨Hh1, Hh2⟩
  ihave HRs := HRsc $$ %(m.insert i st') Hh1
  imod Hclose $$ [-Hh2] with -
  · inext
    iexists W ++ [Ev.record r i s v st'], R.insert r (m.insert i st'), Fr, T, Tix, Cr, Rd, S
    iframe
    isplitr
    · iright
      iexists c
      iframe Hc
      ipureintro; exact ⟨hc.1, hreach'⟩
    isplitr
    · ipureintro
      refine ⟨fun r' => ?_, fun r' m' h1 i' => ?_⟩
      · rw [← HRW.1 r']
        by_cases hrr : r = r'
        · subst hrr; simp [HRl]
        · rw [GMap.lookup_insert_ne _ _ hrr]
      by_cases hrr : r = r'
      · subst hrr
        rw [GMap.lookup_insert] at h1; cases h1
        rw [recState_snoc]
        simp only [true_and]
        by_cases hii : i = i'
        · subst hii; simp
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hii), hrs i', GMap.lookup_insert_ne _ _ hii]; rfl
      · rw [GMap.lookup_insert_ne _ _ hrr] at h1
        rw [recState_snoc]; simp only [hrr, false_and, ite_false]; exact HRW.2 r' m' h1 i'
    isplitr
    · ipureintro
      refine ⟨Hpure.1, Hpure.2.1, Hpure.2.2.1, fun i' me' ids' lead' h => ?_, Hpure.2.2.2.2⟩
      rcases List.mem_append.1 h with h | h
      · exact Hpure.2.2.2.1 _ _ _ _ h
      · simp at h
    iapply BigSepL.bigSepL_singleton.2
    ieval (dsimp only); itrivial
  imodintro
  simp only [Option.getD] at hst
  ieval (simp only [hst])
  isplitl [Hh2]
  · iexact Hh2
  unfold evIn
  iexists W ++ [Ev.record r i s v st']
  iframe Hlb
  ipureintro; simp

end laws

end Perennial.raxos
