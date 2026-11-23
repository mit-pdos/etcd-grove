/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/LearnerProof.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The learner (`leaner.go`): `newLearner` and `learner.learn`, over the transport's `recv` spec
(hypothesis) and the Paxos hub's laws (package accept-learn).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.MsgMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]

set_option goose.wp.extras true

local notation "pkg" => pkg_id.github_com.xiang90.paxos

theorem lrnEntries_init (Γ : Names) (M : GMap w64 GoInterface)
    (h : ∀ k x, M !! k = some x → x = AccLrn.lrnInit) :
    ⊢ [∗map] a ↦ x ∈ M, lrnEntry (GF := GF) Γ a x := by
  refine BigSepM.bigSepM_intro (P := iprop(emp)) ?_
  intro k x hx
  rw [h k x hx]
  unfold lrnEntry
  iintro -
  iexists _
  isplitl
  · ipureintro
    refine ⟨rfl, rfl, ?_⟩
    change (([] : GoString).length : Int) < 2 ^ 48
    simp
  · ileft; ipureintro; rfl

theorem newLearner.wp_proof : newLearner.spec (GF := GF) (hG := hG) :=
  fun Γ id nt nd amap ids asl hid => by
  wp_start as ⟨Henv, #Has⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %am Hm
  ihave %Hlen := ownSlice_len _ _ _ $$ Has
  ihave HI : (∃ (i : w64) (M : GMap w64 GoInterface), "i" ∷ i_ptr ↦ i ∗ "a" ∷ (∃ x : w64, a_ptr ↦ x) ∗
      "Hm" ∷ am ↦$ M ∗
      "%Hi0" ∷ ⌜0 ≤ sint.Z i⌝ ∗ "%Hi" ∷ ⌜sint.Z i ≤ sint.Z asl.len ∧
        (∀ k, (M !! k).isSome ↔ k ∈ accIds.take (sint.nat i)) ∧
        ∀ k x, M !! k = some x → x = AccLrn.lrnInit⌝ : IProp GF) $$ [i a Hm]
  · iexists W64 0, ∅
    iframe
    isplitl
    · iexists _; iexact a
    · isplitr
      · ipureintro; word
      ipureintro; refine ⟨by word, ?_, ?_⟩
      · intro k; simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero]; simp
      · intro k x h; simp at h
  wp_for HI
  wp_if_destruct
  · list_elem accIds (sint.nat i) as ak
    simp only [Hi0, Hif, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index asl (sint.Z i) accIds _ ak Hi0 $$ [$Has] as -
    · ipureintro; exact Hak_lookup
    icases a with ⟨%x, a⟩
    wp_auto
    wp_apply (wp_mapInsert go.int am M ak _) $$ [$Hm] as Hm
    wp_for_post
    iframe
    iexists i + W64 1, _
    iframe
    isplitl
    · iexists _; iexact a
    · isplitr
      · ipureintro; word
      ipureintro
      have hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      refine ⟨by word, ?_, ?_⟩
      · intro k
        rw [hsucc, List.take_add_one, Hak_lookup, GMap.lookup_insert_eq_iff]
        by_cases h : ak = k
        · subst h; simp
        · simp only [h, ↓reduceIte, Hi.2.1 k]; simp [Ne.symm h]
      · intro k y hy
        by_cases h : ak = k
        · simp [h] at hy; subst hy; rfl
        · simp [h] at hy; exact Hi.2.2 k y hy
  have hfull : sint.nat i = accIds.length := by rw [Hlen.1]; word
  rw [hfull, List.take_length] at Hi
  iStructNamed «$r0»
  iapply HΦ
  unfold own_learner
  iexists nt, nd, amap, ids, am, M
  iframe
  isplitr
  · ipureintro; exact hid
  isplitr
  · ipureintro; exact Hi.2.1
  iapply lrnEntries_init Γ M Hi.2.2


instance lrnEntry_persistent (Γ : Names) (a : w64) (x : GoInterface) :
    Persistent (lrnEntry (GF := GF) Γ a x) := by
  unfold lrnEntry; infer_instance

theorem lrnEntry_unfold (Γ : Names) (a : w64) (x : GoInterface) :
    lrnEntry (GF := GF) Γ a x ⊣⊢ ∃ m : message, ⌜x = interface.mkOk message.ty #m ∧
      m.typ' = W64 4 ∧ msgWf m⌝ ∗ (⌜m.n' = W64 0⌝ ∨ (⌜m.from' = a⌝ ∗ accW Γ a m.n' m.value')) := by
  unfold lrnEntry; exact .rfl

/-- `l.receiveAccepted(accepted)`: the learner's view of `accepted.from` moves to `accepted` if
its number is higher. -/
theorem wp_receiveAccepted (Γ : Names) (lp : Loc) (id : w64) (am : Loc)
    (M : GMap w64 GoInterface) (accepted : message)
    (hdom : ∀ a, (M !! a).isSome ↔ a ∈ accIds) (hfrom : accepted.from' ∈ accIds)
    (htyp : accepted.typ' = W64 4) (hwf : msgWf accepted) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ lp.[learner, go!"id"] ↦ id ∗
      lp.[learner, go!"acceptors"] ↦ am ∗ am ↦$ M ∗ ([∗map] a ↦ x ∈ M, lrnEntry Γ a x) ∗
      accW Γ accepted.from' accepted.n' accepted.value' }}
    (App (Val (lp @!! go.GoType.PointerType learner.ty @!! go!"receiveAccepted")) (Val #accepted))
  {{ RET #(); ∃ M' : GMap w64 GoInterface, lp.[learner, go!"id"] ↦ id ∗
      lp.[learner, go!"acceptors"] ↦ am ∗ am ↦$ M' ∗ ⌜∀ a, (M' !! a).isSome ↔ a ∈ accIds⌝ ∗
      [∗map] a ↦ x ∈ M', lrnEntry Γ a x }} := by
  wp_start as ⟨Hid, Hacc, Hm, #HM, #Hw⟩
  wp_auto
  wp_apply (wp_map_lookup1 go.int accept.ty am M accepted.from') $$ [$Hm] as Hm
  obtain ⟨iv, hiv⟩ : ∃ iv, M !! accepted.from' = some iv := by
    have := (hdom accepted.from').2 hfrom
    exact Option.isSome_iff_exists.mp this
  ihave He := BigSepM.bigSepM_lookup hiv $$ HM
  icases (lrnEntry_unfold Γ _ iv).1 $$ He with ⟨%m, %Hmv, #Hor⟩
  obtain ⟨rfl, Hmt, Hmwf⟩ := Hmv
  rw [hiv]
  wp_auto
  wp_apply AccLrn.wp_proposalNumber m Hmt
  wp_if_destruct
  · wp_apply AccLrn.wp_ints2
    iintro %sl Hargs
    wp_auto
    wp_apply log.wp_Printf _ _ _ _ (AccLrn.intArgs_wf _) $$ [$Hargs] as -
    wp_apply (wp_mapInsert go.int am M accepted.from' _) $$ [$Hm] as Hm
    iapply HΦ
    iexists _
    iframe
    isplitr
    · ipureintro
      intro a
      by_cases h : accepted.from' = a
      · subst h; simp [hfrom]
      · simp only [GMap.lookup_insert_eq_iff, h, ↓reduceIte]; exact hdom a
    icases BigSepM.bigSepM_insert_acc hiv $$ HM with ⟨-, Hins⟩
    iapply Hins
    iapply (lrnEntry_unfold Γ _ _).2
    iexists accepted
    isplitl []
    · ipureintro; exact ⟨rfl, htyp, hwf⟩
    · iright
      isplitl []
      · ipureintro; rfl
      · iexact Hw
  · wp_end
    iexists M
    iframe
    isplitr
    · ipureintro; exact hdom
    · iexact HM


theorem accIds_size (M : GMap w64 GoInterface) (hdom : ∀ a, (M !! a).isSome ↔ a ∈ accIds) :
    GMap.size M = 3 :=
  GMap.size_eq_length M accIds (by decide) (fun k => (hdom k).symm)

/-- `l.majority()`: two, for the three acceptors. -/
theorem wp_majority (lp am : Loc) (M : GMap w64 GoInterface)
    (hdom : ∀ a, (M !! a).isSome ↔ a ∈ accIds) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ lp.[learner, go!"acceptors"] ↦ am ∗ am ↦$ M }}
    (App (Val (lp @!! go.GoType.PointerType learner.ty @!! go!"majority")) (Val #()))
  {{ RET #(W64 2); lp.[learner, go!"acceptors"] ↦ am ∗ am ↦$ M }} := by
  wp_start as ⟨Hacc, Hm⟩
  wp_auto
  wp_apply (wp_map_len am M) $$ [$Hm] as Hm
  rw [accIds_size M hdom]
  rw [show BitVec.sdiv (W64 ((3 : Nat) : Int)) (W64 2) + W64 1 = W64 2 from by decide]
  wp_end


theorem forMap_exec (P : IProp GF) (Φ : val → IProp GF) :
    P ⊢ forMapPostcondition P Φ executeVal := by
  iintro HP
  unfold forMapPostcondition
  iright; ileft
  isplitr
  · ipureintro; rfl
  · iexact HP

/-- `chosen()`'s counting invariant: each counted number `n` has its latest entry `x` in
`accepteds`, from an acceptor counted already (in `done`) that accepted `(n, x.value)`; a count
other than one has a second, distinct acceptor that accepted `n`. -/
def chInv (Γ : Names) (done : List w64) (C : GMap w64 w64) (A : GMap w64 GoInterface) : IProp GF :=
  iprop(□ ∀ n c, ⌜C !! n = some c⌝ → ∃ x : message,
    ⌜A !! n = some (interface.mkOk message.ty #x) ∧ x.typ' = W64 4 ∧ msgWf x ∧ x.from' ∈ done ∧
      x.from' ∈ accIds⌝ ∗ accW Γ x.from' n x.value' ∗
    (⌜c = W64 1⌝ ∨ ∃ b v', ⌜b ∈ accIds ∧ b ≠ x.from'⌝ ∗ accW Γ b n v'))

instance chInv_persistent (Γ : Names) done C A : Persistent (chInv (GF := GF) Γ done C A) := by
  unfold chInv; infer_instance

theorem not_mem_take_nodup {α : Type} (l : List α) (h : l.Nodup) (j : Nat) (a : α)
    (hj : l[j]? = some a) : a ∉ l.take j := by
  intro hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
  rw [List.getElem?_take] at hi
  split at hi
  · have := list_nodup_getElem?_inj l h i j a hi hj; omega
  · simp at hi

theorem mem_take_succ {α : Type} (l : List α) (j : Nat) (a : α) (hj : l[j]? = some a) :
    a ∈ l.take (j + 1) := by
  rw [List.take_add_one, hj]; simp

theorem mem_take_mono {α : Type} {l : List α} {a b : Nat} (h : a ≤ b) {x : α}
    (hx : x ∈ l.take a) : x ∈ l.take b := by
  have : l.take a = (l.take b).take a := by rw [List.take_take, Nat.min_eq_left h]
  rw [this] at hx; exact List.mem_of_mem_take hx

theorem chInv_mono (Γ : Names) (done done' : List w64) C A (h : ∀ x, x ∈ done → x ∈ done') :
    chInv (GF := GF) Γ done C A ⊢ chInv Γ done' C A := by
  unfold chInv
  iintro #H
  imodintro
  iintro %n %c %Hc
  icases H $$ %n %c %Hc with ⟨%x, %Hx, #Hw, #Hor⟩
  iexists x
  isplitl []
  · ipureintro; exact ⟨Hx.1, Hx.2.1, Hx.2.2.1, h _ Hx.2.2.2.1, Hx.2.2.2.2⟩
  isplitl []
  · iexact Hw
  · iexact Hor

/-- Counting acceptor `key`'s entry `m`, of number `m.n' ≠ 0`. -/
theorem chInv_step (Γ : Names) (done done' : List w64) C A (key : w64) (m : message)
    (hmono : ∀ x, x ∈ done → x ∈ done') (hnot : key ∉ done) (hin : key ∈ done')
    (hkey : key ∈ accIds) (hfrom : m.from' = key) (htyp : m.typ' = W64 4) (hwf : msgWf m) :
    chInv (GF := GF) Γ done C A ⊢ accW Γ key m.n' m.value' -∗
      chInv Γ done' (<[m.n' := (C !! m.n').getD (zero_val w64) + W64 1]> C)
        (<[m.n' := interface.mkOk message.ty #m]> A) := by
  unfold chInv
  iintro #H #Hw
  imodintro
  iintro %n %c %Hc
  by_cases hn : m.n' = n
  · subst hn
    simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.some.injEq] at Hc
    iexists m
    isplitl []
    · ipureintro
      simp only [GMap.lookup_insert_eq_iff, ↓reduceIte]
      exact ⟨trivial, htyp, hwf, hfrom ▸ hin, hfrom ▸ hkey⟩
    isplitl []
    · rw [hfrom]; iexact Hw
    · cases hC : C !! m.n' with
      | none =>
        ileft; ipureintro; rw [← Hc, hC]; rfl
      | some c0 =>
        iright
        icases H $$ %m.n' %c0 %hC with ⟨%x, %Hx, #Hw', -⟩
        iexists x.from', x.value'
        isplitl []
        · ipureintro
          refine ⟨Hx.2.2.2.2, ?_⟩
          rw [hfrom]; intro he; exact hnot (he ▸ Hx.2.2.2.1)
        · iexact Hw'
  · simp only [GMap.lookup_insert_eq_iff, hn, ↓reduceIte] at Hc
    icases H $$ %n %c %Hc with ⟨%x, %Hx, #Hw', #Hor⟩
    iexists x
    isplitl []
    · ipureintro
      simp only [GMap.lookup_insert_eq_iff, hn, ↓reduceIte]
      exact ⟨Hx.1, Hx.2.1, Hx.2.2.1, hmono _ Hx.2.2.2.1, Hx.2.2.2.2⟩
    isplitl []
    · iexact Hw'
    · iexact Hor

/-- `l.chosen()`'s result: a learner entry chosen by a majority. -/
def chosenRes (Γ : Names) (r : GoInterface) (ok : Bool) : IProp GF :=
  if ok then iprop(∃ x : message, ⌜r = interface.mkOk message.ty #x ∧ x.typ' = W64 4 ∧ msgWf x⌝ ∗
    chosenW Γ x.value') else iprop(True)

/-- `l.chosen()`: a proposal accepted by two distinct acceptors (as the learner's view says),
whose value is therefore chosen. -/
theorem wp_chosen (Γ : Names) (lp am : Loc) (M : GMap w64 GoInterface)
    (hdom : ∀ a, (M !! a).isSome ↔ a ∈ accIds) :
  {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ lp.[learner, go!"acceptors"] ↦ am ∗
      am ↦$ M ∗ ([∗map] a ↦ x ∈ M, lrnEntry Γ a x) }}
    (App (Val (lp @!! go.GoType.PointerType learner.ty @!! go!"chosen")) (Val #()))
  {{ (r : GoInterface) (ok : Bool), RET (PairV #r #ok); lp.[learner, go!"acceptors"] ↦ am ∗
      am ↦$ M ∗ chosenRes Γ r ok }} := by
  wp_start as ⟨#Hinv, Hacc, Hm, #HM⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %cm Hcm
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %amp Hamp
  wp_apply (wp_map_for_range (K := w64) (V := GoInterface)
    (fun keys i => iprop(∃ (C : GMap w64 w64) (A : GMap w64 GoInterface) (v : GoInterface),
      "counts" ∷ counts_ptr ↦ cm ∗ "Hcm" ∷ cm ↦$ C ∗ "accepteds" ∷ accepteds_ptr ↦ amp ∗
      "Hamp" ∷ amp ↦$ A ∗ "accepted" ∷ accepted_ptr ↦ v ∗ "#HC" ∷ chInv Γ (keys.take i.toNat) C A ∗
      "%Hi0" ∷ ⌜0 ≤ i⌝))
    _ go.int accept.ty am M (DFrac.own 1)) $$ [$Hm]
  iintro %keys %Hkeys
  obtain ⟨Hkmem, Hklen, Hknd⟩ := Hkeys
  isplitl [Hcm counts Hamp accepteds accepted]
  · iexists ∅, ∅, _
    iframe
    isplitl
    · unfold chInv
      imodintro
      iintro %n %c %Hc
      simp at Hc
    · ipureintro; omega
  isplitr
  · imodintro
    iintro %i %key %iv ⟨%Hkey, %Hv⟩ Hp
    iNamed Hp
    ihave He := BigSepM.bigSepM_lookup Hv $$ HM
    icases (lrnEntry_unfold Γ _ iv).1 $$ He with ⟨%m, %Hmv, #Hor⟩
    obtain ⟨rfl, Hmt, Hmwf⟩ := Hmv
    wp_auto
    wp_apply AccLrn.wp_proposalNumber m Hmt
    have hkey : key ∈ accIds := (hdom key).1 ((Hkmem key).1 (List.mem_of_getElem? Hkey))
    have hdone : ∀ x, x ∈ keys.take i.toNat → x ∈ keys.take (i + 1).toNat :=
      fun x hx => mem_take_mono (by omega) hx
    wp_if_destruct
    · iapply forMap_exec
      iexists C, A, _
      iframe
      isplitl
      · iapply chInv_mono Γ _ _ C A hdone $$ HC
      · ipureintro; omega
    · icases Hor with (%Hn0 | ⟨%Hfrom, #Hw⟩)
      · exact absurd Hn0 Hif
      wp_apply AccLrn.wp_proposalNumber m Hmt
      wp_apply (wp_map_lookup1 go.int go.int cm C m.n') $$ [$Hcm] as Hcm
      wp_apply AccLrn.wp_proposalNumber m Hmt
      wp_apply (wp_mapInsert go.int cm C m.n' _) $$ [$Hcm] as Hcm
      wp_apply AccLrn.wp_proposalNumber m Hmt
      wp_apply (wp_mapInsert go.int amp A m.n' _) $$ [$Hamp] as Hamp
      iapply forMap_exec
      iexists _, _, _
      iframe
      isplitl
      · have hin : key ∈ keys.take (i + 1).toNat := by
          rw [show (i + 1).toNat = i.toNat + 1 by omega]; exact mem_take_succ keys _ key Hkey
        iapply (chInv_step Γ _ _ C A key m hdone (not_mem_take_nodup keys Hknd _ key Hkey) hin
          hkey Hfrom Hmt Hmwf) $$ HC Hw
      · ipureintro; omega
  iintro Hp Hm
  iNamed Hp
  wp_auto
  wp_apply (wp_map_for_range (K := w64) (V := w64)
    (fun _ _ => iprop(∃ (cv nv : w64),
      "count" ∷ count_ptr ↦ cv ∗ "n" ∷ n_ptr ↦ nv ∗ "l" ∷ l_ptr ↦ lp ∗
      "Hacc" ∷ lp.[learner, go!"acceptors"] ↦ am ∗ "Hm" ∷ am ↦$ M ∗
      "accepteds" ∷ accepteds_ptr ↦ amp ∗ "Hamp" ∷ amp ↦$ A ∗
      "«$res0»" ∷ «$res0_ptr» ↦ GoInterface.nil ∗ "«$res1»" ∷ «$res1_ptr» ↦ zero_val Bool ∗
      "HΦ" ∷ (∀ (r : GoInterface) (ok : Bool), lp.[learner, go!"acceptors"] ↦ am ∗ am ↦$ M ∗
        chosenRes Γ r ok -∗ Φ (PairV #r #ok))))
    _ go.int go.int cm C (DFrac.own 1)) $$ [$Hcm]
  iintro %keys2 %Hkeys2
  isplitl [count n l Hacc Hm accepteds Hamp «$res0» «$res1» HΦ]
  · iexists _, _
    iframe
  isplitr
  · imodintro
    iintro %j %nk %c ⟨%Hnk, %Hc⟩ Hp
    iNamed Hp
    wp_auto
    wp_apply (wp_majority lp am M hdom) $$ [$Hacc $Hm] as ⟨Hacc, Hm⟩
    wp_if_destruct
    · unfold chInv
      icases HC $$ %nk %c %Hc with ⟨%x, %Hx, #Hw1, #Hor⟩
      icases Hor with (%Hc1 | ⟨%b, %v', %Hb, #Hw2⟩)
      · exfalso; rw [Hc1] at Hif; exact absurd Hif (by decide)
      ihave Hag := inv_acc_agree Γ ⊤ x.from' b nk x.value' v' (by solve_ndisj) $$ Hinv
      iapply fupd_wp
      imod Hag $$ Hw1 Hw2 with %Hvv
      imodintro
      subst Hvv
      wp_apply (wp_map_lookup1 go.int accept.ty amp A nk) $$ [$Hamp] as Hamp
      rw [Hx.1]
      unfold forMapPostcondition
      iright; iright; iright; ileft
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hcm
      wp_auto
      iapply HΦ
      iframe
      unfold chosenRes
      simp only [↓reduceIte]
      iexists x
      isplitl []
      · ipureintro; exact ⟨rfl, Hx.2.1, Hx.2.2.1⟩
      unfold chosenW
      iexists nk, x.from', b
      isplitl []
      · ipureintro; exact ⟨Hx.2.2.2.2, Hb.1, fun h => Hb.2 h.symm⟩
      isplitl []
      · iexact Hw1
      · iexact Hw2
    · iapply forMap_exec
      iexists _, _
      iframe
  · iintro Hp Hcm
    iNamed Hp
    wp_auto
    iapply HΦ
    iframe
    unfold chosenRes
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial


theorem learner.learn.wp_proof (wp_recv : tcpNetwork.recv.spec (GF := GF) (hG := hG)) :
    learner.learn.spec (GF := GF) (hG := hG) := fun Γ lp id => by
  wp_start as Hown
  unfold own_learner
  icases Hown with ⟨%nt, %nd, %amap, %ids, %am, %M, Henv, %hid, Hid, Hacc, Hnt, Hm, %hdom, HM⟩
  unfold agentEnv
  icases Henv with ⟨#Hinv, #Hnode, Hnet, %hids⟩
  wp_auto
  ihave HI : (∃ M : GMap w64 GoInterface, "Hm" ∷ am ↦$ M ∗
      "%hdom" ∷ ⌜∀ a, (M !! a).isSome ↔ a ∈ accIds⌝ ∗
      "HM" ∷ [∗map] a ↦ x ∈ M, lrnEntry Γ a x : IProp GF) $$ [Hm HM]
  · iexists M; iframe; ipureintro; exact hdom
  wp_for HI
  wp_apply (wp_recv (msgOK Γ) nt nd amap ids id _ hids) $$ [$Hnode $Hnet] as %m %ok ⟨Hnet, Hmsg⟩
  cases ok
  · wp_auto
    wp_for_post
    iframe
    iexists M
    iframe
    ipureintro; exact hdom
  simp only [↓reduceIte]
  unfold inboxP
  icases Hmsg with ⟨Hok, %Hto, %Hwf⟩
  ihave Hok := (AccLrn.msgOK_lrn Γ m (Hto ▸ hid)).1 $$ Hok
  icases Hok with ⟨%Htf, #Hw⟩
  wp_auto
  wp_if_destruct
  · wp_apply (wp_receiveAccepted Γ lp id am M m hdom Htf.2 Htf.1 Hwf) $$ [$Hid $Hacc $Hm $HM $Hw]
      as ⟨%M', Hid, Hacc, Hm, %hdom', #HM'⟩
    wp_apply (wp_chosen Γ lp am M' hdom') $$ [$Hinv $Hacc $Hm $HM'] as %r %cok ⟨Hacc, Hm, Hres⟩
    cases cok
    · wp_auto
      wp_for_post
      iframe
      iexists M'
      iframe
      isplitr
      · ipureintro; exact hdom'
      · iexact HM'
    unfold chosenRes
    simp only [↓reduceIte]
    icases Hres with ⟨%x, %Hx, #Hch⟩
    obtain ⟨rfl, Hxt, Hxwf⟩ := Hx
    wp_auto
    wp_apply AccLrn.wp_proposalNumber x Hxt
    wp_apply AccLrn.wp_ints2
    iintro %sl Hargs
    wp_auto
    wp_apply log.wp_Printf _ _ _ _ (AccLrn.intArgs_wf _) $$ [$Hargs] as -
    wp_apply AccLrn.wp_proposalValue x Hxt
    wp_for_post
    iapply HΦ
    isplitl [Hnt Hnet Hid Hacc Hm]
    · iexists nt, nd, amap, ids, am, M'
      isplitl [Hnet]
      · isplitr
        · iexact Hinv
        isplitr
        · iexact Hnode
        isplitl
        · iexact Hnet
        · ipureintro; exact hids
      isplitr
      · ipureintro; exact hid
      iframe
      isplitr
      · ipureintro; exact hdom'
      · iexact HM'
    isplitl []
    · iexact Hch
    · ipureintro; exact Hxwf
  · exfalso; exact Hif Htf.1

end proofs