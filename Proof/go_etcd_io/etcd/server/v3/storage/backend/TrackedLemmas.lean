/-
**The tracked buckets by bucket set: the laws** (decision 3, option (b), of
`notes/backend-auth-split-plan.md`). The client's part of the tracked buckets of a set `S`
(`rbPart`), its idle part (`rbOwnIn`), the whole (`rbOwn = rbPart ⊤`) and the batch lock's side
(`rbSide`) are halves of one ghost map's elements, a bucket's contents and pending flag
(`InvBackend.lean`, `rbElem`). The laws: split and join over disjoint sets, congruence, agreement
of two parts, and the two ghost steps the proved operations take: a session's write to one bucket
(contents updated, flag set: `rbSide_put`) and `Unlock`'s (flags of the part handed in cleared:
`rbSide_idle`, used only by `batchTxBuffered.Unlock`'s proof).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section tracked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

open Classical

/-! ### Pointwise -/

private theorem ite_or_split {A B C : Prop} {_ : Decidable A} {_ : Decidable B} {_ : Decidable C}
    (hc : C ↔ A ∨ B) (X : IProp GF) (hd : A → B → False) :
    (if C then X else iprop(True)) ⊣⊢
      iprop((if A then X else iprop(True)) ∗ (if B then X else iprop(True))) := by
  by_cases ha : A
  · have hb : ¬ B := fun hb => hd ha hb
    simp only [if_pos (hc.2 (Or.inl ha)), if_pos ha, if_neg hb]
    exact ⟨by iintro H; isplitl [H]; iexact H; itrivial, by iintro ⟨H, -⟩; iexact H⟩
  · by_cases hb : B
    · simp only [if_pos (hc.2 (Or.inr hb)), if_neg ha, if_pos hb]
      exact ⟨by iintro H; isplitr; itrivial; iexact H, by iintro ⟨-, H⟩; iexact H⟩
    · have hnc : ¬ C := fun h => (hc.1 h).elim ha hb
      simp only [if_neg hnc, if_neg ha, if_neg hb]
      exact ⟨by iintro -; isplitl; itrivial; itrivial, by iintro -; itrivial⟩

private theorem lookup_ne_of_get {D : GMap GoString Unit} {k : GoString} {x : Unit}
    (hk : Std.PartialMap.get? D k = some x) : D.lookup k ≠ none := by
  intro h0
  have h1 : D.lookup k = some x := hk
  rw [h0] at h1
  cases h1

/-! ### The elements -/

/-- The elements of disjoint bucket sets are those of their union. -/
theorem rbEls_split (γ : BNames) (S S' : GoString → Prop) (q : Qp)
    (v : GoString → Option BktData × Bool) (hd : ∀ n, S n → S' n → False) :
    rbEls (GF := GF) γ (fun n => S n ∨ S' n) q v ⊣⊢ iprop(rbEls γ S q v ∗ rbEls γ S' q v) := by
  unfold rbEls
  constructor
  · refine (BigSepM.bigSepM_mono fun {k} {_} _ =>
      (ite_or_split (A := S k) (B := S' k) Iff.rfl (rbElem (GF := GF) γ k q (v k)) (hd k)).1).trans
      (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
  · refine (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
      (BigSepM.bigSepM_mono fun {k} {_} _ =>
        (ite_or_split (A := S k) (B := S' k) Iff.rfl (rbElem (GF := GF) γ k q (v k)) (hd k)).2)

/-- Congruence: only the values at the set's tracked buckets matter. -/
theorem rbEls_congr (γ : BNames) (S : GoString → Prop) (q : Qp)
    (v v' : GoString → Option BktData × Bool)
    (h : ∀ n, S n → γ.rbD.lookup n ≠ none → v n = v' n) :
    rbEls (GF := GF) γ S q v ⊣⊢ rbEls γ S q v' := by
  unfold rbEls
  constructor
  · refine BigSepM.bigSepM_mono fun {k} {_} hk => ?_
    by_cases hS : S k
    · simp only [if_pos hS, h k hS (lookup_ne_of_get hk)]; exact .rfl
    · simp only [if_neg hS]; exact .rfl
  · refine BigSepM.bigSepM_mono fun {k} {_} hk => ?_
    by_cases hS : S k
    · simp only [if_pos hS, h k hS (lookup_ne_of_get hk)]; exact .rfl
    · simp only [if_neg hS]; exact .rfl

/-- Two halves of the elements are the whole. -/
theorem rbEls_halves (γ : BNames) (S : GoString → Prop) (v : GoString → Option BktData × Bool) :
    iprop(rbEls (GF := GF) γ S (1 : Qp).half v ∗ rbEls γ S (1 : Qp).half v) ⊣⊢ rbEls γ S 1 v := by
  unfold rbEls
  constructor
  · refine (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
      (BigSepM.bigSepM_mono fun {k} {_} _ => ?_)
    by_cases hS : S k
    · simp only [if_pos hS]; exact (ghostMapElem_halves γ.rbk k (v k)).2
    · simp only [if_neg hS]; iintro -; itrivial
  · refine (BigSepM.bigSepM_mono fun {k} {_} _ => ?_).trans
      (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
    by_cases hS : S k
    · simp only [if_pos hS]; exact (ghostMapElem_halves γ.rbk k (v k)).1
    · simp only [if_neg hS]; iintro -; isplitl; itrivial; itrivial

/-- Two elements of one bucket agree. -/
theorem rbEls_agree1 (γ : BNames) (S S' : GoString → Prop) (q q' : Qp)
    (v v' : GoString → Option BktData × Bool) (n : GoString) (hS : S n) (hS' : S' n)
    (hn : γ.rbD.lookup n ≠ none) :
    iprop(rbEls (GF := GF) γ S q v ∗ rbEls γ S' q' v') ⊢ ⌜v n = v' n⌝ := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hn
  unfold rbEls
  iintro ⟨H1, H2⟩
  icases (BigSepM.bigSepM_lookup_acc
    (Φ := fun k (_ : Unit) => if S k then rbElem (GF := GF) γ k q (v k) else iprop(True))
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ H1 with ⟨H1, -⟩
  icases (BigSepM.bigSepM_lookup_acc
    (Φ := fun k (_ : Unit) => if S' k then rbElem (GF := GF) γ k q' (v' k) else iprop(True))
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ H2 with ⟨H2, -⟩
  ihave H1 := (show (if S n then rbElem (GF := GF) γ n q (v n) else iprop(True)) ⊢
    rbElem γ n q (v n) by simp only [if_pos hS]; exact .rfl) $$ H1
  ihave H2 := (show (if S' n then rbElem (GF := GF) γ n q' (v' n) else iprop(True)) ⊢
    rbElem γ n q' (v' n) by simp only [if_pos hS']; exact .rfl) $$ H2
  iapply ghostMapElem_agree n γ.rbk (DFrac.own q) (DFrac.own q') (v n) (v' n) $$ H1 H2

/-- Two families of elements agree where both have the bucket. -/
theorem rbEls_agree (γ : BNames) (S S' : GoString → Prop) (q q' : Qp)
    (v v' : GoString → Option BktData × Bool) :
    iprop(rbEls (GF := GF) γ S q v ∗ rbEls γ S' q' v') ⊢
      iprop(rbEls γ S q v ∗ rbEls γ S' q' v' ∗
        ⌜∀ n, S n → S' n → γ.rbD.lookup n ≠ none → v n = v' n⌝) := by
  by_cases hall : ∀ n, S n → S' n → γ.rbD.lookup n ≠ none → v n = v' n
  · iintro ⟨H1, H2⟩
    isplitl [H1]; iexact H1
    isplitl [H2]; iexact H2
    ipureintro; exact hall
  · obtain ⟨n, hrest⟩ := Classical.not_forall.mp hall
    have hS : S n := Classical.byContradiction fun h => hrest fun h' => absurd h' h
    have hS' : S' n := Classical.byContradiction fun h => hrest fun _ h' => absurd h' h
    have hn : γ.rbD.lookup n ≠ none :=
      Classical.byContradiction fun h => hrest fun _ _ h' => absurd h' h
    have hne : v n ≠ v' n := fun he => hrest fun _ _ _ => he
    iintro H
    ihave %h := rbEls_agree1 γ S S' q q' v v' n hS hS' hn $$ H
    exact absurd h hne

/-- The whole elements, updated to any values (the ghost map's authority with them). -/
private theorem els_update (g : GName) (S : GoString → Prop) (D : GMap GoString Unit)
    (v w : GoString → Option BktData × Bool) :
    ∀ M : GMap GoString (Option BktData × Bool),
      iprop(ghostMapAuth (GF := GF) g 1 M ∗
        ([∗map] n ↦ _u ∈ D, if S n then ghostMapElem g n (DFrac.own 1) (v n) else iprop(True))) ⊢
      |==> ∃ M' : GMap GoString (Option BktData × Bool), ghostMapAuth g 1 M' ∗
        ([∗map] n ↦ _u ∈ D, if S n then ghostMapElem g n (DFrac.own 1) (w n) else iprop(True)) := by
  induction D using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    intro M
    rw [BigSepM.bigSepM_empty.to_eq, BigSepM.bigSepM_empty.to_eq]
    iintro ⟨Ha, -⟩
    imodintro
    iexists M
    isplitl [Ha]; iexact Ha; iempintro
  | hins i x D hi IH =>
    intro M
    rw [(BigSepM.bigSepM_insert
      (Φ := fun n (_ : Unit) => if S n then ghostMapElem (GF := GF) g n (DFrac.own 1) (v n)
        else iprop(True)) hi).to_eq,
      (BigSepM.bigSepM_insert
      (Φ := fun n (_ : Unit) => if S n then ghostMapElem (GF := GF) g n (DFrac.own 1) (w n)
        else iprop(True)) hi).to_eq]
    iintro ⟨Ha, Hi, Hs⟩
    imod IH M $$ [Ha Hs] with ⟨%M1, Ha, Hs⟩
    · isplitl [Ha]; iexact Ha; iexact Hs
    by_cases hS : S i
    · ihave Hi := (show (if S i then ghostMapElem (GF := GF) g i (DFrac.own 1) (v i)
          else iprop(True)) ⊢ ghostMapElem g i (DFrac.own 1) (v i)
          by simp only [if_pos hS]; exact .rfl) $$ Hi
      imod ghost_map_update (w i) $$ Ha Hi with ⟨Ha, Hi⟩
      imodintro
      iexists _
      isplitl [Ha]; iexact Ha
      isplitl [Hi]
      · iapply (show ghostMapElem (GF := GF) g i (DFrac.own 1) (w i) ⊢
          (if S i then ghostMapElem g i (DFrac.own 1) (w i) else iprop(True))
          by simp only [if_pos hS]; exact .rfl) $$ Hi
      · iexact Hs
    · imodintro
      iexists M1
      isplitl [Ha]; iexact Ha
      isplitr
      · iapply (show (⊢ (if S i then ghostMapElem (GF := GF) g i (DFrac.own 1) (w i)
          else iprop(True))) by simp only [if_neg hS]; iintro; itrivial)
      · iexact Hs

/-- **The whole elements, updated** (the ghost map's authority with them). -/
theorem rbEls_update (γ : BNames) (S : GoString → Prop) (v w : GoString → Option BktData × Bool) :
    iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth (GF := GF) γ.rbk 1 M) ∗
      rbEls γ S 1 v) ⊢
      |==> iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth γ.rbk 1 M) ∗
        rbEls γ S 1 w) := by
  unfold rbEls rbElem
  iintro ⟨⟨%M, Ha⟩, Hs⟩
  imod els_update γ.rbk S γ.rbD v w M $$ [Ha Hs] with ⟨%M', Ha, Hs⟩
  · isplitl [Ha]; iexact Ha; iexact Hs
  imodintro
  isplitl [Ha]
  · iexists M'; iexact Ha
  · iexact Hs

/-- The elements of no bucket are nothing. -/
theorem rbEls_none (γ : BNames) (q : Qp) (v : GoString → Option BktData × Bool) :
    ⊢ rbEls (GF := GF) γ (fun _ => False) q v := by
  unfold rbEls
  refine BigSepM.bigSepM_intro (P := iprop(emp)) fun {k} {_} _ => ?_
  simp only [if_neg not_false]
  iintro -
  itrivial

/-- **Allocation**: a fresh ghost map whose elements over `D` are at `v`. -/
private theorem els_alloc_from (D : GMap GoString Unit) (v : GoString → Option BktData × Bool) (g : GName) :
    ∀ M : GMap GoString (Option BktData × Bool), (∀ k, D.lookup k ≠ none → M.lookup k = none) →
      ghostMapAuth (GF := GF) g 1 M ⊢
        |==> ∃ M' : GMap GoString (Option BktData × Bool), ghostMapAuth g 1 M' ∗
          ([∗map] n ↦ _u ∈ D, ghostMapElem g n (DFrac.own 1) (v n)) := by
  induction D using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    intro M _
    rw [BigSepM.bigSepM_empty.to_eq]
    iintro Ha
    imodintro
    iexists M
    isplitl [Ha]; iexact Ha; iempintro
  | hins i x D hi IH =>
    intro M hM
    rw [(BigSepM.bigSepM_insert
      (Φ := fun n (_ : Unit) => ghostMapElem (GF := GF) g n (DFrac.own 1) (v n)) hi).to_eq]
    have hi' : D.lookup i = none := hi
    have hMi : M.lookup i = none := hM i (by
      show (if i = i then some x else D.lookup i) ≠ none
      simp)
    iintro Ha
    imod ghost_map_insert i (v i) hMi $$ Ha with ⟨Ha, Hi⟩
    imod IH (M.insert i (v i)) (by
      intro k hk
      have hki : i ≠ k := by
        intro e; subst e; exact hk hi'
      rw [GMap.lookup_insert_ne _ _ hki]
      exact hM k (by
        show (if i = k then some x else D.lookup k) ≠ none
        rw [if_neg hki]; exact hk)) $$ Ha with ⟨%M', Ha, Hs⟩
    imodintro
    iexists M'
    isplitl [Ha]; iexact Ha
    isplitl [Hi]; iexact Hi; iexact Hs

/-- **Allocation of the tracked buckets' ghost map** over the names `D`, at `v`. -/
theorem rbEls_alloc (D : GMap GoString Unit) (v : GoString → Option BktData × Bool) :
    ⊢ |==> ∃ g : GName, (∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth (GF := GF) g 1 M) ∗
      ([∗map] n ↦ _u ∈ D, ghostMapElem g n (DFrac.own 1) (v n)) := by
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Option BktData × Bool)
    with ⟨%g, Ha⟩
  imod els_alloc_from D v g ∅ (fun _ _ => rfl) $$ Ha with ⟨%M', Ha, Hs⟩
  imodintro
  iexists g
  isplitl [Ha]
  · iexists M'; iexact Ha
  · iexact Hs

/-- The elements of every bucket, from the raw ghost map's (at `γ.rbk`, over `γ.rbD`). -/
theorem rbEls_top_of (γ : BNames) (q : Qp) (v : GoString → Option BktData × Bool) :
    ([∗map] n ↦ _u ∈ γ.rbD, ghostMapElem γ.rbk n (DFrac.own q) (v n)) ⊢
      rbEls (GF := GF) γ (fun _ => True) q v := by
  unfold rbEls
  refine BigSepM.bigSepM_mono fun {k} {_} _ => ?_
  simp only [if_pos trivial]
  exact .rfl

/-! ### The parts -/

/-- **Congruence of a part** (contents on the set, flags on its tracked buckets). -/
theorem rbPartF_congr (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (F F' : GoString → Bool) (hr : ∀ n, S n → r.lookup n = r'.lookup n)
    (hF : ∀ n, S n → γ.rbD.lookup n ≠ none → F n = F' n) :
    rbPartF (GF := GF) γ S r F ⊣⊢ rbPartF γ S r' F' := by
  unfold rbPartF
  have hv := rbEls_congr (GF := GF) γ S (1 : Qp).half (fun n => (r.lookup n, F n))
    (fun n => (r'.lookup n, F' n)) (fun n hS hn => by rw [hr n hS, hF n hS hn])
  constructor
  · iintro ⟨%Hp, H⟩
    isplitr
    · ipureintro; intro n hS h0; rw [← hr n hS]; exact Hp n hS h0
    · iapply hv.1 $$ H
  · iintro ⟨%Hp, H⟩
    isplitr
    · ipureintro; intro n hS h0; rw [hr n hS]; exact Hp n hS h0
    · iapply hv.2 $$ H

/-- A part at its flags is a part. -/
theorem rbPartF_part (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData)
    (F : GoString → Bool) : rbPartF (GF := GF) γ S r F ⊢ rbPart γ S r := by
  unfold rbPart
  iintro H
  iexists F
  iexact H

/-- Two parts agree on the buckets both have (contents, and flags on the tracked ones). -/
theorem rbPartF_agree (γ : BNames) (S S' : GoString → Prop) (r r' : GMap GoString BktData)
    (F F' : GoString → Bool) :
    iprop(rbPartF (GF := GF) γ S r F ∗ rbPartF γ S' r' F') ⊢
      iprop(rbPartF γ S r F ∗ rbPartF γ S' r' F' ∗
        ⌜(∀ n, S n → S' n → r.lookup n = r'.lookup n) ∧
          (∀ n, S n → S' n → γ.rbD.lookup n ≠ none → F n = F' n)⌝) := by
  unfold rbPartF
  iintro ⟨⟨%Hp, H1⟩, ⟨%Hp', H2⟩⟩
  icases rbEls_agree γ S S' _ _ _ _ $$ [$H1 $H2] with ⟨H1, H2, %Ha⟩
  isplitl [H1]
  · isplitr; ipureintro; exact Hp; iexact H1
  isplitl [H2]
  · isplitr; ipureintro; exact Hp'; iexact H2
  ipureintro
  constructor
  · intro n hS hS'
    by_cases hn : γ.rbD.lookup n = none
    · rw [Hp n hS hn, Hp' n hS' hn]
    · exact congrArg Prod.fst (Ha n hS hS' hn)
  · intro n hS hS' hn
    exact congrArg Prod.snd (Ha n hS hS' hn)

/-- **Two parts agree** on the buckets both have. -/
theorem rbPart_agree (γ : BNames) (S S' : GoString → Prop) (r r' : GMap GoString BktData) :
    iprop(rbPart (GF := GF) γ S r ∗ rbPart γ S' r') ⊢
      iprop(rbPart γ S r ∗ rbPart γ S' r' ∗ ⌜∀ n, S n → S' n → r.lookup n = r'.lookup n⌝) := by
  unfold rbPart
  iintro ⟨⟨%F, H1⟩, ⟨%F', H2⟩⟩
  icases rbPartF_agree γ S S' r r' F F' $$ [$H1 $H2] with ⟨H1, H2, %Ha⟩
  isplitl [H1]; iexists F; iexact H1
  isplitl [H2]; iexists F'; iexact H2
  ipureintro; exact Ha.1

/-- **The idle part agrees with a part, and stays idle.** -/
theorem rbOwnIn_agree (γ : BNames) (S S' : GoString → Prop) (r r' : GMap GoString BktData) :
    iprop(rbOwnIn (GF := GF) γ S r ∗ rbPart γ S' r') ⊢
      iprop(rbOwnIn γ S r ∗ rbPart γ S' r' ∗ ⌜∀ n, S n → S' n → r.lookup n = r'.lookup n⌝) := by
  unfold rbOwnIn rbPart
  iintro ⟨H1, ⟨%F', H2⟩⟩
  icases rbPartF_agree γ S S' r r' _ F' $$ [$H1 $H2] with ⟨H1, H2, %Ha⟩
  isplitl [H1]; iexact H1
  isplitl [H2]; iexists F'; iexact H2
  ipureintro; exact Ha.1

/-- **The client's halves of the tracked buckets agree** (two `rbOwn`s: the client's and the
batch lock's, as a snapshot's observation is handed). -/
theorem rbOwn_agree (γ : BNames) (r r' : GMap GoString BktData) :
    iprop(rbOwn (GF := GF) γ r ∗ rbOwn γ r') ⊢ iprop(rbOwn γ r ∗ rbOwn γ r' ∗ ⌜r = r'⌝) := by
  unfold rbOwn
  iintro H
  icases rbPart_agree γ (fun _ => True) (fun _ => True) r r' $$ H with ⟨H1, H2, %Ha⟩
  iframe H1 H2
  ipureintro
  exact GMap.ext fun n => Ha n trivial trivial

/-- **The parts of disjoint bucket sets, at the same flags, are the part of their union.** -/
theorem rbPartF_split (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (F : GoString → Bool) (hd : ∀ n, S n → S' n → False) :
    rbPartF (GF := GF) γ (fun n => S n ∨ S' n) r F ⊣⊢
      iprop(rbPartF γ S r F ∗ rbPartF γ S' r F) := by
  unfold rbPartF
  have he := rbEls_split (GF := GF) γ S S' (1 : Qp).half (fun n => (r.lookup n, F n)) hd
  constructor
  · iintro ⟨%Hp, Hs⟩
    icases he.1 $$ Hs with ⟨H1, H2⟩
    isplitl [H1]
    · isplitr
      · ipureintro; exact fun n h => Hp n (Or.inl h)
      · iexact H1
    · isplitr
      · ipureintro; exact fun n h => Hp n (Or.inr h)
      · iexact H2
  · iintro ⟨⟨%Hp1, H1⟩, ⟨%Hp2, H2⟩⟩
    isplitr
    · ipureintro
      rintro n (h | h)
      · exact Hp1 n h
      · exact Hp2 n h
    · iapply he.2
      isplitl [H1]; iexact H1; iexact H2

/-- **The parts of disjoint bucket sets are the part of their union.** -/
theorem rbPart_split (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (hd : ∀ n, S n → S' n → False) :
    rbPart (GF := GF) γ (fun n => S n ∨ S' n) r ⊣⊢ iprop(rbPart γ S r ∗ rbPart γ S' r) := by
  unfold rbPart
  constructor
  · iintro ⟨%F, H⟩
    icases (rbPartF_split γ S S' r F hd).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists F; iexact H1
    · iexists F; iexact H2
  · iintro ⟨⟨%F1, H1⟩, ⟨%F2, H2⟩⟩
    iexists (fun n => if S n then F1 n else F2 n)
    iapply (rbPartF_split γ S S' r _ hd).2
    isplitl [H1]
    · iapply (rbPartF_congr γ S r r F1 _ (fun _ _ => rfl)
        (fun n hS _ => by simp only [if_pos hS])).1 $$ H1
    · iapply (rbPartF_congr γ S' r r F2 _ (fun _ _ => rfl)
        (fun n hS' _ => by simp only [if_neg (fun hS => hd n hS hS')])).1 $$ H2

/-- **The idle parts of disjoint bucket sets are the idle part of their union.** -/
theorem rbOwnIn_split (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (hd : ∀ n, S n → S' n → False) :
    rbOwnIn (GF := GF) γ (fun n => S n ∨ S' n) r ⊣⊢ iprop(rbOwnIn γ S r ∗ rbOwnIn γ S' r) := by
  unfold rbOwnIn
  exact rbPartF_split γ S S' r _ hd

/-- **Restriction**: a part says nothing of the buckets outside its set. -/
theorem rbPart_congr (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (h : ∀ n, S n → r.lookup n = r'.lookup n) :
    rbPart (GF := GF) γ S r ⊣⊢ rbPart γ S r' := by
  unfold rbPart
  constructor
  · iintro ⟨%F, H⟩
    iexists F
    iapply (rbPartF_congr γ S r r' F F h (fun _ _ _ => rfl)).1 $$ H
  · iintro ⟨%F, H⟩
    iexists F
    iapply (rbPartF_congr γ S r r' F F h (fun _ _ _ => rfl)).2 $$ H

/-- **Restriction**, of the idle part. -/
theorem rbOwnIn_congr (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (h : ∀ n, S n → r.lookup n = r'.lookup n) :
    rbOwnIn (GF := GF) γ S r ⊣⊢ rbOwnIn γ S r' := by
  unfold rbOwnIn
  exact rbPartF_congr γ S r r' _ _ h (fun _ _ _ => rfl)

/-- **The same set**, extensionally (a law, so that clients need not unfold). -/
theorem rbOwnIn_set (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (h : ∀ n, S n ↔ S' n) : rbOwnIn (GF := GF) γ S r ⊣⊢ rbOwnIn γ S' r := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact .rfl

/-- **The same set**, extensionally, of the part. -/
theorem rbPart_set (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (h : ∀ n, S n ↔ S' n) : rbPart (GF := GF) γ S r ⊣⊢ rbPart γ S' r := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact .rfl

/-- **The idle part is a part** (forgetting that nothing is pending). -/
theorem rbOwnIn_part (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    rbOwnIn (GF := GF) γ S r ⊢ rbPart γ S r := by
  unfold rbOwnIn
  exact rbPartF_part γ S r _

/-- The part of no bucket is nothing. -/
theorem rbPart_none (γ : BNames) (r : GMap GoString BktData) :
    ⊢ rbPart (GF := GF) γ (fun _ => False) r := by
  unfold rbPart rbPartF
  iexists (fun _ => false)
  isplitr
  · ipureintro; intro n h; exact h.elim
  · iapply rbEls_none

/-- The idle part of no bucket is nothing. -/
theorem rbOwnIn_none (γ : BNames) (r : GMap GoString BktData) :
    ⊢ rbOwnIn (GF := GF) γ (fun _ => False) r := by
  unfold rbOwnIn rbPartF
  isplitr
  · ipureintro; intro n h; exact h.elim
  · iapply rbEls_none

/-- **The idle part of every bucket is the idle part of `S` and of the rest.** -/
theorem rbOwnIn_split_compl (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    rbOwnIn (GF := GF) γ (fun _ => True) r ⊣⊢
      iprop(rbOwnIn γ S r ∗ rbOwnIn γ (fun n => ¬ S n) r) := by
  refine (rbOwnIn_set γ _ (fun n => S n ∨ ¬ S n) r ?_).trans ?_
  · intro n; exact ⟨fun _ => Classical.em _, fun _ => trivial⟩
  exact rbOwnIn_split γ S (fun n => ¬ S n) r (fun _ h1 h2 => h2 h1)

/-- **The whole is the part of `S` and of the rest** (`rbOwn`'s split, for clients that never
need idleness). -/
theorem rbOwn_split (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    rbOwn (GF := GF) γ r ⊣⊢ iprop(rbPart γ S r ∗ rbPart γ (fun n => ¬ S n) r) := by
  unfold rbOwn
  refine (rbPart_set γ _ (fun n => S n ∨ ¬ S n) r ?_).trans ?_
  · intro n; exact ⟨fun _ => Classical.em _, fun _ => trivial⟩
  exact rbPart_split γ S (fun n => ¬ S n) r (fun _ h1 h2 => h2 h1)

/-! ### The ghost steps of the proved operations -/

/-- Two halves of a part, at the authority, updated to new contents and flags (whole elements
in between). -/
theorem rbPartF_update (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (F F' G : GoString → Bool)
    (hp : ∀ n, S n → γ.rbD.lookup n = none → r.lookup n = none → r'.lookup n = none) :
    iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth (GF := GF) γ.rbk 1 M) ∗
      rbPartF γ S r F ∗ rbPartF γ S r F') ⊢
      |==> iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth γ.rbk 1 M) ∗
        rbPartF γ S r' G ∗ rbPartF γ S r' G) := by
  iintro ⟨Ha, H1, H2⟩
  icases rbPartF_agree γ S S r r F F' $$ [$H1 $H2] with ⟨H1, H2, %Hag⟩
  ihave H2 := (rbPartF_congr γ S r r F' F (fun _ _ => rfl)
    (fun n hS hn => (Hag.2 n hS hS hn).symm)).1 $$ H2
  unfold rbPartF
  icases H1 with ⟨%Hp, H1⟩
  icases H2 with ⟨-, H2⟩
  ihave Hs := (rbEls_halves γ S _).1 $$ [$H1 $H2]
  imod rbEls_update γ S _ (fun n => (r'.lookup n, G n)) $$ [$Ha $Hs] with ⟨Ha, Hs⟩
  icases (rbEls_halves γ S _).2 $$ Hs with ⟨H1, H2⟩
  imodintro
  isplitl [Ha]; iexact Ha
  have hp' : ∀ n, S n → γ.rbD.lookup n = none → r'.lookup n = none :=
    fun n hS h0 => hp n hS h0 (Hp n hS h0)
  isplitl [H1]
  · isplitr; ipureintro; exact hp'; iexact H1
  · isplitr; ipureintro; exact hp'; iexact H2

/-- **A session's write to the tracked bucket `n`** (`UnsafePut`, `UnsafeDelete`,
`UnsafeCreateBucket`, `UnsafeDeleteBucket`): the batch lock's side and the client's part of `n`
updated to the new contents, the bucket's write pending. -/
theorem rbSide_put (γ : BNames) (P : BParams) (r r' : GMap GoString BktData) (n : GoString)
    (hBT : ∃ i, P.BT.lookup n = some i) (hRB : P.RB n = true)
    (hO : ∀ m, m ≠ n → r'.lookup m = r.lookup m) :
    iprop(rbSide (GF := GF) γ P r ∗ rbPart γ (fun m => m = n) r) ⊢
      |==> iprop(rbSide γ P r' ∗ rbPart γ (fun m => m = n) r') := by
  unfold rbSide
  iintro ⟨⟨Ha, Hl, %Hd⟩, Hc⟩
  have hd : γ.rbD.lookup n ≠ none := by
    obtain ⟨i, hi⟩ := hBT; exact Hd n i hi hRB
  icases (rbOwn_split γ (fun m => m = n) r).1 $$ Hl with ⟨Hln, Hlo⟩
  iunfold rbPart at Hln Hc
  icases Hln with ⟨%FL, Hln⟩
  icases Hc with ⟨%FC, Hc⟩
  imod rbPartF_update γ (fun m => m = n) r r' FL FC (fun _ => true)
    (by intro m hm h0; subst hm; exact absurd h0 hd) $$ [$Ha $Hln $Hc] with ⟨Ha, Hln, Hc⟩
  imodintro
  isplitl [Ha Hln Hlo]
  · isplitl [Ha]; iexact Ha
    isplitl [Hln Hlo]
    · iapply (rbOwn_split γ (fun m => m = n) r').2
      isplitl [Hln]
      · iapply rbPartF_part $$ Hln
      · iapply (rbPart_congr γ (fun m => ¬ m = n) r r' (fun m hm => (hO m hm).symm)).1 $$ Hlo
    · ipureintro; exact Hd
  · iapply rbPartF_part $$ Hc

/-- **`Unlock`'s ghost step**: the part handed in made idle (its flags cleared), the batch lock's
side with it. Only `batchTxBuffered.Unlock`'s proof takes it, at the end of the session (Go writes
the session back and commits a pending delete there); used anywhere else it would assert an
idleness Go does not give. -/
theorem rbSide_idle (γ : BNames) (P : BParams) (r : GMap GoString BktData) (S : GoString → Prop)
    (rS : GMap GoString BktData) :
    iprop(rbSide (GF := GF) γ P r ∗ rbPart γ S rS) ⊢ |==> iprop(rbSide γ P r ∗ rbOwnIn γ S rS) := by
  unfold rbSide rbOwnIn
  iintro ⟨⟨Ha, Hl, %Hd⟩, Hc⟩
  icases (rbOwn_split γ S r).1 $$ Hl with ⟨HlS, Hlo⟩
  icases rbPart_agree γ S S r rS $$ [$HlS $Hc] with ⟨HlS, Hc, %Hag⟩
  ihave HlS := (rbPart_congr γ S r rS (fun n h => Hag n h h)).1 $$ HlS
  iunfold rbPart at HlS Hc
  icases HlS with ⟨%FL, HlS⟩
  icases Hc with ⟨%FC, Hc⟩
  imod rbPartF_update γ S rS rS FL FC (fun _ => false) (fun _ _ _ h => h) $$ [$Ha $HlS $Hc]
    with ⟨Ha, HlS, Hc⟩
  imodintro
  isplitl [Ha HlS Hlo]
  · isplitl [Ha]; iexact Ha
    isplitl [HlS Hlo]
    · iapply (rbOwn_split γ S r).2
      isplitl [HlS]
      · iapply (rbPart_congr γ S rS r (fun n h => (Hag n h h).symm)).1
        iapply rbPartF_part $$ HlS
      · iexact Hlo
    · ipureintro; exact Hd
  · iexact Hc

/-- **The batch lock's side agrees with a part** on the part's buckets. -/
theorem rbSide_agree (γ : BNames) (P : BParams) (r : GMap GoString BktData) (S : GoString → Prop)
    (r' : GMap GoString BktData) :
    iprop(rbSide (GF := GF) γ P r ∗ rbPart γ S r') ⊢
      iprop(rbSide γ P r ∗ rbPart γ S r' ∗ ⌜∀ n, S n → r.lookup n = r'.lookup n⌝) := by
  unfold rbSide rbOwn
  iintro ⟨⟨Ha, Hl, %Hd⟩, Hc⟩
  icases rbPart_agree γ (fun _ => True) S r r' $$ [$Hl $Hc] with ⟨Hl, Hc, %Hag⟩
  isplitl [Ha Hl]
  · iframe Ha Hl; ipureintro; exact Hd
  iframe Hc
  ipureintro
  exact fun n h => Hag n trivial h

/-- **The batch lock's side agrees with an idle part**, which stays idle. -/
theorem rbSide_agree_in (γ : BNames) (P : BParams) (r : GMap GoString BktData)
    (S : GoString → Prop) (r' : GMap GoString BktData) :
    iprop(rbSide (GF := GF) γ P r ∗ rbOwnIn γ S r') ⊢
      iprop(rbSide γ P r ∗ rbOwnIn γ S r' ∗ ⌜∀ n, S n → r.lookup n = r'.lookup n⌝) := by
  unfold rbSide rbOwn
  iintro ⟨⟨Ha, Hl, %Hd⟩, Hc⟩
  icases rbOwnIn_agree γ S (fun _ => True) r' r $$ [$Hc $Hl] with ⟨Hc, Hl, %Hag⟩
  isplitl [Ha Hl]
  · iframe Ha Hl; ipureintro; exact Hd
  iframe Hc
  ipureintro
  exact fun n h => (Hag n h trivial).symm

/-- **The whole-form write resource is the part of bucket `n` and the rest** (for callers holding
`rbOwn`: they hand the operation `rbPut` and get `rbPutAll` back). -/
theorem rbPutAll_split (γ : BNames) (P : BParams) (n : GoString) (S : Data) :
    rbPutAll (GF := GF) γ P n S ⊢
      iprop(rbPut γ P n S ∗
        (∀ S' : Data, ⌜∀ m, m ≠ n → S'.lookup m = S.lookup m⌝ -∗
          rbPut γ P n S' -∗ rbPutAll γ P n S')) := by
  unfold rbPutAll rbPut
  cases hn : P.RB n
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro -
    isplitr
    · itrivial
    iintro %S' - -
    itrivial
  · simp only [↓reduceIte]
    iintro H
    icases (rbOwn_split γ (fun m => m = n) (rbData P S)).1 $$ H with ⟨Hn, Hr⟩
    iframe Hn
    iintro %S' %hS' Hn'
    have hcg : ∀ m : GoString, ¬ m = n → (rbData P S).lookup m = (rbData P S').lookup m := by
      intro m hm
      rw [rbData_lookup, rbData_lookup, hS' m hm]
    iapply (rbOwn_split γ (fun m => m = n) (rbData P S')).2
    iframe Hn'
    iapply (rbPart_congr γ _ (rbData P S) (rbData P S') hcg).1 $$ Hr

end tracked

end backend
end EtcdGrove
end Perennial
