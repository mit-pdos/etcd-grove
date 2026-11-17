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
import all Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

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
private theorem rbEls_update (γ : BNames) (S : GoString → Prop) (v w : GoString → Option BktData × Bool) :
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
  have hv := rbEls_congr (GF := GF) γ S (1 : Qp).half.half (fun n => (r.lookup n, F n))
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
  have he := rbEls_split (GF := GF) γ S S' (1 : Qp).half.half (fun n => (r.lookup n, F n)) hd
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

/-! ### The claim invariant's pieces (A6.2 of `auth-schema-srv`, 2026-11-17)

Fractions, ghost map elements, one entry of a family, and the claim invariant's two branches. -/

theorem q4_add : (1 : Qp).half.half + (1 : Qp).half.half = (1 : Qp).half := Qp.half_add_half _

theorem q2_add : (1 : Qp).half + (1 : Qp).half = 1 := Qp.half_add_half _

theorem q34_add : ((1 : Qp).half + (1 : Qp).half.half) + (1 : Qp).half.half = 1 :=
  Subtype.ext (by simp; grind)

theorem q_whole : ((1 : Qp).half.half + (1 : Qp).half.half) + (1 : Qp).half = 1 := by
  rw [q4_add, q2_add]

theorem q_over : 1 < ((1 : Qp).half.half + (1 : Qp).half.half).val +
    ((1 : Qp).half + (1 : Qp).half.half).val := by
  simp; grind

theorem dfrac_own_op (a b : Qp) : DFrac.own a • DFrac.own b = DFrac.own (a + b) := rfl

/-- Two shares of one element: one share, the values equal. -/
theorem gme_join {V : Type} [Pos.Countable V] (g : GName) (n : GoString) (q1 q2 : Qp) (v1 v2 : V) :
    iprop(ghostMapElem (GF := GF) g n (DFrac.own q1) v1 ∗ ghostMapElem g n (DFrac.own q2) v2) ⊢
      iprop(ghostMapElem g n (DFrac.own (q1 + q2)) v1 ∗ ⌜v1 = v2⌝) := by
  have h := ghostMapElem_combine (GF := GF) n g (DFrac.own q1) (DFrac.own q2) v1 v2
  rw [dfrac_own_op] at h
  iintro ⟨H1, H2⟩
  iapply h $$ H1 H2

/-- One share as two. -/
theorem gme_split {V : Type} [Pos.Countable V] (g : GName) (n : GoString) (q1 q2 : Qp) (v : V) :
    ghostMapElem (GF := GF) g n (DFrac.own (q1 + q2)) v ⊢
      iprop(ghostMapElem g n (DFrac.own q1) v ∗ ghostMapElem g n (DFrac.own q2) v) :=
  ((ghostMapElem_fractional n g v).fractional q1 q2).1

/-- A share at an equal fraction. -/
theorem gme_frac {V : Type} [Pos.Countable V] (g : GName) (n : GoString) (q q' : Qp) (v : V)
    (h : q = q') : ghostMapElem (GF := GF) g n (DFrac.own q) v ⊢ ghostMapElem g n (DFrac.own q') v := by
  rw [h]

/-- Two shares of one element above the whole: false. -/
theorem gme_excl {V : Type} [Pos.Countable V] (g : GName) (n : GoString) (q1 q2 : Qp) (v1 v2 : V)
    (h : 1 < q1.val + q2.val) :
    iprop(ghostMapElem (GF := GF) g n (DFrac.own q1) v1 ∗ ghostMapElem g n (DFrac.own q2) v2) ⊢ False := by
  iintro ⟨H1, H2⟩
  ihave %Hv := ghostMapElem_valid_2 n g _ _ _ _ $$ H1 H2
  exfalso
  have h1 := Hv.1
  rw [dfrac_own_op] at h1
  have h2 : (q1 + q2).val ≤ 1 := h1
  simp only [Qp.val_add] at h2
  exact absurd h (Std.not_lt.2 h2)

/-- One entry of a family over `D`, the family rebuilt with another family equal elsewhere. -/
theorem mapAcc (D : GMap GoString Unit) (Φ Ψ : GoString → IProp GF) (n : GoString)
    (hn : D.lookup n ≠ none) (h : ∀ k, k ≠ n → Φ k ⊢ Ψ k) :
    ([∗map] k ↦ _u ∈ D, Φ k) ⊢ iprop(Φ n ∗ (Ψ n -∗ [∗map] k ↦ _u ∈ D, Ψ k)) := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hn
  iintro H
  icases (BigSepM.bigSepM_lookup_acc_impl (Φ := fun k (_ : Unit) => Φ k) (m := D) (i := n) (x := u) hu)
    $$ H with ⟨Hn, Hw⟩
  iframe Hn
  iintro Hn'
  ispecialize Hw $$ %(fun k (_ : Unit) => Ψ k)
  iapply Hw
  · iintro !> %k %x %_ %hk H
    iapply (h k hk) $$ H
  · iexact Hn'

/-- One entry, as the family over `D` with that entry alone. -/
theorem mapIf_one (D : GMap GoString Unit) (S : GoString → Prop) (n : GoString) (hS : ∀ k, S k ↔ k = n)
    (hn : D.lookup n ≠ none) (X : GoString → IProp GF) :
    X n ⊣⊢ [∗map] k ↦ _u ∈ D, (if S k then X k else iprop(True)) := by
  constructor
  · iintro Hx
    ihave H0 : [∗map] k ↦ _u ∈ D, (iprop(True) : IProp GF) $$ []
    · exact BigSepM.bigSepM_intro (P := iprop(emp)) fun {_} {_} _ => by iintro -; itrivial
    icases mapAcc D (fun _ => iprop(True)) (fun k => if S k then X k else iprop(True)) n hn (fun k hk => by
      rw [if_neg (fun h => hk ((hS k).1 h))]) $$ H0 with ⟨-, Hw⟩
    iapply Hw
    rw [if_pos ((hS n).2 rfl)]
    iexact Hx
  · iintro H
    icases mapAcc D (fun k => if S k then X k else iprop(True)) (fun _ => iprop(True)) n hn
      (fun _ _ => by iintro -; itrivial) $$ H with ⟨Hn, -⟩
    rw [if_pos ((hS n).2 rfl)]
    iexact Hn

/-- **A part of one tracked bucket is a quarter of its element.** -/
theorem rbPartF_one (γ : BNames) (n : GoString) (r : GMap GoString BktData) (F : GoString → Bool)
    (hd : γ.rbD.lookup n ≠ none) :
    rbPartF (GF := GF) γ (fun m => m = n) r F ⊣⊢ rbElem γ n (1 : Qp).half.half (r.lookup n, F n) := by
  unfold rbPartF rbEls
  have h := mapIf_one (GF := GF) γ.rbD (fun m => m = n) n (fun _ => Iff.rfl) hd
    (fun k => rbElem γ k (1 : Qp).half.half (r.lookup k, F k))
  constructor
  · iintro ⟨-, H⟩
    iapply h.2 $$ H
  · iintro H
    isplitr
    · ipureintro; intro m hm h0; subst hm; exact absurd h0 hd
    · iapply h.1 $$ H

/-- The elements of every bucket, as the raw family. -/
theorem rbEls_top (γ : BNames) (q : Qp) (v : GoString → Option BktData × Bool) :
    rbEls (GF := GF) γ (fun _ => True) q v ⊣⊢
      [∗map] n ↦ _u ∈ γ.rbD, ghostMapElem γ.rbk n (DFrac.own q) (v n) := by
  unfold rbEls
  constructor
  · refine BigSepM.bigSepM_mono fun {k} {_} _ => ?_
    simp only [if_pos trivial]; exact .rfl
  · exact rbEls_top_of γ q v

theorem rbClaimOne_U (γ : BNames) (n : GoString) (cl : Bool) (h : cl = false) :
    rbClaimOne (GF := GF) γ n cl ⊣⊢ rbClaimU γ n := by
  subst h; unfold rbClaimOne; simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨.rfl, .rfl⟩

theorem rbClaimOne_C (γ : BNames) (n : GoString) (cl : Bool) (h : cl = true) :
    rbClaimOne (GF := GF) γ n cl ⊣⊢ rbClaimC γ n := by
  subst h; unfold rbClaimOne; simp only [↓reduceIte]; exact ⟨.rfl, .rfl⟩

/-- **Update each entry** of a family over `D`, threading a resource `A` (an authority). -/
theorem map_upd_thread (A : IProp GF) (Φ Ψ : GoString → IProp GF) (D : GMap GoString Unit) :
    (∀ n, D.lookup n ≠ none → iprop(A ∗ Φ n) ⊢ |==> iprop(A ∗ Ψ n)) →
    iprop(A ∗ [∗map] n ↦ _u ∈ D, Φ n) ⊢ |==> iprop(A ∗ [∗map] n ↦ _u ∈ D, Ψ n) := by
  induction D using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    intro _
    iintro ⟨Ha, -⟩
    imodintro
    iframe Ha
    rw [BigSepM.bigSepM_empty.to_eq]; iempintro
  | hins i x D hi IH =>
    intro h
    rw [(BigSepM.bigSepM_insert (Φ := fun n (_ : Unit) => Φ n) hi).to_eq,
      (BigSepM.bigSepM_insert (Φ := fun n (_ : Unit) => Ψ n) hi).to_eq]
    iintro ⟨Ha, Hi, Hs⟩
    imod h i (by show (if i = i then some x else D.lookup i) ≠ none; simp) $$ [Ha Hi] with ⟨Ha, Hi⟩
    · iframe
    imod IH (fun n hn => h n (by
        show (if i = n then some x else D.lookup n) ≠ none
        by_cases e : i = n
        · simp [e]
        · rw [if_neg e]; exact hn)) $$ [Ha Hs] with ⟨Ha, Hs⟩
    · iframe
    imodintro
    iframe

/-- Three families over one map, as one. -/
theorem map_zip3 (D : GMap GoString Unit) (A B C : GoString → IProp GF) :
    iprop(([∗map] n ↦ _u ∈ D, A n) ∗ ([∗map] n ↦ _u ∈ D, B n) ∗ ([∗map] n ↦ _u ∈ D, C n)) ⊣⊢
      [∗map] n ↦ _u ∈ D, iprop(A n ∗ B n ∗ C n) := by
  rw [BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => A n),
    BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => B n)]
  exact ⟨.rfl, .rfl⟩

/-- Four families over one map, as one. -/
theorem map_zip4 (D : GMap GoString Unit) (A B C E : GoString → IProp GF) :
    iprop(([∗map] n ↦ _u ∈ D, A n) ∗ ([∗map] n ↦ _u ∈ D, B n) ∗ ([∗map] n ↦ _u ∈ D, C n) ∗
      ([∗map] n ↦ _u ∈ D, E n)) ⊣⊢
      [∗map] n ↦ _u ∈ D, iprop(A n ∗ B n ∗ C n ∗ E n) := by
  rw [BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => A n),
    BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => B n),
    BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => C n)]
  exact ⟨.rfl, .rfl⟩

/-- Five families over one map, as one. -/
theorem map_zip5 (D : GMap GoString Unit) (A B C E G : GoString → IProp GF) :
    iprop(([∗map] n ↦ _u ∈ D, A n) ∗ ([∗map] n ↦ _u ∈ D, B n) ∗ ([∗map] n ↦ _u ∈ D, C n) ∗
      ([∗map] n ↦ _u ∈ D, E n) ∗ ([∗map] n ↦ _u ∈ D, G n)) ⊣⊢
      [∗map] n ↦ _u ∈ D, iprop(A n ∗ B n ∗ C n ∗ E n ∗ G n) := by
  rw [BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => A n),
    BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => B n),
    BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => C n),
    BigSepM.bigSepM_sep_eq (Φ := fun n (_ : Unit) => E n)]
  exact ⟨.rfl, .rfl⟩

/-! ### The ghost steps of the proved operations -/

/-- The whole part at flags `F` is its parts on `S` and on the rest, at the same flags. -/
private theorem rbPartF_split_compl (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData)
    (F : GoString → Bool) :
    rbPartF (GF := GF) γ (fun _ => True) r F ⊢ iprop(rbPartF γ S r F ∗ rbPartF γ (fun n => ¬ S n) r F) := by
  have hset : (fun _ : GoString => True) = (fun n => S n ∨ ¬ S n) :=
    funext fun n => propext ⟨fun _ => Classical.em _, fun _ => trivial⟩
  rw [hset]
  exact (rbPartF_split γ S (fun n => ¬ S n) r F (fun _ h1 h2 => h2 h1)).1

/-- The parts on `S` and on the rest, at the same flags, are the whole part. -/
private theorem rbPartF_join_same (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData)
    (F : GoString → Bool) :
    iprop(rbPartF (GF := GF) γ S r F ∗ rbPartF γ (fun n => ¬ S n) r F) ⊢ rbPartF γ (fun _ => True) r F := by
  have hset : (fun _ : GoString => True) = (fun n => S n ∨ ¬ S n) :=
    funext fun n => propext ⟨fun _ => Classical.em _, fun _ => trivial⟩
  rw [hset]
  exact (rbPartF_split γ S (fun n => ¬ S n) r F (fun _ h1 h2 => h2 h1)).2

/-- The parts on `S` and on the rest, at flags `F1` and `F2`, are the whole part at their union's flags. -/
private theorem rbPartF_join_compl (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData)
    (F1 F2 : GoString → Bool) :
    iprop(rbPartF (GF := GF) γ S r F1 ∗ rbPartF γ (fun n => ¬ S n) r F2) ⊢
      rbPartF γ (fun _ => True) r (fun n => if S n then F1 n else F2 n) := by
  have hset : (fun _ : GoString => True) = (fun n => S n ∨ ¬ S n) :=
    funext fun n => propext ⟨fun _ => Classical.em _, fun _ => trivial⟩
  rw [hset]
  iintro ⟨H1, H2⟩
  iapply (rbPartF_split γ S (fun n => ¬ S n) r _ (fun _ h1 h2 => h2 h1)).2
  isplitl [H1]
  · iapply (rbPartF_congr γ S r r F1 _ (fun _ _ => rfl) (fun n hS _ => by simp only [if_pos hS])).1 $$ H1
  · iapply (rbPartF_congr γ (fun n => ¬ S n) r r F2 _ (fun _ _ => rfl)
      (fun n hS _ => by simp only [if_neg hS])).1 $$ H2

/-- **A session's write to the tracked bucket `n`** (`UnsafePut`, `UnsafeDelete`,
`UnsafeCreateBucket`, `UnsafeDeleteBucket`): the batch lock's side and the client's part of `n`
updated to the new contents, the bucket's write pending (`I'` of the other buckets with no write
pending, from `I`). (A6.2) The bucket is unclaimed (the client's quarter, the batch lock's and a claimed
bucket's three quarters are too many), and its element is whole only with the claim invariant's half,
which the write updates (the flag set: the invariant's link holds vacuously). -/
theorem rbSide_put (γ : BNames) (P : BParams) (r r' : GMap GoString BktData) (n : GoString)
    (hBT : ∃ i, P.BT.lookup n = some i) (hRB : P.RB n = true)
    (hO : ∀ m, m ≠ n → r'.lookup m = r.lookup m) (I I' : GoString → Prop)
    (hI : ∀ m, m ≠ n → I m → I' m) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rbSide (GF := GF) γ P r I ∗ rbPart γ (fun m => m = n) r) ⊢
      |={E}=> iprop(rbSide γ P r' I' ∗ rbPart γ (fun m => m = n) r') := by
  unfold rbSide
  iintro ⟨⟨⟨%M, Ha⟩, ⟨%FL, Hl, %HI⟩, %Hd, #Hinv⟩, Hc⟩
  have hd : γ.rbD.lookup n ≠ none := by
    obtain ⟨i, hi⟩ := hBT; exact Hd n i hi hRB
  icases rbPartF_split_compl γ (fun m => m = n) r FL $$ Hl with ⟨Hln, Hlo⟩
  iunfold rbPart at Hc
  icases Hc with ⟨%FC, Hc⟩
  ihave Hln := (rbPartF_one γ n r FL hd).1 $$ Hln
  ihave Hc := (rbPartF_one γ n r FC hd).1 $$ Hc
  icases gme_join γ.rbk n _ _ _ _ $$ [$Hln $Hc] with ⟨Hlc, -⟩
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  icases mapAcc γ.rbD (fun k => rbClaimOne (GF := GF) γ k (Cl k)) (fun k => rbClaimOne (GF := GF) γ k (Cl k))
    n hd (fun _ _ => .rfl) $$ Hm with ⟨Hn, Hm⟩
  cases hcl : Cl n
  · ihave Hn := (rbClaimOne_U γ n _ rfl).1 $$ Hn
    iunfold rbClaimU at Hn
    icases Hn with ⟨%c, %f, %v, Hk, Hr, Hcn, -⟩
    icases gme_join γ.rbk n _ _ _ _ $$ [$Hlc $Hk] with ⟨Hw, -⟩
    ihave Hw := gme_frac γ.rbk n _ 1 _ q_whole $$ Hw
    imod ghost_map_update ((r'.lookup n, true) : Option BktData × Bool) $$ Ha Hw with ⟨Ha, Hw⟩
    ihave Hw := gme_frac γ.rbk n 1 _ _ q_whole.symm $$ Hw
    icases gme_split γ.rbk n _ _ _ $$ Hw with ⟨Hlc, Hk⟩
    icases gme_split γ.rbk n _ _ _ $$ Hlc with ⟨Hln, Hc⟩
    imod Hclose $$ [Hac Hm Hk Hr Hcn] with -
    · inext
      iunfold rbClaimInv
      iexists _, Cl
      iframe Hac
      isplitr
      · ipureintro; exact Hbt
      iapply Hm
      iapply (rbClaimOne_U γ n _ rfl).2
      iunfold rbClaimU
      iexists r'.lookup n, true, v
      iframe
      ipureintro; intro h; cases h
    imodintro
    isplitl [Ha Hln Hlo]
    · isplitl [Ha]
      · iexists _; iexact Ha
      isplitl [Hln Hlo]
      · iexists (fun m => @ite _ (m = n) (Classical.propDecidable _) true (FL m))
        isplitl [Hln Hlo]
        · iapply rbPartF_join_compl γ (fun m => m = n) r' (fun _ => true) FL
          isplitl [Hln]
          · iapply (rbPartF_one γ n r' (fun _ => true) hd).2 $$ Hln
          iapply (rbPartF_congr γ (fun m => ¬ m = n) r r' FL FL (fun m hm => (hO m hm).symm)
            (fun _ _ _ => rfl)).1 $$ Hlo
        · ipureintro
          intro m hm hf
          by_cases e : m = n
          · simp [e] at hf
          · simp only [if_neg e] at hf; exact hI m e (HI m hm hf)
      isplitr
      · ipureintro; exact Hd
      · iexact Hinv
    · iapply rbPartF_part γ _ r' (fun _ => true)
      iapply (rbPartF_one γ n r' (fun _ => true) hd).2 $$ Hc
  · ihave Hn := (rbClaimOne_C γ n _ rfl).1 $$ Hn
    iunfold rbClaimC at Hn
    icases Hn with ⟨%c, %w, Hk, -, -⟩
    iexfalso
    iapply gme_excl γ.rbk n _ _ _ _ q_over $$ [$Hlc $Hk]

/-- (A6.2) One tracked bucket's flag cleared at `Unlock`'s end (`rbSide_idle`): with the batch lock's
quarter and the client's, the claim invariant's half of the (unclaimed) element whole; the invariant's link
re-established from the batch lock's readers' quarter (the readers see the writer's contents there). -/
private theorem idle_one (γ : BNames) (P : BParams) (st : BSess) (S : GoString → Prop)
    (r : GMap GoString BktData) (FL FC : GoString → Bool) (Cl : GoString → Bool) (n : GoString)
    (hrv : S n → rvBkt P (st.C, st.R) n = (r.lookup n).getD ∅) :
    iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth (GF := GF) γ.rbk 1 M) ∗
      (rbElem γ n (1 : Qp).half.half (r.lookup n, FL n) ∗
        (if S n then rbElem γ n (1 : Qp).half.half (r.lookup n, FC n) else iprop(True)) ∗
        rbClaimOne γ n (Cl n) ∗ rbrOne γ P st n)) ⊢
    |==> iprop((∃ M : GMap GoString (Option BktData × Bool), ghostMapAuth γ.rbk 1 M) ∗
      (rbElem γ n (1 : Qp).half.half (r.lookup n, if S n then false else FL n) ∗
        (if S n then rbElem γ n (1 : Qp).half.half (r.lookup n, false) else iprop(True)) ∗
        rbClaimOne γ n (Cl n) ∗ rbrOne γ P st n)) := by
  by_cases hS : S n
  · simp only [if_pos hS]
    iintro ⟨⟨%M, Ha⟩, Hl, Hc, Hn, Hrb⟩
    icases gme_join γ.rbk n _ _ _ _ $$ [$Hl $Hc] with ⟨Hlc, -⟩
    cases hcl : Cl n
    · ihave Hn := (rbClaimOne_U γ n _ rfl).1 $$ Hn
      iunfold rbClaimU at Hn
      icases Hn with ⟨%c, %f, %v, Hk, Hr, Hcn, -⟩
      iunfold rbrOne at Hrb
      icases gme_join γ.rbr n _ _ _ _ $$ [$Hr $Hrb] with ⟨Hr, %Hv⟩
      subst Hv
      icases gme_split γ.rbr n _ _ _ $$ Hr with ⟨Hr, Hrb⟩
      icases gme_join γ.rbk n _ _ _ _ $$ [$Hlc $Hk] with ⟨Hw, -⟩
      ihave Hw := gme_frac γ.rbk n _ 1 _ q_whole $$ Hw
      imod ghost_map_update ((r.lookup n, false) : Option BktData × Bool) $$ Ha Hw with ⟨Ha, Hw⟩
      ihave Hw := gme_frac γ.rbk n 1 _ _ q_whole.symm $$ Hw
      icases gme_split γ.rbk n _ _ _ $$ Hw with ⟨Hlc, Hk⟩
      icases gme_split γ.rbk n _ _ _ $$ Hlc with ⟨Hl, Hc⟩
      imodintro
      isplitl [Ha]
      · iexists _; iexact Ha
      iframe Hl Hc
      isplitl [Hk Hr Hcn]
      · iapply (rbClaimOne_U γ n _ rfl).2
        iunfold rbClaimU
        iexists r.lookup n, false, _
        iframe
        ipureintro; intro _; exact hrv hS
      · iunfold rbrOne; iexact Hrb
    · ihave Hn := (rbClaimOne_C γ n _ rfl).1 $$ Hn
      iunfold rbClaimC at Hn
      icases Hn with ⟨%c, %w, Hk, -, -⟩
      iexfalso
      iapply gme_excl γ.rbk n _ _ _ _ q_over $$ [$Hlc $Hk]
  · simp only [if_neg hS]
    iintro H
    imodintro
    iexact H

/-- **`Unlock`'s ghost step**: the part handed in made idle (its flags cleared), the batch lock's
side with it (`I'` of the buckets with no write pending: `S`'s and those with none before). Only
`batchTxBuffered.Unlock`'s proof takes it, at the end of the session (Go writes the session back and
commits a pending delete there); used anywhere else it would assert an idleness Go does not give.
(A6.2) The claim invariant's link of each of `S`'s buckets re-established: the readers see the writer's
contents there (`hrv`, from `trkOk` and the buckets untouched). -/
private theorem rbSide_idle (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (rS : GMap GoString BktData) (I I' : GoString → Prop) (hI : ∀ m, I m → I' m) (hS : ∀ m, S m → I' m)
    (hrv : ∀ n, S n → rvBkt P (st.C, st.R) n = ((rbData P st.S).lookup n).getD ∅)
    (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rbSide (GF := GF) γ P (rbData P st.S) I ∗ rbrSide γ P st c ∗ rbPart γ S rS) ⊢
      |={E}=> iprop(rbSide γ P (rbData P st.S) I' ∗ rbrSide γ P st c ∗ rbOwnIn γ S rS) := by
  unfold rbSide rbrSide rbOwnIn
  iintro ⟨⟨Ha, ⟨%FL, Hl, %HI⟩, %Hd, #Hinv⟩, ⟨Har, %Hrd, %Hcw, Hb⟩, Hc⟩
  iunfold rbPart at Hc
  icases Hc with ⟨%FC, Hc⟩
  icases rbPartF_agree γ (fun _ => True) S (rbData P st.S) rS FL FC $$ [$Hl $Hc] with ⟨Hl, Hc, %Hag⟩
  ihave Hc := (rbPartF_congr γ S rS (rbData P st.S) FC FC (fun n h => (Hag.1 n trivial h).symm)
    (fun _ _ _ => rfl)).1 $$ Hc
  iunfold rbPartF at Hl
  iunfold rbPartF at Hc
  icases Hl with ⟨%Hpl, Hl⟩
  icases Hc with ⟨%Hpc, Hc⟩
  ihave Hl := (rbEls_top γ _ _).1 $$ Hl
  iunfold rbEls at Hc
  iinv Hinv with >Hbody Hclose
  iunfold rbClaimInv at Hbody
  icases Hbody with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  ihave Hz := (map_zip4 γ.rbD
    (fun n => rbElem (GF := GF) γ n (1 : Qp).half.half ((rbData P st.S).lookup n, FL n))
    (fun n => if S n then rbElem (GF := GF) γ n (1 : Qp).half.half ((rbData P st.S).lookup n, FC n)
      else iprop(True))
    (fun n => rbClaimOne (GF := GF) γ n (Cl n)) (fun n => rbrOne (GF := GF) γ P st n)).1 $$ [$Hl $Hc $Hm $Hb]
  imod map_upd_thread _ _ _ γ.rbD (fun n _ => idle_one γ P st S (rbData P st.S) FL FC Cl n (hrv n))
    $$ [$Ha $Hz] with ⟨Ha, Hz⟩
  icases (map_zip4 γ.rbD
    (fun n => rbElem (GF := GF) γ n (1 : Qp).half.half ((rbData P st.S).lookup n, if S n then false else FL n))
    (fun n => if S n then rbElem (GF := GF) γ n (1 : Qp).half.half ((rbData P st.S).lookup n, false)
      else iprop(True))
    (fun n => rbClaimOne (GF := GF) γ n (Cl n)) (fun n => rbrOne (GF := GF) γ P st n)).2 $$ Hz
    with ⟨Hl, Hc, Hm, Hb⟩
  imod Hclose $$ [Hac Hm] with -
  · inext
    iunfold rbClaimInv
    iexists Mc, Cl
    iframe Hac Hm
    ipureintro; exact Hbt
  imodintro
  isplitl [Ha Hl]
  · iframe Ha
    isplitl [Hl]
    · iexists (fun m => if S m then false else FL m)
      isplitl [Hl]
      · iunfold rbPartF
        isplitr
        · ipureintro; exact Hpl
        iapply (rbEls_top γ _ (fun n => ((rbData P st.S).lookup n, if S n then false else FL n))).2 $$ Hl
      · ipureintro
        intro m hm hf
        by_cases e : S m
        · exact hS m e
        · simp only [if_neg e] at hf; exact hI m (HI m hm hf)
    isplitr
    · ipureintro; exact Hd
    · iexact Hinv
  isplitl [Har Hb]
  · iframe Har Hb
    ipureintro; exact ⟨Hrd, Hcw⟩
  · iapply (rbPartF_congr γ S (rbData P st.S) rS _ _ (fun n h => Hag.1 n trivial h) (fun _ _ _ => rfl)).1
    iunfold rbPartF
    isplitr
    · ipureintro; exact Hpc
    · iunfold rbEls; iexact Hc

/-- (A1.7) **The batch lock's side, with a weaker fact of the buckets with no write pending.** -/
theorem rbSide_mono (γ : BNames) (P : BParams) (r : GMap GoString BktData) (I I' : GoString → Prop)
    (h : ∀ n, I n → I' n) : rbSide (GF := GF) γ P r I ⊢ rbSide γ P r I' := by
  unfold rbSide
  iintro ⟨Ha, ⟨%F, Hl, %HI⟩, %Hd, #Hinv⟩
  iframe Ha
  isplitl [Hl]
  · iexists F; iframe Hl; ipureintro; exact fun n hn hf => h n (HI n hn hf)
  isplitr
  · ipureintro; exact Hd
  · iexact Hinv

/-- (A1.7) The batch lock's halves, with a weaker fact of the buckets with no write pending. -/
theorem trkHalf_mono (γ : BNames) (P : BParams) (S : Data) (I I' : GoString → Prop)
    (h : ∀ n, I n → I' n) : trkHalf (GF := GF) γ P S I ⊢ trkHalf γ P S I' := by
  unfold trkHalf
  iintro ⟨Hh, Hs⟩
  iframe Hh
  iapply rbSide_mono γ P _ I I' h $$ Hs

/-- (R2b-3c part 2) **The batch lock's side holds the lock's half of the tracked buckets** (the stopped
lock's, which `Close` hands out). -/
theorem rbSide_rbOwn (γ : BNames) (P : BParams) (r : GMap GoString BktData)
    (I : GoString → Prop := fun _ => True) :
    rbSide (GF := GF) γ P r I ⊢ rbOwn γ r := by
  unfold rbSide rbOwn rbPart
  iintro ⟨-, ⟨%F, Hl, -⟩, -⟩
  iexists F
  iexact Hl

/-- **The batch lock's side agrees with a part** on the part's buckets. -/
theorem rbSide_agree (γ : BNames) (P : BParams) (r : GMap GoString BktData) (S : GoString → Prop)
    (r' : GMap GoString BktData) {I : GoString → Prop} :
    iprop(rbSide (GF := GF) γ P r I ∗ rbPart γ S r') ⊢
      iprop(rbSide γ P r I ∗ rbPart γ S r' ∗ ⌜∀ n, S n → r.lookup n = r'.lookup n⌝) := by
  unfold rbSide rbPart
  iintro ⟨⟨Ha, ⟨%F, Hl, %HI⟩, %Hd, #Hinv⟩, ⟨%F', Hc⟩⟩
  icases rbPartF_agree γ (fun _ => True) S r r' F F' $$ [$Hl $Hc] with ⟨Hl, Hc, %Hag⟩
  isplitl [Ha Hl]
  · iframe Ha
    isplitl [Hl]
    · iexists F; iframe Hl; ipureintro; exact HI
    isplitr
    · ipureintro; exact Hd
    · iexact Hinv
  isplitl [Hc]
  · iexists F'; iexact Hc
  ipureintro
  exact fun n h => Hag.1 n trivial h

/-- **The batch lock's side agrees with an idle part**, which stays idle; (A1.7) the buckets of the part
satisfy `I` (their flags are clear). -/
theorem rbSide_agree_inI (γ : BNames) (P : BParams) (r : GMap GoString BktData)
    (S : GoString → Prop) (r' : GMap GoString BktData) {I : GoString → Prop} :
    iprop(rbSide (GF := GF) γ P r I ∗ rbOwnIn γ S r') ⊢
      iprop(rbSide γ P r I ∗ rbOwnIn γ S r' ∗ ⌜∀ n, S n → r.lookup n = r'.lookup n⌝ ∗
        ⌜∀ n, S n → γ.rbD.lookup n ≠ none → I n⌝) := by
  unfold rbSide rbOwnIn
  iintro ⟨⟨Ha, ⟨%F, Hl, %HI⟩, %Hd, #Hinv⟩, Hc⟩
  icases rbPartF_agree γ (fun _ => True) S r r' F _ $$ [$Hl $Hc] with ⟨Hl, Hc, %Hag⟩
  isplitl [Ha Hl]
  · iframe Ha
    isplitl [Hl]
    · iexists F; iframe Hl; ipureintro; exact HI
    isplitr
    · ipureintro; exact Hd
    · iexact Hinv
  iframe Hc
  isplitr
  · ipureintro; exact fun n h => Hag.1 n trivial h
  · ipureintro; exact fun n h hn => HI n hn (Hag.2 n trivial h hn)

/-- **The batch lock's side agrees with an idle part**, which stays idle. -/
theorem rbSide_agree_in (γ : BNames) (P : BParams) (r : GMap GoString BktData)
    (S : GoString → Prop) (r' : GMap GoString BktData) {I : GoString → Prop} :
    iprop(rbSide (GF := GF) γ P r I ∗ rbOwnIn γ S r') ⊢
      iprop(rbSide γ P r I ∗ rbOwnIn γ S r' ∗ ⌜∀ n, S n → r.lookup n = r'.lookup n⌝) := by
  iintro H
  icases rbSide_agree_inI γ P r S r' $$ H with ⟨Hs, Hc, %Ha, -⟩
  iframe Hs Hc
  ipureintro; exact Ha

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
  · simp only [Bool.false_eq_true, ↓reduceIte]
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

/-! ### The readers' contents of the tracked buckets (A1 of `auth-schema-srv`, D3, 2026-11-17)

`readTx.mu`'s half of each tracked bucket's readers' element (`rbrHalves`, inside `clnPart`) and the
batch lock's side (`rbrSide`, sealed): its authorities, the other half of an unclaimed bucket's element,
and a claimed bucket's claim half with the other half of its `γ.rbk` element. The laws: allocation, the
split of `readTx.mu`'s half among the readers, a write's step (a claimed bucket cannot be written through
an unclaimed part: three halves of its `γ.rbk` element) and the readers' state's step (the write-back,
a commit: an unclaimed bucket's element updated with both halves, a claimed one untouched by the
session and so unchanged). -/

/-- **Allocation** of a fresh ghost map over the names `D`, at `v` (any value type). -/
private theorem gEls_alloc_from {V : Type} [Pos.Countable V] (D : GMap GoString Unit) (v : GoString → V)
    (g : GName) :
    ∀ M : GMap GoString V, (∀ k, D.lookup k ≠ none → M.lookup k = none) →
      ghostMapAuth (GF := GF) g 1 M ⊢
        |==> ∃ M' : GMap GoString V, ghostMapAuth g 1 M' ∗
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

/-- **Allocation of the readers' contents** over the names `D` (A6.2): every bucket's readers' element at
`rv`'s contents, in a half (`readTx.mu`'s) and two quarters (the batch lock's, the claim invariant's). -/
theorem rbr_alloc (P : BParams) (D : GMap GoString Unit) (rv : RView) :
    ⊢ |==> ∃ gr : GName,
      (∃ M : GMap GoString BktData, ghostMapAuth (GF := GF) gr 1 M) ∗
      ([∗map] n ↦ _u ∈ D, ghostMapElem (GF := GF) gr n (DFrac.own (1 : Qp).half) (rvBkt P rv n)) ∗
      ([∗map] n ↦ _u ∈ D, ghostMapElem (GF := GF) gr n (DFrac.own (1 : Qp).half.half) (rvBkt P rv n)) ∗
      ([∗map] n ↦ _u ∈ D, ghostMapElem (GF := GF) gr n (DFrac.own (1 : Qp).half.half) (rvBkt P rv n)) := by
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := BktData) with ⟨%gr, Har⟩
  imod gEls_alloc_from D (rvBkt P rv) gr ∅ (fun _ _ => rfl) $$ Har with ⟨%Mr, Har, Hr⟩
  imodintro
  iexists gr
  isplitl [Har]
  · iexists Mr; iexact Har
  ihave Hr := BigSepM.bigSepM_mono (Φ := fun n (_ : Unit) =>
      ghostMapElem (GF := GF) gr n (DFrac.own 1) (rvBkt P rv n))
    (Ψ := fun n (_ : Unit) => iprop(ghostMapElem (GF := GF) gr n (DFrac.own (1 : Qp).half) (rvBkt P rv n) ∗
      ghostMapElem gr n (DFrac.own (1 : Qp).half.half) (rvBkt P rv n) ∗
      ghostMapElem gr n (DFrac.own (1 : Qp).half.half) (rvBkt P rv n)))
    (fun {k} {_} _ => by
      iintro H
      icases (ghostMapElem_halves gr k (rvBkt P rv k)).1 $$ H with ⟨H1, H2⟩
      ihave H2 := gme_frac gr k _ _ _ q4_add.symm $$ H2
      icases gme_split gr k _ _ _ $$ H2 with ⟨H2, H3⟩
      iframe) $$ Hr
  iapply (map_zip3 D _ _ _).2 $$ Hr

/-- **Allocation of the claim elements** over the names `D` (A6.2): every bucket unclaimed, its element at
`none` in two halves (the claim invariant's, the claim token's). -/
theorem rbc_alloc (D : GMap GoString Unit) :
    ⊢ |==> ∃ gc : GName,
      (∃ M : GMap GoString (Option (Option BktData × Bool)), ghostMapAuth (GF := GF) gc 1 M) ∗
      ([∗map] n ↦ _u ∈ D, ghostMapElem (GF := GF) gc n (DFrac.own (1 : Qp).half)
        (none : Option (Option BktData × Bool))) ∗
      ([∗map] n ↦ _u ∈ D, ghostMapElem (GF := GF) gc n (DFrac.own (1 : Qp).half)
        (none : Option (Option BktData × Bool))) := by
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Option (Option BktData × Bool))
    with ⟨%gc, Hac⟩
  imod gEls_alloc_from D (fun _ => (none : Option (Option BktData × Bool))) gc ∅ (fun _ _ => rfl)
    $$ Hac with ⟨%Mc, Hac, Hc⟩
  imodintro
  iexists gc
  isplitl [Hac]
  · iexists Mc; iexact Hac
  iapply (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
  iapply BigSepM.bigSepM_mono (fun {k} {_} _ => (ghostMapElem_halves gc k _).1) $$ Hc

/-- **The batch lock's side at the start** (A6.2): its quarters of the readers' elements at the state's
readers' contents. -/
theorem rbrSide_init (γ : BNames) (P : BParams) (st : BSess)
    (hD : ∀ n, γ.rbD.lookup n ≠ none → P.RB n = true) (hcw : ∀ n, st.cw n = false) :
    iprop((∃ M : GMap GoString BktData, ghostMapAuth (GF := GF) γ.rbr 1 M) ∗
      ([∗map] n ↦ _u ∈ γ.rbD, ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half.half)
          (rvBkt P (st.C, st.R) n))) ⊢
      rbrSide γ P st := by
  unfold rbrSide
  iintro ⟨Har, Hs⟩
  iframe Har
  isplitr
  · ipureintro; exact hD
  isplitr
  · ipureintro; exact fun _ _ => hcw
  unfold rbrOne
  iexact Hs

/-- **The claim invariant at the start** (A6.2): every tracked bucket unclaimed, with half of its `γ.rbk`
element at `v`, a quarter of its readers' element at `w`, half of its claim element at `none`, the readers
seeing the writer's contents where no write is pending. -/
theorem rbClaimInv_init (γ : BNames) (P : BParams) (v : GoString → Option BktData × Bool)
    (w : GoString → BktData)
    (hbt : ∀ n i, P.BT.lookup n = some i → P.RB n = true → γ.rbD.lookup n ≠ none)
    (hL : ∀ n, γ.rbD.lookup n ≠ none → (v n).2 = false → w n = (v n).1.getD ∅) :
    iprop((∃ M : GMap GoString (Option (Option BktData × Bool)), ghostMapAuth (GF := GF) γ.rbc 1 M) ∗
      ([∗map] n ↦ _u ∈ γ.rbD, rbElem (GF := GF) γ n (1 : Qp).half (v n)) ∗
      ([∗map] n ↦ _u ∈ γ.rbD, ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half.half) (w n)) ∗
      ([∗map] n ↦ _u ∈ γ.rbD, ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half)
        (none : Option (Option BktData × Bool)))) ⊢
      rbClaimInv γ P := by
  unfold rbClaimInv
  iintro ⟨⟨%M, Hac⟩, Hk, Hr, Hc⟩
  iexists M, (fun _ => false)
  iframe Hac
  isplitr
  · ipureintro; exact hbt
  ihave Hz := (map_zip3 γ.rbD _ _ _).1 $$ [$Hk $Hr $Hc]
  iapply BigSepM.bigSepM_mono (fun {k} {x} hk => ?_) $$ Hz
  have hk' : γ.rbD.lookup k ≠ none := by
    have h1 : γ.rbD.lookup k = some x := hk
    rw [h1]; simp
  iintro ⟨Hk, Hr, Hc⟩
  iapply (rbClaimOne_U γ k _ rfl).2
  iunfold rbClaimU
  iexists (v k).1, (v k).2, w k
  iframe
  ipureintro; exact hL k hk'

/-- **The claim tokens from the claim invariant's other halves** (A6.2). -/
theorem rbClaimToks_init (γ : BNames) (P : BParams) :
    iprop(inv rbClaimN (rbClaimInv (GF := GF) γ P) ∗
      ([∗map] n ↦ _u ∈ γ.rbD, ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half)
        (none : Option (Option BktData × Bool)))) ⊢ rbClaimToks γ P (fun _ => True) := by
  unfold rbClaimToks
  iintro ⟨#Hi, Hc⟩
  iframe Hi
  iapply BigSepM.bigSepM_mono (fun {k} {_} _ => by simp only [if_pos trivial]; exact .rfl) $$ Hc

/-- `readTx.mu`'s share of the readers' contents splits among the readers. -/
theorem rbrHalves_frac (γ : BNames) (P : BParams) (rv : RView) (q1 q2 : Qp) :
    rbrHalves (GF := GF) γ P (q1 + q2) rv ⊣⊢ iprop(rbrHalves γ P q1 rv ∗ rbrHalves γ P q2 rv) := by
  unfold rbrHalves
  have h : ∀ k, ghostMapElem (GF := GF) γ.rbr k (DFrac.own (q1 + q2).half) (rvBkt P rv k) ⊣⊢
      iprop(ghostMapElem γ.rbr k (DFrac.own q1.half) (rvBkt P rv k) ∗
        ghostMapElem γ.rbr k (DFrac.own q2.half) (rvBkt P rv k)) := by
    intro k
    rw [Qp_half_add]
    exact (ghostMapElem_fractional k γ.rbr (rvBkt P rv k)).fractional _ _
  constructor
  · exact (BigSepM.bigSepM_mono fun {k} {_} _ => (h k).1).trans
      (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
  · exact (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
      (BigSepM.bigSepM_mono fun {k} {_} _ => (h k).2)

/-- One element of a family. -/
private theorem rbEls_elem (γ : BNames) (S : GoString → Prop) (q : Qp)
    (v : GoString → Option BktData × Bool) (n : GoString) (hS : S n) (hn : γ.rbD.lookup n ≠ none) :
    rbEls (GF := GF) γ S q v ⊢ rbElem γ n q (v n) := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hn
  unfold rbEls
  iintro H
  icases (BigSepM.bigSepM_lookup_acc
    (Φ := fun k (_ : Unit) => if S k then rbElem (GF := GF) γ k q (v k) else iprop(True))
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ H with ⟨H, -⟩
  ihave H := (show (if S n then rbElem (GF := GF) γ n q (v n) else iprop(True)) ⊢
    rbElem γ n q (v n) by simp only [if_pos hS]; exact .rfl) $$ H
  iexact H

/-- One bucket's side, congruence (its readers' state kept). -/
private theorem rbrOne_congr (γ : BNames) (P : BParams) (st st' : BSess) (n : GoString)
    (hC : st'.C = st.C) (hR : st'.R = st.R) :
    rbrOne (GF := GF) γ P st n ⊢ rbrOne γ P st' n := by
  unfold rbrOne
  rw [hC, hR]

/-- **A step that keeps the readers' state keeps the batch lock's side** (A6.2: whatever the buckets'
kinds and contents). -/
theorem rbrSide_congr (γ : BNames) (P : BParams) (st st' : BSess) (hC : st'.C = st.C)
    (hR : st'.R = st.R) (c : Bool) (hok : cwOk c st → cwOk c st') :
    rbrSide (GF := GF) γ P st c ⊢ rbrSide γ P st' c := by
  unfold rbrSide
  iintro ⟨Har, %Hd, %Hcw, Hb⟩
  iframe Har
  isplitr
  · ipureintro; exact Hd
  isplitr
  · ipureintro; exact hok Hcw
  iapply BigSepM.bigSepM_mono (fun {k} {_} _ => rbrOne_congr γ P st st' k hC hR) $$ Hb

/-- **A session's write to bucket `m` through its (unclaimed) part keeps the batch lock's side** (the
readers' state kept). -/
theorem rbrSide_write (γ : BNames) (P : BParams) (r : GMap GoString BktData) (m : GoString) (S : Data)
    (st st' : BSess) (hC : st'.C = st.C) (hR : st'.R = st.R)
    (_hO : ∀ n, n ≠ m → st'.tk n = st.tk n ∧ (rbData P st'.S).lookup n = (rbData P st.S).lookup n)
    (hcw : st'.cw = st.cw) (hhw : st'.cnt.hw = st.cnt.hw) (c : Bool := false) {I : GoString → Prop} :
    iprop(rbSide (GF := GF) γ P r I ∗ rbPart γ (fun k => k = m) (rbData P S) ∗ rbrSide γ P st c) ⊢
      iprop(rbSide γ P r I ∗ rbPart γ (fun k => k = m) (rbData P S) ∗ rbrSide γ P st' c) := by
  have hok : cwOk c st → cwOk c st' := fun h h1 h2 => by rw [hcw]; exact h h1 (hhw ▸ h2)
  iintro ⟨Hs, Hp, Hr⟩
  iframe Hs Hp
  iapply rbrSide_congr γ P st st' hC hR c hok $$ Hr

/-- **Update each element** of a family over `D`, threading the authority. -/
private theorem els_upd_each {V : Type} [Pos.Countable V] (g : GName) (Φ Ψ : GoString → IProp GF)
    (D : GMap GoString Unit) :
    (∀ n (M : GMap GoString V), D.lookup n ≠ none →
      iprop(ghostMapAuth (GF := GF) g 1 M ∗ Φ n) ⊢
        |==> ∃ M' : GMap GoString V, ghostMapAuth g 1 M' ∗ Ψ n) →
    ∀ M : GMap GoString V, iprop(ghostMapAuth (GF := GF) g 1 M ∗ ([∗map] n ↦ _u ∈ D, Φ n)) ⊢
      |==> ∃ M' : GMap GoString V, ghostMapAuth g 1 M' ∗ ([∗map] n ↦ _u ∈ D, Ψ n) := by
  induction D using Std.LawfulFiniteMap.induction_on with
  | hemp =>
    intro _ M
    iintro ⟨Ha, -⟩
    imodintro
    iexists M
    isplitl [Ha]
    · iexact Ha
    · rw [BigSepM.bigSepM_empty.to_eq]; iempintro
  | hins i x D hi IH =>
    intro h M
    rw [(BigSepM.bigSepM_insert (Φ := fun n (_ : Unit) => Φ n) hi).to_eq,
      (BigSepM.bigSepM_insert (Φ := fun n (_ : Unit) => Ψ n) hi).to_eq]
    iintro ⟨Ha, Hi, Hs⟩
    imod h i M (by show (if i = i then some x else D.lookup i) ≠ none; simp) $$ [Ha Hi]
      with ⟨%M1, Ha, Hi⟩
    · iframe
    imod IH (fun n M' hn => h n M' (by
        show (if i = n then some x else D.lookup n) ≠ none
        by_cases e : i = n
        · simp [e]
        · rw [if_neg e]; exact hn)) M1 $$ [Ha Hs] with ⟨%M2, Ha, Hs⟩
    · iframe
    imodintro
    iexists M2
    iframe

/-- **The batch lock's halves of what it tracks, congruence** (the writer's contents, the readers'
state and every tracked bucket's kind kept). -/
theorem trkSide_congr (γ : BNames) (P : BParams) (st st' : BSess) (hS : st'.S = st.S)
    (hC : st'.C = st.C) (hR : st'.R = st.R) (hT : ∀ n, P.RB n = true → st'.tk n = st.tk n)
    (hcw : st'.cw = st.cw) (c : Bool) (hok : cwOk c st → cwOk c st') :
    trkSide (GF := GF) γ P st c ⊢ trkSide γ P st' c := by
  unfold trkSide
  rw [hS, tkI_congr (fun n hn => ⟨hT n hn, by rw [hcw]⟩)]
  iintro ⟨Hh, Hr⟩
  iframe Hh
  iapply rbrSide_congr γ P st st' hC hR c hok $$ Hr

/-- The batch lock's side's mode fact (A1.4): no claimed writes in the client-facing mode outside the
hook's window. -/
theorem trkSide_cw (γ : BNames) (P : BParams) (st : BSess) (c : Bool) :
    trkSide (GF := GF) γ P st c ⊢ iprop(trkSide γ P st c ∗ ⌜cwOk c st⌝) := by
  unfold trkSide rbrSide
  iintro ⟨Hh, Har, %Hd, %Hcw, Hb⟩
  iframe Hh Har Hb
  ipureintro
  exact ⟨⟨Hd, Hcw⟩, Hcw⟩

/-! ### Writes through a claimed part (A1.4 of `auth-schema-srv`, 2026-11-17) -/

open Classical in
/-- One element of a claimed part's family, with the family rebuilt at new values elsewhere unchanged. -/
private theorem rbcEls_acc (γ : BNames) (S : GoString → Prop) (v : GoString → Option (Option BktData × Bool))
    (n : GoString) (hS : S n) (hn : γ.rbD.lookup n ≠ none) :
    ([∗map] k ↦ _u ∈ γ.rbD, (if S k then ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half) (v k)
      else iprop(True))) ⊢
      iprop(ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half) (v n) ∗
        (∀ v' : GoString → Option (Option BktData × Bool), ⌜∀ k, S k → k ≠ n → v' k = v k⌝ -∗
          ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half) (v' n) -∗
          [∗map] k ↦ _u ∈ γ.rbD, (if S k then ghostMapElem γ.rbc k (DFrac.own (1 : Qp).half) (v' k)
            else iprop(True)))) := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hn
  iintro H
  icases (BigSepM.bigSepM_lookup_acc_impl (Φ := fun k (_ : Unit) => if S k then
      ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half) (v k) else iprop(True))
    (m := γ.rbD) (i := n) (x := u) hu) $$ H with ⟨Hn, Hw⟩
  ihave Hn := (show (if S n then ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half) (v n)
      else iprop(True)) ⊢ ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half) (v n) by
    simp only [if_pos hS]; exact .rfl) $$ Hn
  iframe Hn
  iintro %v' %hv' Hn'
  ispecialize Hw $$ %(fun k (_ : Unit) => if S k then
    ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half) (v' k) else iprop(True))
  iapply Hw
  · iintro !> %k %x %_ %hk H
    iapply (show (if S k then ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half) (v k)
        else iprop(True)) ⊢ (if S k then ghostMapElem γ.rbc k (DFrac.own (1 : Qp).half) (v' k)
        else iprop(True)) by
      by_cases hSk : S k
      · simp only [if_pos hSk, hv' k hSk hk]; exact .rfl
      · simp only [if_neg hSk]; exact .rfl) $$ H
  · iapply (show ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half) (v' n) ⊢
        (if S n then ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half) (v' n) else iprop(True)) by
      simp only [if_pos hS]; exact .rfl) $$ Hn'

/-- **A claimed session's write to the claimed bucket `m`** (A1.4; A6.2): the claim element (the part's half
and the claim invariant's) and the bucket's `γ.rbk` element (the invariant's three quarters and the batch
lock's quarter) move to the new contents, the claim element's flag set and the `γ.rbk` flag left clear (the
batch lock records the claimed write in `st.cw`: `hIm`); the readers' contents are untouched (they move at
`Unlock`, through the client's quarters, A1.5). -/
theorem rbrSide_writeR (γ : BNames) (P : BParams) (m : GoString) (st st' : BSess)
    (hC : st'.C = st.C) (hR : st'.R = st.R)
    (hO : ∀ n, n ≠ m → st'.tk n = st.tk n ∧ st'.S.lookup n = st.S.lookup n ∧ st'.cw n = st.cw n)
    (I I' : GoString → Prop) (hI : ∀ n, n ≠ m → I n → I' n) (hIm : I m → I' m)
    (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rbSide (GF := GF) γ P (rbData P st.S) I ∗ rbPutR γ P m st.S ∗ rbrSide γ P st true) ⊢
      |={E}=> iprop(rbSide γ P (rbData P st'.S) I' ∗ rbPutR γ P m st'.S ∗ rbrSide γ P st' true) := by
  have hO' : ∀ n, n ≠ m → (rbData P st'.S).lookup n = (rbData P st.S).lookup n := by
    intro n hn; rw [rbData_lookup, rbData_lookup, (hO n hn).2.1]
  unfold rbPutR rbPartR rbPartRF rbSide
  iintro ⟨⟨⟨%M, Ha⟩, ⟨%FL, Hl, %HI⟩, %Hd, #Hinv⟩, ⟨%hRB, %F, %Hpd, Hp⟩, Hr⟩
  have hmd : γ.rbD.lookup m ≠ none := Hpd m rfl
  icases rbcEls_acc γ (fun k => k = m) (fun k => some ((rbData P st.S).lookup k, F k)) m rfl hmd $$ Hp
    with ⟨Hpm, Hp⟩
  icases rbPartF_split_compl γ (fun k => k = m) (rbData P st.S) FL $$ Hl with ⟨Hln, Hlo⟩
  ihave Hln := (rbPartF_one γ m _ FL hmd).1 $$ Hln
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  icases mapAcc γ.rbD (fun k => rbClaimOne (GF := GF) γ k (Cl k)) (fun k => rbClaimOne (GF := GF) γ k (Cl k))
    m hmd (fun _ _ => .rfl) $$ Hm with ⟨Hn, Hm⟩
  cases hcl : Cl m
  · ihave Hn := (rbClaimOne_U γ m _ rfl).1 $$ Hn
    iunfold rbClaimU at Hn
    icases Hn with ⟨%c, %f, %v, -, -, Hcn, -⟩
    ihave %Hv := ghostMapElem_agree m γ.rbc _ _ _ _ $$ Hcn Hpm
    cases Hv
  · ihave Hn := (rbClaimOne_C γ m _ rfl).1 $$ Hn
    iunfold rbClaimC at Hn
    icases Hn with ⟨%c, %w, Hk, Hcn, -⟩
    icases gme_join γ.rbc m _ _ _ _ $$ [$Hcn $Hpm] with ⟨Hc, -⟩
    ihave Hc := gme_frac γ.rbc m _ 1 _ q2_add $$ Hc
    imod ghost_map_update (some ((rbData P st'.S).lookup m, true) : Option (Option BktData × Bool))
      $$ Hac Hc with ⟨Hac, Hc⟩
    ihave Hc := gme_frac γ.rbc m 1 _ _ q2_add.symm $$ Hc
    icases gme_split γ.rbc m _ _ _ $$ Hc with ⟨Hc1, Hc2⟩
    icases gme_join γ.rbk m _ _ _ _ $$ [$Hk $Hln] with ⟨Hw, %Hke⟩
    have hFL : FL m = false := (congrArg Prod.snd Hke).symm
    ihave Hw := gme_frac γ.rbk m _ 1 _ q34_add $$ Hw
    imod ghost_map_update (((rbData P st'.S).lookup m, false) : Option BktData × Bool) $$ Ha Hw
      with ⟨Ha, Hw⟩
    ihave Hw := gme_frac γ.rbk m 1 _ _ q34_add.symm $$ Hw
    icases gme_split γ.rbk m _ _ _ $$ Hw with ⟨Hk, Hln⟩
    imod Hclose $$ [Hac Hm Hk Hc1] with -
    · inext
      iunfold rbClaimInv
      iexists _, Cl
      iframe Hac
      isplitr
      · ipureintro; exact Hbt
      iapply Hm
      iapply (rbClaimOne_C γ m _ rfl).2
      iunfold rbClaimC
      iexists (rbData P st'.S).lookup m, ((rbData P st'.S).lookup m, true)
      iframe Hk Hc1
      ipureintro; rfl
    imodintro
    isplitl [Ha Hln Hlo]
    · isplitl [Ha]
      · iexists _; iexact Ha
      isplitl [Hln Hlo]
      · iexists FL
        isplitl [Hln Hlo]
        · iapply rbPartF_join_same γ (fun k => k = m) (rbData P st'.S) FL
          isplitl [Hln]
          · iapply (rbPartF_one γ m (rbData P st'.S) FL hmd).2
            rw [hFL]
            iexact Hln
          iapply (rbPartF_congr γ (fun k => ¬ k = m) (rbData P st.S) (rbData P st'.S) FL FL
            (fun n hn => (hO' n hn).symm) (fun _ _ _ => rfl)).1 $$ Hlo
        · ipureintro
          intro n hn hf
          by_cases e : n = m
          · subst e; exact hIm (HI n hn hf)
          · exact hI n e (HI n hn hf)
      isplitr
      · ipureintro; exact Hd
      · iexact Hinv
    isplitl [Hp Hc2]
    · isplitr
      · ipureintro; exact hRB
      iexists (fun _ => true)
      isplitr
      · ipureintro; exact Hpd
      iapply Hp $$ %(fun k => some ((rbData P st'.S).lookup k, true)) %(fun k hk hk' => absurd hk hk')
      iexact Hc2
    · iapply rbrSide_congr γ P st st' hC hR true (fun _ h => by cases h) $$ Hr

/-- **A session's write to bucket `m` through a part of either kind** (`k`: claimed; A1.4), in the mode
`c` (a claimed part only in a claimed session): the batch lock's sides and the part move to the new
contents. -/
theorem rbWrite (γ : BNames) (P : BParams) (st st' : BSess) (m : GoString) (k c : Bool)
    (hC : st'.C = st.C) (hR : st'.R = st.R) (hhw : st'.cnt.hw = st.cnt.hw)
    (hBT : P.RB m = true → ∃ i, P.BT.lookup m = some i)
    (hB : P.RB m = false → rbData P st'.S = rbData P st.S)
    (hO : ∀ n, n ≠ m → st'.tk n = st.tk n ∧ st'.S.lookup n = st.S.lookup n ∧ st'.cw n = st.cw n)
    (hcw : k = false → st'.cw m = st.cw m)
    (hcwT : k = true → st.tk m = .idle ∨ st.cw m = true → st'.tk m = .idle ∨ st'.cw m = true)
    (hkc : k = true → c = true) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rbSide (GF := GF) γ P (rbData P st.S) (tkI P st) ∗ rbPut γ P m st.S k ∗ rbrSide γ P st c) ⊢
      |={E}=> iprop(rbSide γ P (rbData P st'.S) (tkI P st') ∗ rbPut γ P m st'.S k ∗ rbrSide γ P st' c) := by
  have hO' : ∀ n, n ≠ m → (rbData P st'.S).lookup n = (rbData P st.S).lookup n := by
    intro n hn; rw [rbData_lookup, rbData_lookup, (hO n hn).2.1]
  have hI : ∀ n, n ≠ m → tkI P st n → tkI P st' n := fun n hn h hRB => by
    rw [(hO n hn).1, (hO n hn).2.2]; exact h hRB
  cases k
  · have hcwe : st'.cw = st.cw := funext fun n => by
      by_cases h : n = m
      · subst h; exact hcw rfl
      · exact (hO n h).2.2
    unfold rbPut
    cases hb : P.RB m
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hB hb]
      iintro ⟨Hs, -, Hr⟩
      ihave Hs := rbSide_mono γ P _ _ (tkI P st') (fun n h => by
        by_cases e : n = m
        · subst e; intro h'; rw [hb] at h'; cases h'
        · exact hI n e h) $$ Hs
      iframe Hs
      isplitr
      · imodintro; itrivial
      imodintro
      iapply rbrSide_congr γ P st st' hC hR c
        (fun h h1 h2 => by rw [hcwe]; exact h h1 (by rw [← hhw]; exact h2)) $$ Hr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iintro ⟨Hs, Hp, Hr⟩
      icases rbrSide_write γ P (rbData P st.S) m st.S st st' hC hR
        (fun n hn => ⟨(hO n hn).1, hO' n hn⟩) hcwe hhw c $$ [$Hs $Hp $Hr] with ⟨Hs, Hp, Hr⟩
      imod rbSide_put γ P (rbData P st.S) (rbData P st'.S) m (hBT hb) hb hO' _ _ hI E hE $$ [$Hs $Hp]
        with ⟨Hs, Hp⟩
      imodintro
      iframe
  · obtain rfl := hkc rfl
    unfold rbPut
    simp only [↓reduceIte]
    iapply rbrSide_writeR γ P m st st' hC hR hO _ _ hI (fun h hRB => hcwT rfl (h hRB)) E hE

end tracked

end backend
end EtcdGrove
end Perennial
