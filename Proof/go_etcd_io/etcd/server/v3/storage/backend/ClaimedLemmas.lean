/-
**Claimed buckets at `Unlock`** (A1.5 of `auth-schema-srv`, D5 of `notes/auth-schema-srv-a1-scope.md`,
2026-11-17). A client that claimed tracked buckets `Sc` holds their readers' halves (`rbRd`); `Unlock` moves
the readers' contents of a bucket written through a claimed part (`st.cw`) at the write-back and at the
commit, both under `readTx`'s write lock, so it needs the client's halves there: the client hands it an
**accessor** (`rbAcc`), run at each step, that lends the halves and takes them back at the new contents,
which the client may count on to be a move `unlockOk` allows (D2, by kind: the writer's contents; a bucket
untouched or only deleted from kept; a bucket both put into and deleted from at the write-back's
intermediate contents). The laws: the batch lock's side and `readTx.mu`'s halves step together with the
client's (`trkSide_updR`, the update wand `rtRes_wb_close*`/`rtRes_cm_close` take), the mode of the batch
lock's side (`trkSide_mode`), and the claimed part made idle at `Unlock`'s end (`rbPartR_idle`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas
import all Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
import all Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- **The readers' contents a claimed bucket `n` may move to at `Unlock` of the session state `st`**,
from `old` (A1.5, D2 by kind): the writer's contents; or, for a bucket untouched or only deleted from in
the session, `old` (the write-back leaves it; the commit moves it to the writer's); or, for a bucket both
put into and deleted from (`mix`), the write-back's intermediate contents (the session's puts over the old
readers' state, its deletes not yet committed). -/
def unlockOk (P : BParams) (st : BSess) (n : GoString) (old new : BktData) : Prop :=
  new = bktOf st.S n ∨ ((st.tk n = .idle ∨ st.tk n = .del) ∧ new = old) ∨
    (st.tk n = .mix ∧ new = rvBkt P (st.C, writebackR st.W st.R) n)

/-- Two contents with one tracked data read one tracked bucket alike. -/
theorem bktOf_rb {P : BParams} {S S' : Data} {n : GoString} (h : rbData P S' = rbData P S)
    (hn : P.RB n = true) : bktOf S' n = bktOf S n := by
  have := congrArg (fun m => GMap.lookup m n) h
  simp only [rbData_lookup, hn, ↓reduceIte] at this
  unfold bktOf; rw [this]

/-- **The write-back moves a claimed bucket as `Unlock`'s client may count on** (`unlockOk`, by kind). -/
theorem unlockOk_wb {P : BParams} {st : BSess} {Sc : List GoString} (h : trkOk P st st.tk) :
    ∀ n, n ∈ Sc → P.RB n = true →
      unlockOk P st n (rvBkt P (st.C, st.R) n) (rvBkt P (st.C, writebackR st.W st.R) n) := by
  intro n _ hn
  unfold unlockOk
  cases htk : st.tk n
  · exact Or.inr (Or.inl ⟨Or.inl rfl, rvBkt_wb_keep h hn (Or.inl htk)⟩)
  · exact Or.inl (rvBkt_wb_put h hn htk)
  · exact Or.inr (Or.inl ⟨Or.inr rfl, rvBkt_wb_keep h hn (Or.inr htk)⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- The session state with no claimed write recorded (for a state whose tracked buckets are all idle). -/
def BSess.clrCw (st : BSess) : BSess := { st with cw := fun _ => false }

section claimed
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

open Classical

/-- **A claiming client's accessor of its readers' halves of the buckets `Sc`** (A1.5, D5), with its
resource `Rr`: from `Rr`, the halves at their current contents `old`, and back to `Rr` given the halves
at any contents `v` that move each bucket as `ok` allows. Persistent: `Unlock` runs it at the write-back
and again at the commit, at mask `⊤` (no backend invariant open). -/
def rbAcc (γ : BNames) (Sc : List GoString) (ok : GoString → BktData → BktData → Prop)
    (Rr : IProp GF) : IProp GF :=
  iprop(□ (Rr -∗ |={⊤}=> ∃ old : GoString → BktData,
    ([∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (old n)) ∗
    ∀ v : GoString → BktData, ⌜∀ n, n ∈ Sc → ok n (old n) (v n)⌝ -∗
      ([∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (v n)) -∗ |={⊤}=> Rr))

instance rbAcc_persistent (γ : BNames) (Sc : List GoString) (ok : GoString → BktData → BktData → Prop)
    (Rr : IProp GF) : Persistent (rbAcc γ Sc ok Rr) := by
  unfold rbAcc; infer_instance

/-- The accessor of no bucket (a caller that claimed none). -/
theorem rbAcc_nil (γ : BNames) (ok : GoString → BktData → BktData → Prop) (Rr : IProp GF) :
    ⊢ rbAcc γ [] ok Rr := by
  unfold rbAcc
  iintro !> HR
  imodintro
  iexists (fun _ => (∅ : BktData))
  isplitr
  · exact BigSepL.bigSepL_nil_intro
  · iintro %v %_ -
    imodintro
    iexact HR

/-- An accessor for the moves `ok` is one for fewer moves `ok'`. -/
theorem rbAcc_mono (γ : BNames) (Sc : List GoString) (ok ok' : GoString → BktData → BktData → Prop)
    (Rr : IProp GF) (h : ∀ n o v, n ∈ Sc → ok' n o v → ok n o v) :
    rbAcc γ Sc ok Rr ⊢ rbAcc γ Sc ok' Rr := by
  unfold rbAcc
  iintro #H !> HR
  imod H $$ HR with ⟨%old, Hh, Hk⟩
  imodintro
  iexists old
  iframe Hh
  iintro %v %hv Hv
  iapply Hk $$ %v %(fun n hn => h n _ _ hn (hv n hn)) Hv

/-! ### The client's halves as a family over the tracked names -/

/-- One entry of a family over `D`, the family rebuilt with another family equal elsewhere. -/
private theorem mapIf_acc (D : GMap GoString Unit) (Φ Ψ : GoString → IProp GF) (n : GoString)
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

private theorem mapIf_nil (D : GMap GoString Unit) (Φ : GoString → IProp GF) :
    ⊢ [∗map] n ↦ _u ∈ D, (if n ∈ ([] : List GoString) then Φ n else iprop(True)) := by
  refine BigSepM.bigSepM_intro (P := iprop(emp)) fun {k} {_} _ => ?_
  rw [if_neg (by simp)]
  iintro -
  itrivial

private theorem mapIf_cons_ne (Sc : List GoString) (m k : GoString) (hk : k ≠ m) (Φ : GoString → IProp GF) :
    (if k ∈ m :: Sc then Φ k else iprop(True)) = (if k ∈ Sc then Φ k else iprop(True)) := by
  have : (k ∈ m :: Sc) ↔ k ∈ Sc := by simp [hk]
  by_cases h : k ∈ Sc
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

/-- The client's halves of the buckets `Sc`, as a family over the tracked names. -/
theorem rbRdL_map (γ : BNames) (f : GoString → BktData) (q : Qp) (Sc : List GoString)
    (hnd : Sc.Nodup) :
    ([∗list] n ∈ Sc, rbRd (GF := GF) γ n q (f n)) ⊢
      iprop(⌜∀ n, n ∈ Sc → γ.rbD.lookup n ≠ none⌝ ∗
        [∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own q) (f n)
          else iprop(True))) := by
  induction Sc with
  | nil =>
    iintro -
    isplitr
    · ipureintro; intro n h; cases h
    · iapply mapIf_nil
  | cons m Sc ih =>
    have hm : m ∉ Sc := (List.nodup_cons.1 hnd).1
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Hm, Hs⟩
    iunfold rbRd at Hm
    icases Hm with ⟨%Hmd, Hm⟩
    icases ih (List.nodup_cons.1 hnd).2 $$ Hs with ⟨%Hd, Hs⟩
    icases mapIf_acc γ.rbD
      (fun k => if k ∈ Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q) (f k) else iprop(True))
      (fun k => if k ∈ m :: Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q) (f k) else iprop(True))
      m Hmd (fun k hk => by
        rw [mapIf_cons_ne Sc m k hk (fun k => ghostMapElem (GF := GF) γ.rbr k (DFrac.own q) (f k))]) $$ Hs with ⟨-, Hw⟩
    isplitr
    · ipureintro
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact Hmd
      · exact Hd k hk
    · iapply Hw
      ihave Hm := (show ghostMapElem (GF := GF) γ.rbr m (DFrac.own q) (f m) ⊢
          (if m ∈ m :: Sc then ghostMapElem γ.rbr m (DFrac.own q) (f m) else iprop(True)) by
        rw [if_pos (by simp)]) $$ Hm
      iexact Hm

/-- Back from the family over the tracked names to the client's halves. -/
theorem rbRdL_of_map (γ : BNames) (f : GoString → BktData) (q : Qp) (Sc : List GoString)
    (hnd : Sc.Nodup) (hd : ∀ n, n ∈ Sc → γ.rbD.lookup n ≠ none) :
    ([∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own q) (f n)
      else iprop(True))) ⊢ [∗list] n ∈ Sc, rbRd γ n q (f n) := by
  induction Sc with
  | nil => exact BigSepL.bigSepL_nil_intro
  | cons m Sc ih =>
    have hm : m ∉ Sc := (List.nodup_cons.1 hnd).1
    have hmd := hd m (by simp)
    iintro H
    icases mapIf_acc γ.rbD
      (fun k => if k ∈ m :: Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q) (f k) else iprop(True))
      (fun k => if k ∈ Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q) (f k) else iprop(True))
      m hmd (fun k hk => by
        rw [mapIf_cons_ne Sc m k hk (fun k => ghostMapElem (GF := GF) γ.rbr k (DFrac.own q) (f k))]) $$ H with ⟨Hm, Hw⟩
    ihave Hs := Hw $$ []
    · rw [if_neg hm]; itrivial
    ihave Hm := (show (if m ∈ m :: Sc then ghostMapElem (GF := GF) γ.rbr m (DFrac.own q) (f m)
        else iprop(True)) ⊢ ghostMapElem γ.rbr m (DFrac.own q) (f m) by
      rw [if_pos (by simp)]) $$ Hm
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hm]
    · iunfold rbRd
      iframe Hm
      ipureintro; exact hmd
    · iapply (ih (List.nodup_cons.1 hnd).2 (fun n hn => hd n (List.mem_cons_of_mem _ hn))) $$ Hs

/-! ### The step of the readers' state with the client's halves -/

/-- One bucket's step of the readers' state, with the client's half of a bucket of `Sc`. -/
private theorem rbrOne_stepR (γ : BNames) (P : BParams) (st st' : BSess) (rv rv' : RView)
    (Sc : List GoString) (old : GoString → BktData) (n : GoString)
    (hrv : rv = (st.C, st.R)) (hrv' : rv' = (st'.C, st'.R))
    (hS : rbData P st'.S = rbData P st.S)
    (hk : st.tk n = .idle → st.cw n = false → st'.tk n = .idle ∧ rvBkt P rv n = rvBkt P rv' n)
    (hcl : st.cw n = true → st'.tk n = .idle ∨ st'.cw n = true)
    (hcwS : st.cw n = true → n ∈ Sc)
    (M : GMap GoString BktData) :
    iprop(ghostMapAuth (GF := GF) γ.rbr 1 M ∗
      (ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv n) ∗ (rbrOne γ P st n ∗
        (if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (old n) else iprop(True))))) ⊢
    |==> ∃ M' : GMap GoString BktData, ghostMapAuth γ.rbr 1 M' ∗
      (ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv' n) ∗ (rbrOne γ P st' n ∗
        ((if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv' n)
          else iprop(True)) ∗ ⌜n ∈ Sc → old n = rvBkt P rv n⌝))) := by
  subst hrv hrv'
  by_cases hin : n ∈ Sc
  · rw [if_pos hin, if_pos hin]
    unfold rbrOne
    iintro ⟨Ha, Hh, ⟨-, Hr⟩ | ⟨%v, Hc, Hk, %Hf⟩, Ho⟩
    · iexfalso
      icases ghostMapElem_combine n γ.rbr _ _ _ _ $$ Hh Hr with ⟨Hh, -⟩
      ihave %Hv := ghostMapElem_valid_2 n γ.rbr _ _ _ _ $$ Hh Ho
      exfalso
      have h := DFrac.valid_own_op Hv.1
      rw [Qp.half_add_half] at h
      exact absurd h (by decide)
    · icombine Hh Ho gives %Hag
      have hag : rvBkt P (st.C, st.R) n = old n := Hag.2
      ihave Hr := (ghostMapElem_halves γ.rbr n (rvBkt P (st.C, st.R) n)).2 $$ [Hh Ho]
      · isplitl [Hh]
        · iexact Hh
        · rw [hag]; iexact Ho
      imod ghost_map_update (rvBkt P (st'.C, st'.R) n) $$ Ha Hr with ⟨Ha, Hr⟩
      icases (ghostMapElem_halves γ.rbr n _).1 $$ Hr with ⟨Hr1, Hr2⟩
      imodintro
      iexists _
      iframe Ha Hr1 Hr2
      isplitl [Hc Hk]
      · iright
        iexists v
        rw [hS]
        iframe Hc Hk
        ipureintro
        refine ⟨?_, Hf.2⟩
        cases hcw : st.cw n
        · exact Or.inl (hk (Hf.1.resolve_right (by rw [hcw]; simp)) hcw).1
        · exact hcl hcw
      · ipureintro; intro _; exact hag.symm
  · rw [if_neg hin, if_neg hin]
    have hcw : st.cw n = false := by
      cases h : st.cw n
      · rfl
      · exact absurd (hcwS h) hin
    unfold rbrOne
    iintro ⟨Ha, Hh, ⟨Hc, Hr⟩ | ⟨%v, Hc, Hk, %Hf⟩, -⟩
    · ihave Hr := (ghostMapElem_halves γ.rbr n (rvBkt P (st.C, st.R) n)).2 $$ [Hh Hr]
      · iframe
      imod ghost_map_update (rvBkt P (st'.C, st'.R) n) $$ Ha Hr with ⟨Ha, Hr⟩
      icases (ghostMapElem_halves γ.rbr n _).1 $$ Hr with ⟨Hr1, Hr2⟩
      imodintro
      iexists _
      iframe Ha Hr1
      isplitl [Hc Hr2]
      · ileft
        iframe
      · isplitr
        · itrivial
        · ipureintro; intro h; exact absurd h hin
    · obtain ⟨h1, h2⟩ := hk (Hf.1.resolve_right (by rw [hcw]; simp)) hcw
      imodintro
      iexists M
      iframe Ha
      rw [← h2, hS]
      iframe Hh
      isplitl [Hc Hk]
      · iright
        iexists v
        iframe
        ipureintro
        exact ⟨Or.inl h1, Hf.2⟩
      · isplitr
        · itrivial
        · ipureintro; intro h; exact absurd h hin

/-- **A step of the readers' state with the client's halves of the claimed buckets `Sc`** (A1.5): every
bucket's readers' element moves to the new readers' contents, an unclaimed one with the batch lock's half,
one of `Sc` with the client's; every other claimed bucket is untouched (no claimed write outside `Sc`). -/
theorem rbrSide_stepR (γ : BNames) (P : BParams) (st st' : BSess) (rv rv' : RView) (c c' : Bool)
    (Sc : List GoString) (old : GoString → BktData)
    (hrv : rv = (st.C, st.R)) (hrv' : rv' = (st'.C, st'.R))
    (hS : rbData P st'.S = rbData P st.S)
    (hk : ∀ n, P.RB n = true → st.tk n = .idle → st.cw n = false →
      st'.tk n = .idle ∧ rvBkt P rv n = rvBkt P rv' n)
    (hcl : ∀ n, st.cw n = true → st'.tk n = .idle ∨ st'.cw n = true)
    (hcwS : ∀ n, st.cw n = true → n ∈ Sc) (hmode : cwOk c' st') :
    iprop(rbrSide (GF := GF) γ P st c ∗ rbrHalves γ P 1 rv ∗
      [∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (old n)
        else iprop(True))) ⊢
      |==> iprop(rbrSide γ P st' c' ∗ rbrHalves γ P 1 rv' ∗
        ([∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then
          ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv' n) else iprop(True))) ∗
        ⌜∀ n, γ.rbD.lookup n ≠ none → n ∈ Sc → old n = rvBkt P rv n⌝ ∗
        ⌜∀ n, γ.rbD.lookup n ≠ none → P.RB n = true⌝) := by
  unfold rbrSide rbrHalves
  iintro ⟨⟨⟨%M, Ha⟩, Hac, %Hd, -, Hs⟩, Hh, Ho⟩
  ihave Hj := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq
    (Φ := fun n (_ : Unit) => rbrOne (GF := GF) γ P st n)
    (Ψ := fun n (_ : Unit) => if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half)
      (old n) else iprop(True)) (m := γ.rbD))).2 $$ [Hs Ho]
  · iframe
  ihave Hj := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq
    (Φ := fun n (_ : Unit) => ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv n))
    (Ψ := fun n (_ : Unit) => iprop(rbrOne (GF := GF) γ P st n ∗
      (if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half) (old n)
        else iprop(True)))) (m := γ.rbD))).2 $$ [Hh Hj]
  · iframe
  imod els_upd_each γ.rbr
    (fun n => iprop(ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv n) ∗
      (rbrOne γ P st n ∗ (if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half)
        (old n) else iprop(True)))))
    (fun n => iprop(ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv' n) ∗
      (rbrOne γ P st' n ∗ ((if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half)
        (rvBkt P rv' n) else iprop(True)) ∗ ⌜n ∈ Sc → old n = rvBkt P rv n⌝)))) γ.rbD
    (fun n M hn => rbrOne_stepR γ P st st' rv rv' Sc old n hrv hrv' hS (hk n (Hd n hn)) (hcl n)
      (hcwS n) M) M
    $$ [Ha Hj] with ⟨%M', Ha, Hj⟩
  · iframe
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hj with ⟨Hh, Hj⟩
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hj with ⟨Hs, Hj⟩
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hj with ⟨Ho, Hp⟩
  ihave %Hall := BigSepM.bigSepM_pure_intro $$ Hp
  imodintro
  iframe Hh Hac Hs Ho
  isplitl [Ha]
  · isplitl [Ha]
    · iexists M'; iexact Ha
    isplitr
    · ipureintro; exact Hd
    · ipureintro; exact hmode
  isplitr
  · ipureintro
    intro n hn hin
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hn
    exact Hall n u hu hin
  · ipureintro; exact Hd

/-- **The update of the readers' contents with a claiming client's accessor** (A1.5, D5), as the wand
`rtRes_wb_close`/`rtRes_cm_close` take: from the batch lock's halves at `st` (mode `c`), the client's
resource `Rr` and its accessor for the buckets `Sc` (holding every claimed write of the session), the
readers' halves at `rv` move to `rv'`, the batch lock's halves to `st'` (mode `c'`), and `Rr` comes back
(the accessor run once, each bucket of `Sc` moved as `ok` allows, `hok`). -/
theorem trkSide_updR (γ : BNames) (P : BParams) (st st' : BSess) (rv rv' : RView) (c c' : Bool)
    (Sc : List GoString) (ok : GoString → BktData → BktData → Prop) (Rr : IProp GF) (hnd : Sc.Nodup)
    (hrv : rv = (st.C, st.R)) (hrv' : rv' = (st'.C, st'.R)) (hS : st'.S = st.S)
    (hk : ∀ n, P.RB n = true → st.tk n = .idle → st.cw n = false →
      st'.tk n = .idle ∧ rvBkt P rv n = rvBkt P rv' n)
    (hcl : ∀ n, st.cw n = true → st'.tk n = .idle ∨ st'.cw n = true)
    (hcwS : ∀ n, st.cw n = true → n ∈ Sc) (hmode : cwOk c' st')
    (hok : ∀ n, n ∈ Sc → P.RB n = true → ok n (rvBkt P rv n) (rvBkt P rv' n)) :
    iprop(trkSide (GF := GF) γ P st c ∗ Rr ∗ rbAcc γ Sc ok Rr) ⊢
      (rbrHalves γ P 1 rv -∗ |={⊤}=> rbrHalves γ P 1 rv' ∗ (trkSide γ P st' c' ∗ Rr)) := by
  unfold trkSide
  iintro ⟨⟨Hh, Hr⟩, HR, #Hacc⟩ Hhv
  iunfold rbAcc at Hacc
  imod Hacc $$ HR with ⟨%old, Hc, Hk⟩
  icases rbRdL_map γ old (1 : Qp).half Sc hnd $$ Hc with ⟨%Hscd, Hc⟩
  imod rbrSide_stepR γ P st st' rv rv' c c' Sc old hrv hrv' (by rw [hS]) hk hcl hcwS hmode
    $$ [Hr Hhv Hc] with ⟨Hr, Hhv, Hc, %Hold, %HRB⟩
  · iframe
  ihave Hc := rbRdL_of_map γ (fun n => rvBkt P rv' n) (1 : Qp).half Sc hnd Hscd $$ Hc
  imod Hk $$ %(fun n => rvBkt P rv' n) %(fun n hn => by
      rw [Hold n (Hscd n hn) hn]; exact hok n hn (HRB n (Hscd n hn))) Hc with HR
  imodintro
  rw [hS]
  iframe

/-! ### The mode of the batch lock's side -/

/-- **The batch lock's side in another mode** (A1.5): the same state, the mode fact of the new mode. -/
theorem trkSide_mode (γ : BNames) (P : BParams) (st : BSess) (c c' : Bool)
    (h : cwOk c st → cwOk c' st) :
    trkSide (GF := GF) γ P st c ⊢ trkSide γ P st c' := by
  unfold trkSide rbrSide
  iintro ⟨Hh, Har, Hac, %Hd, %Hcw, Hb⟩
  iframe Hh Har Hac Hb
  ipureintro
  exact ⟨Hd, h Hcw⟩

/-- **No claimed write recorded, once every tracked bucket is idle** (A1.5: `Unlock` with nothing pending):
the batch lock's side at `st.clrCw`, in the client-facing mode. -/
theorem trkSide_clr (γ : BNames) (P : BParams) (st : BSess) (c : Bool)
    (hT : ∀ n, P.RB n = true → st.tk n = .idle) :
    trkSide (GF := GF) γ P st c ⊢ trkSide γ P st.clrCw := by
  unfold trkSide rbrSide
  iintro ⟨Hh, Har, Hac, %Hd, -, Hb⟩
  isplitl [Hh]
  · iapply (show trkHalf (GF := GF) γ P st.S ⊢ trkHalf γ P st.clrCw.S from .rfl) $$ Hh
  iframe Har Hac
  isplitr
  · ipureintro; exact Hd
  isplitr
  · ipureintro; exact fun _ _ _ => rfl
  iapply BigSepM.bigSepM_mono (fun {k} {x} hk => ?_) $$ Hb
  have hk' : γ.rbD.lookup k ≠ none := by
    have h1 : γ.rbD.lookup k = some x := hk
    rw [h1]; simp
  unfold rbrOne
  iintro (H | ⟨%v, Hc, Hp, %Hf⟩)
  · ileft
    iapply (show iprop(ghostMapElem (GF := GF) γ.rbc k (DFrac.own 1) (none : Option (Option BktData × Bool)) ∗
        ghostMapElem γ.rbr k (DFrac.own (1 : Qp).half) (rvBkt P (st.C, st.R) k)) ⊢
      iprop(ghostMapElem (GF := GF) γ.rbc k (DFrac.own 1) (none : Option (Option BktData × Bool)) ∗
        ghostMapElem γ.rbr k (DFrac.own (1 : Qp).half) (rvBkt P (st.clrCw.C, st.clrCw.R) k)) from .rfl) $$ H
  · iright
    iexists v
    iframe Hc
    isplitl [Hp]
    · iapply (show rbPart (GF := GF) γ (fun m => m = k) (rbData P st.S) ⊢
        rbPart γ (fun m => m = k) (rbData P st.clrCw.S) from .rfl) $$ Hp
    ipureintro
    exact ⟨Or.inl (hT k (Hd k hk')), Hf.2⟩

/-! ### The claimed part at `Unlock` -/

/-- The claimed part of no bucket is nothing. -/
theorem rbPartR_nil (γ : BNames) (r : GMap GoString BktData) :
    ⊢ rbPartR (GF := GF) γ (fun n => n ∈ ([] : List GoString)) r := by
  unfold rbPartR rbPartRF
  iexists (fun _ => false)
  isplitr
  · ipureintro; intro n h; cases h
  · refine BigSepM.bigSepM_intro (P := iprop(emp)) fun {k} {_} _ => ?_
    rw [if_neg (by simp)]
    iintro -
    itrivial

/-- A claimed part's buckets are tracked buckets. -/
theorem rbPartR_RB (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (r : GMap GoString BktData) :
    trkSide (GF := GF) γ P st c ∗ rbPartR γ S r ⊢
      trkSide γ P st c ∗ rbPartR γ S r ∗ ⌜∀ n, S n → P.RB n = true⌝ := by
  unfold trkSide rbrSide rbPartR rbPartRF
  iintro ⟨⟨Hh, Har, Hac, %Hd, %Hcw, Hb⟩, %F, %Hs, Hp⟩
  iframe Hh Har Hac Hb
  isplitr
  · ipureintro; exact ⟨Hd, Hcw⟩
  isplitl [Hp]
  · iexists F
    iframe Hp
    ipureintro; exact Hs
  · ipureintro; exact fun n h => Hd n (Hs n h)

/-- One claimed bucket's flag cleared, the batch lock's half with it. -/
private theorem rbrOne_idleR (γ : BNames) (P : BParams) (st : BSess) (S : GoString → Prop)
    (r : GMap GoString BktData) (F : GoString → Bool) (n : GoString)
    (M : GMap GoString (Option (Option BktData × Bool))) :
    iprop(ghostMapAuth (GF := GF) γ.rbc 1 M ∗ (rbrOne γ P st n ∗
      (if S n then ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half)
        (some (r.lookup n, F n) : Option (Option BktData × Bool)) else iprop(True)))) ⊢
    |==> ∃ M' : GMap GoString (Option (Option BktData × Bool)), ghostMapAuth γ.rbc 1 M' ∗
      (rbrOne γ P st n ∗ (if S n then ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half)
        (some (r.lookup n, false) : Option (Option BktData × Bool)) else iprop(True))) := by
  by_cases hS : S n
  · rw [if_pos hS, if_pos hS]
    unfold rbrOne
    iintro ⟨Ha, ⟨Hc, -⟩ | ⟨%v, Hc, Hk, %Hf⟩, Hp⟩
    · iexfalso
      ihave %Hv := ghostMapElem_valid_2 n γ.rbc _ _ _ _ $$ Hc Hp
      exfalso
      have h := DFrac.valid_own_op Hv.1
      exact absurd h (by decide)
    · icombine Hc Hp gives %Hv
      obtain rfl : v = (r.lookup n, F n) := Option.some.inj Hv.2
      ihave Hc := (ghostMapElem_halves γ.rbc n _).2 $$ [Hc Hp]
      · iframe
      imod ghost_map_update (some (r.lookup n, false) : Option (Option BktData × Bool)) $$ Ha Hc
        with ⟨Ha, Hc⟩
      icases (ghostMapElem_halves γ.rbc n _).1 $$ Hc with ⟨Hc1, Hc2⟩
      imodintro
      iexists _
      iframe Ha Hc2
      iright
      iexists (r.lookup n, false)
      iframe Hc1 Hk
      ipureintro; exact Hf
  · rw [if_neg hS, if_neg hS]
    iintro ⟨Ha, H, -⟩
    imodintro
    iexists M
    iframe

/-- **`Unlock`'s ghost step on a claimed part** (A1.5): its flags cleared, at the session's end (as
`rbSide_idle` for an unclaimed part). Private: only `batchTxBuffered.Unlock`'s proof takes it (`import all`);
used anywhere else it would assert an idleness Go does not give. -/
private theorem rbPartR_idle (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (r : GMap GoString BktData) :
    iprop(trkSide (GF := GF) γ P st c ∗ rbPartR γ S r) ⊢ |==> iprop(trkSide γ P st c ∗ rbOwnInR γ S r) := by
  unfold trkSide rbrSide rbPartR rbOwnInR rbPartRF
  iintro ⟨⟨Hh, Har, ⟨%Mc, Hac⟩, %Hd, %Hcw, Hb⟩, %F, %Hs, Hp⟩
  ihave Hj := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq
    (Φ := fun n (_ : Unit) => rbrOne (GF := GF) γ P st n)
    (Ψ := fun n (_ : Unit) => if S n then ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half)
      (some (r.lookup n, F n) : Option (Option BktData × Bool)) else iprop(True)) (m := γ.rbD))).2
    $$ [Hb Hp]
  · iframe
  imod els_upd_each γ.rbc
    (fun n => iprop(rbrOne (GF := GF) γ P st n ∗ (if S n then ghostMapElem (GF := GF) γ.rbc n
      (DFrac.own (1 : Qp).half) (some (r.lookup n, F n) : Option (Option BktData × Bool))
      else iprop(True))))
    (fun n => iprop(rbrOne (GF := GF) γ P st n ∗ (if S n then ghostMapElem (GF := GF) γ.rbc n
      (DFrac.own (1 : Qp).half) (some (r.lookup n, false) : Option (Option BktData × Bool))
      else iprop(True)))) γ.rbD
    (fun n M _ => rbrOne_idleR γ P st S r F n M) Mc $$ [Hac Hj] with ⟨%M', Hac, Hj⟩
  · iframe
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hj with ⟨Hb, Hp⟩
  imodintro
  iframe Hh Har Hb
  isplitl [Hac]
  · isplitl [Hac]
    · iexists M'; iexact Hac
    isplitr
    · ipureintro; exact Hd
    · ipureintro; exact Hcw
  isplitr
  · ipureintro; exact Hs
  · iexact Hp

/-! ### The batch lock in a claimed session -/

/-- The client-facing batch lock is a claimed session's (the mode weakened). -/
theorem batchLocked_claimed (γ : BNames) (P : BParams) (b : Loc) (st : BSess) :
    batchLocked (GF := GF) γ P b st ⊢ batchLocked γ P b st true := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, %Hok⟩, %Hwf⟩
  ihave Hk := trkSide_mode γ P st false true (fun _ h => by cases h) $$ Hk
  iexists t, db
  iframe
  iframe #
  ipureintro; exact ⟨Hok, Hwf⟩

/-- The batch lock's mode fact. -/
theorem batchLocked_cwOk (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (c : Bool) :
    batchLocked (GF := GF) γ P b st c ⊢ batchLocked γ P b st c ∗ ⌜cwOk c st⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, %Hok⟩, %Hwf⟩
  icases trkSide_cw γ P st c $$ Hk with ⟨Hk, %Hcw⟩
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hwf⟩
  · ipureintro; exact Hcw

/-- A claimed part's buckets are tracked buckets, from the batch lock. -/
theorem batchLocked_rbPartR_RB (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (c : Bool)
    (S : GoString → Prop) (r : GMap GoString BktData) :
    batchLocked (GF := GF) γ P b st c ∗ rbPartR γ S r ⊢
      batchLocked γ P b st c ∗ rbPartR γ S r ∗ ⌜∀ n, S n → P.RB n = true⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, %Hok⟩, %Hwf⟩, Hp⟩
  icases rbPartR_RB γ P st c S r $$ [$Hk $Hp] with ⟨Hk, Hp, %HRB⟩
  iframe Hp
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hwf⟩
  · ipureintro; exact HRB

/-- **The free lock's ghost with no claimed write recorded** (A1.5: `Unlock` with nothing pending, every
tracked bucket idle). -/
theorem batchGhostAt_clr (γ : BNames) (P : BParams) (st : BSess) (fr c : Bool)
    (hT : ∀ n, P.RB n = true → st.tk n = .idle) :
    batchGhostAt (GF := GF) γ P st fr c ⊢ batchGhostAt γ P st.clrCw fr := by
  unfold batchGhostAt
  iintro ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, %Hok⟩
  ihave Hk := trkSide_clr γ P st c hT $$ Hk
  iapply (show iprop(batchViewQ (GF := GF) γ P st ∗
      ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.C, st.R) : RView), false) ∗
        ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
        dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
        trkSide γ P st.clrCw ∗ fkHalf γ P st ∗ ⌜bgOk P st fr n w u⌝) ⊢
    iprop(batchViewQ (GF := GF) γ P st.clrCw ∗
      ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.clrCw.C, st.clrCw.R) : RView), false) ∗
        ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
        dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
        trkSide γ P st.clrCw ∗ fkHalf γ P st.clrCw ∗ ⌜bgOk P st.clrCw fr n w u⌝) from .rfl)
  iframe Hv
  iexists n, w, u
  iframe
  ipureintro; exact Hok

end claimed

end backend
end EtcdGrove
end Perennial
