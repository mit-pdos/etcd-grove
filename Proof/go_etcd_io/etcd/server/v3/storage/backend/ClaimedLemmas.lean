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
(A1.7) The claim itself (`batchLocked_claim`: an idle part becomes a claimed part and the client gets the
readers' halves) and the claimed parts' split laws.
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
resource `Rr`, atomic around the mask `E` (auth-schema-srv A6, F-acc, decided by etcd-grove-03; until then
two updates at `⊤`, `E = ⊤`): from `Rr`, the halves at their current contents `old` with the mask `⊤`
narrowed to `E`, and back to `Rr` and `⊤` given the halves at any contents `v` that move each bucket as
`ok` allows. Persistent: `Unlock` runs it at the write-back and again at the commit, with no backend
invariant open; inside the window (at `E`) it runs only `rbrSide_stepR`, which opens the claim invariant
(`↑rbClaimN ⊆ E`, the specs' premise). So a client may keep an invariant of its own open across the
window and hold the halves there with no "lent" state.

**Soundness of the window** (checked when F-acc was decided): (1) the window adds no law: inside it the
client gets the halves `rbRd ½` it gave and must give back halves at contents `ok` allows, as before; the
backend does exactly the step it did at `⊤`. None of the four forbidden laws (soundness note §6,
`bStopView`/`rbOwnInR`'s docstrings: (i) an exclusivity law between a claimed resource and an `rbk` share,
(ii) a reader law taking `rbOwnIn` without `bOpen` or a held read lock, (iii) a re-opening of a closed
backend under the same names, (iv) an update of a bucket's `γ.rbk` element from client-shaped shares
plus the invariant or a token without `rbSide`) is stated or derivable from it: the accessor's type is
unchanged but for the masks. (2) No invariant in `rbClaimN` is open in the client's hands inside the
window: the window's mask `E` contains `↑rbClaimN`, so every invariant under `rbClaimN` is closed when
the client's first half returns, and the client's second half starts from `E`; the claim invariant
(`rbClaimInv`, `inv rbClaimN`, allocated only by `New`) is opened inside the window only by the
backend's step. -/
def rbAcc (γ : BNames) (Sc : List GoString) (ok : GoString → BktData → BktData → Prop)
    (Rr : IProp GF) (E : CoPset) : IProp GF :=
  iprop(□ (Rr -∗ |={⊤, E}=> ∃ old : GoString → BktData,
    ([∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (old n)) ∗
    ∀ v : GoString → BktData, ⌜∀ n, n ∈ Sc → ok n (old n) (v n)⌝ -∗
      ([∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (v n)) -∗ |={E, ⊤}=> Rr))

instance rbAcc_persistent (γ : BNames) (Sc : List GoString) (ok : GoString → BktData → BktData → Prop)
    (Rr : IProp GF) (E : CoPset) : Persistent (rbAcc γ Sc ok Rr E) := by
  unfold rbAcc; infer_instance

/-- The accessor of no bucket (a caller that claimed none), around any mask. -/
theorem rbAcc_nil (γ : BNames) (ok : GoString → BktData → BktData → Prop) (Rr : IProp GF)
    (E : CoPset) :
    ⊢ rbAcc γ [] ok Rr E := by
  unfold rbAcc
  iintro !> HR
  imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := E) CoPset.subseteq_top) with Hcl
  imodintro
  iexists (fun _ => (∅ : BktData))
  isplitr
  · exact BigSepL.bigSepL_nil_intro
  · iintro %v %_ -
    imod Hcl
    imodintro
    iexact HR

/-- An accessor for the moves `ok` is one for fewer moves `ok'`. -/
theorem rbAcc_mono (γ : BNames) (Sc : List GoString) (ok ok' : GoString → BktData → BktData → Prop)
    (Rr : IProp GF) (E : CoPset) (h : ∀ n o v, n ∈ Sc → ok' n o v → ok n o v) :
    rbAcc γ Sc ok Rr E ⊢ rbAcc γ Sc ok' Rr E := by
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
        [∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own q.half) (f n)
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
      (fun k => if k ∈ Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q.half) (f k) else iprop(True))
      (fun k => if k ∈ m :: Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q.half) (f k) else iprop(True))
      m Hmd (fun k hk => by
        rw [mapIf_cons_ne Sc m k hk (fun k => ghostMapElem (GF := GF) γ.rbr k (DFrac.own q.half) (f k))]) $$ Hs with ⟨-, Hw⟩
    isplitr
    · ipureintro
      intro k hk
      rcases List.mem_cons.1 hk with rfl | hk
      · exact Hmd
      · exact Hd k hk
    · iapply Hw
      ihave Hm := (show ghostMapElem (GF := GF) γ.rbr m (DFrac.own q.half) (f m) ⊢
          (if m ∈ m :: Sc then ghostMapElem γ.rbr m (DFrac.own q.half) (f m) else iprop(True)) by
        rw [if_pos (by simp)]) $$ Hm
      iexact Hm

/-- Back from the family over the tracked names to the client's halves. -/
theorem rbRdL_of_map (γ : BNames) (f : GoString → BktData) (q : Qp) (Sc : List GoString)
    (hnd : Sc.Nodup) (hd : ∀ n, n ∈ Sc → γ.rbD.lookup n ≠ none) :
    ([∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own q.half) (f n)
      else iprop(True))) ⊢ [∗list] n ∈ Sc, rbRd γ n q (f n) := by
  induction Sc with
  | nil => exact BigSepL.bigSepL_nil_intro
  | cons m Sc ih =>
    have hm : m ∉ Sc := (List.nodup_cons.1 hnd).1
    have hmd := hd m (by simp)
    iintro H
    icases mapIf_acc γ.rbD
      (fun k => if k ∈ m :: Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q.half) (f k) else iprop(True))
      (fun k => if k ∈ Sc then ghostMapElem (GF := GF) γ.rbr k (DFrac.own q.half) (f k) else iprop(True))
      m hmd (fun k hk => by
        rw [mapIf_cons_ne Sc m k hk (fun k => ghostMapElem (GF := GF) γ.rbr k (DFrac.own q.half) (f k))]) $$ H with ⟨Hm, Hw⟩
    ihave Hs := Hw $$ []
    · rw [if_neg hm]; itrivial
    ihave Hm := (show (if m ∈ m :: Sc then ghostMapElem (GF := GF) γ.rbr m (DFrac.own q.half) (f m)
        else iprop(True)) ⊢ ghostMapElem γ.rbr m (DFrac.own q.half) (f m) by
      rw [if_pos (by simp)]) $$ Hm
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hm]
    · iunfold rbRd
      iframe Hm
      ipureintro; exact hmd
    · iapply (ih (List.nodup_cons.1 hnd).2 (fun n hn => hd n (List.mem_cons_of_mem _ hn))) $$ Hs

/-! ### The step of the readers' state with the client's halves -/

/-- One bucket's step of the readers' state, with the client's quarter of a bucket of `Sc` (A6.2): a bucket
of `Sc` moves with `readTx.mu`'s half, the batch lock's quarter and the client's; an untouched bucket
outside `Sc` keeps its contents; a touched one outside `Sc` is unclaimed (its flag is set, `tkI`, and a
claimed bucket's is clear) and moves with the claim invariant's quarter (its link holds vacuously). -/
private theorem rbrOne_stepR (γ : BNames) (P : BParams) (st st' : BSess) (rv rv' : RView)
    (Sc : List GoString) (old : GoString → BktData) (r : GMap GoString BktData) (FL Cl : GoString → Bool)
    (n : GoString) (hrv : rv = (st.C, st.R)) (hrv' : rv' = (st'.C, st'.R))
    (hk : st.tk n = .idle → st.cw n = false → st'.tk n = .idle ∧ rvBkt P rv n = rvBkt P rv' n)
    (hcwS : st.cw n = true → n ∈ Sc) (hFL : FL n = false → st.tk n = .idle ∨ st.cw n = true) :
    iprop((∃ M : GMap GoString BktData, ghostMapAuth (GF := GF) γ.rbr 1 M) ∗
      (ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv n) ∗ rbrOne γ P st n ∗
        (if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half.half) (old n) else iprop(True)) ∗
        rbClaimOne γ n (Cl n) ∗ rbElem γ n (1 : Qp).half.half (r.lookup n, FL n))) ⊢
    |==> iprop((∃ M : GMap GoString BktData, ghostMapAuth γ.rbr 1 M) ∗
      (ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv' n) ∗ rbrOne γ P st' n ∗
        ((if n ∈ Sc then ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half.half) (rvBkt P rv' n)
          else iprop(True)) ∗ ⌜n ∈ Sc → old n = rvBkt P rv n⌝) ∗
        rbClaimOne γ n (Cl n) ∗ rbElem γ n (1 : Qp).half.half (r.lookup n, FL n))) := by
  subst hrv hrv'
  unfold rbrOne
  by_cases hin : n ∈ Sc
  · rw [if_pos hin, if_pos hin]
    iintro ⟨⟨%M, Ha⟩, Hh, Hl, Ho, Hn, Hk⟩
    icases gme_join γ.rbr n _ _ _ _ $$ [$Hh $Hl] with ⟨Hh, -⟩
    icases gme_join γ.rbr n _ _ _ _ $$ [$Hh $Ho] with ⟨Hw, %Hag⟩
    ihave Hw := gme_frac γ.rbr n _ 1 _ q34_add $$ Hw
    imod ghost_map_update (rvBkt P (st'.C, st'.R) n) $$ Ha Hw with ⟨Ha, Hw⟩
    ihave Hw := gme_frac γ.rbr n 1 _ _ q34_add.symm $$ Hw
    icases gme_split γ.rbr n _ _ _ $$ Hw with ⟨Hw, Ho⟩
    icases gme_split γ.rbr n _ _ _ $$ Hw with ⟨Hh, Hl⟩
    imodintro
    isplitl [Ha]
    · iexists _; iexact Ha
    iframe
    ipureintro; intro _; exact Hag.symm
  · rw [if_neg hin, if_neg hin]
    have hcw : st.cw n = false := by
      cases h : st.cw n
      · rfl
      · exact absurd (hcwS h) hin
    by_cases htk : st.tk n = .idle
    · obtain ⟨_, h2⟩ := hk htk hcw
      iintro ⟨Ha, Hh, Hl, -, Hn, Hk⟩
      imodintro
      iframe Ha Hn Hk
      rw [← h2]
      iframe
      isplitr
      · itrivial
      · ipureintro; intro h; exact absurd h hin
    · have hFLt : FL n = true := by
        cases h : FL n
        · rcases hFL h with h1 | h1
          · exact absurd h1 htk
          · rw [hcw] at h1; cases h1
        · rfl
      iintro ⟨⟨%M, Ha⟩, Hh, Hl, -, Hn, Hk⟩
      cases hcl : Cl n
      · ihave Hn := (rbClaimOne_U γ n _ rfl).1 $$ Hn
        iunfold rbClaimU at Hn
        icases Hn with ⟨%c, %f, %v, Hkc, Hr, Hcn, -⟩
        icases gme_join γ.rbk n _ _ _ _ $$ [$Hkc $Hk] with ⟨Hkk, %Hfe⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hfe
        icases gme_split γ.rbk n _ _ _ $$ Hkk with ⟨Hkc, Hk⟩
        have hf : FL n = true := hFLt
        icases gme_join γ.rbr n _ _ _ _ $$ [$Hh $Hl] with ⟨Hh, -⟩
        icases gme_join γ.rbr n _ _ _ _ $$ [$Hh $Hr] with ⟨Hw, -⟩
        ihave Hw := gme_frac γ.rbr n _ 1 _ q34_add $$ Hw
        imod ghost_map_update (rvBkt P (st'.C, st'.R) n) $$ Ha Hw with ⟨Ha, Hw⟩
        ihave Hw := gme_frac γ.rbr n 1 _ _ q34_add.symm $$ Hw
        icases gme_split γ.rbr n _ _ _ $$ Hw with ⟨Hw, Hr⟩
        icases gme_split γ.rbr n _ _ _ $$ Hw with ⟨Hh, Hl⟩
        imodintro
        isplitl [Ha]
        · iexists _; iexact Ha
        iframe Hh Hl Hk
        isplitr
        · isplitr
          · itrivial
          · ipureintro; intro h; exact absurd h hin
        iapply (rbClaimOne_U γ n _ rfl).2
        iunfold rbClaimU
        iexists r.lookup n, FL n, _
        iframe
        ipureintro; intro h; rw [hf] at h; cases h
      · ihave Hn := (rbClaimOne_C γ n _ rfl).1 $$ Hn
        iunfold rbClaimC at Hn
        icases Hn with ⟨%c, %w, Hkc, -, -⟩
        ihave %Hfe := ghostMapElem_agree n γ.rbk _ _ _ _ $$ Hkc Hk
        have := congrArg Prod.snd Hfe
        simp only at this
        rw [hFLt] at this
        cases this

/-- **A step of the readers' state with the client's quarters of the claimed buckets `Sc`** (A1.5; A6.2):
every bucket's readers' element moves to the new readers' contents: one of `Sc` with the client's quarter,
an untouched one keeps its contents, a touched one outside `Sc` (unclaimed) with the claim invariant's. -/
theorem rbrSide_stepR (γ : BNames) (P : BParams) (st st' : BSess) (rv rv' : RView) (c c' : Bool)
    (Sc : List GoString) (old : GoString → BktData)
    (hrv : rv = (st.C, st.R)) (hrv' : rv' = (st'.C, st'.R))
    (hk : ∀ n, P.RB n = true → st.tk n = .idle → st.cw n = false →
      st'.tk n = .idle ∧ rvBkt P rv n = rvBkt P rv' n)
    (hcwS : ∀ n, st.cw n = true → n ∈ Sc) (hmode : cwOk c' st') (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rbSide (GF := GF) γ P (rbData P st.S) (tkI P st) ∗ rbrSide γ P st c ∗ rbrHalves γ P 1 rv ∗
      [∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then
        ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half.half) (old n) else iprop(True))) ⊢
      |={E}=> iprop(rbSide γ P (rbData P st.S) (tkI P st) ∗ rbrSide γ P st' c' ∗ rbrHalves γ P 1 rv' ∗
        ([∗map] n ↦ _u ∈ γ.rbD, (if n ∈ Sc then
          ghostMapElem γ.rbr n (DFrac.own (1 : Qp).half.half) (rvBkt P rv' n) else iprop(True))) ∗
        ⌜∀ n, γ.rbD.lookup n ≠ none → n ∈ Sc → old n = rvBkt P rv n⌝ ∗
        ⌜∀ n, γ.rbD.lookup n ≠ none → P.RB n = true⌝) := by
  unfold rbSide rbrSide rbrHalves
  iintro ⟨⟨Hka, ⟨%FL, Hl, %HI⟩, %Hbd, #Hinv⟩, ⟨Ha, %Hd, -, Hs⟩, Hh, Ho⟩
  iunfold rbPartF at Hl
  icases Hl with ⟨%Hpl, Hl⟩
  ihave Hl := (rbEls_top γ _ _).1 $$ Hl
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  ihave Hz := (map_zip5 γ.rbD
    (fun n => ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv n))
    (fun n => rbrOne (GF := GF) γ P st n)
    (fun n => if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half.half) (old n)
      else iprop(True))
    (fun n => rbClaimOne (GF := GF) γ n (Cl n))
    (fun n => rbElem (GF := GF) γ n (1 : Qp).half.half ((rbData P st.S).lookup n, FL n))).1
    $$ [$Hh $Hs $Ho $Hm $Hl]
  imod map_upd_thread _ _ _ γ.rbD (fun n hn => rbrOne_stepR γ P st st' rv rv' Sc old (rbData P st.S) FL Cl n
      hrv hrv' (hk n (Hd n hn)) (hcwS n) (fun h => HI n hn h (Hd n hn))) $$ [$Ha $Hz] with ⟨Ha, Hz⟩
  icases (map_zip5 γ.rbD
    (fun n => ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half) (rvBkt P rv' n))
    (fun n => rbrOne (GF := GF) γ P st' n)
    (fun n => iprop((if n ∈ Sc then ghostMapElem (GF := GF) γ.rbr n (DFrac.own (1 : Qp).half.half)
      (rvBkt P rv' n) else iprop(True)) ∗ ⌜n ∈ Sc → old n = rvBkt P rv n⌝))
    (fun n => rbClaimOne (GF := GF) γ n (Cl n))
    (fun n => rbElem (GF := GF) γ n (1 : Qp).half.half ((rbData P st.S).lookup n, FL n))).2 $$ Hz
    with ⟨Hh, Hs, Hj, Hm, Hl⟩
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hj with ⟨Ho, Hp⟩
  ihave %Hall := BigSepM.bigSepM_pure_intro $$ Hp
  imod Hclose $$ [Hac Hm] with -
  · inext
    iunfold rbClaimInv
    iexists Mc, Cl
    iframe Hac Hm
    ipureintro; exact Hbt
  imodintro
  isplitl [Hka Hl]
  · iframe Hka
    isplitl [Hl]
    · iexists FL
      isplitl [Hl]
      · iunfold rbPartF
        isplitr
        · ipureintro; exact Hpl
        · iapply (rbEls_top γ _ (fun n => ((rbData P st.S).lookup n, FL n))).2 $$ Hl
      · ipureintro; exact HI
    isplitr
    · ipureintro; exact Hbd
    · iexact Hinv
  iframe Hh Ho
  isplitl [Ha Hs]
  · iframe Ha Hs
    ipureintro; exact ⟨Hd, hmode⟩
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
    (Sc : List GoString) (ok : GoString → BktData → BktData → Prop) (Rr : IProp GF) (E : CoPset)
    (hE : ↑rbClaimN ⊆ E) (hnd : Sc.Nodup)
    (hrv : rv = (st.C, st.R)) (hrv' : rv' = (st'.C, st'.R)) (hS : st'.S = st.S)
    (hk : ∀ n, P.RB n = true → st.tk n = .idle → st.cw n = false →
      st'.tk n = .idle ∧ rvBkt P rv n = rvBkt P rv' n)
    (hcl : ∀ n, st.cw n = true → st'.tk n = .idle ∨ st'.cw n = true)
    (hkI : ∀ n, P.RB n = true → st.tk n = .idle → st'.tk n = .idle)
    (hcwS : ∀ n, st.cw n = true → n ∈ Sc) (hmode : cwOk c' st')
    (hok : ∀ n, n ∈ Sc → P.RB n = true → ok n (rvBkt P rv n) (rvBkt P rv' n)) :
    iprop(trkSide (GF := GF) γ P st c ∗ Rr ∗ rbAcc γ Sc ok Rr E) ⊢
      (rbrHalves γ P 1 rv -∗ |={⊤}=> rbrHalves γ P 1 rv' ∗ (trkSide γ P st' c' ∗ Rr)) := by
  unfold trkSide trkHalf
  iintro ⟨⟨⟨Hh, Hs⟩, Hr⟩, HR, #Hacc⟩ Hhv
  iunfold rbAcc at Hacc
  imod Hacc $$ HR with ⟨%old, Hc, Hk⟩
  icases rbRdL_map γ old (1 : Qp).half Sc hnd $$ Hc with ⟨%Hscd, Hc⟩
  imod rbrSide_stepR γ P st st' rv rv' c c' Sc old hrv hrv' hk hcwS hmode E hE
    $$ [Hs Hr Hhv Hc] with ⟨Hs, Hr, Hhv, Hc, %Hold, %HRB⟩
  · iframe
  ihave Hc := rbRdL_of_map γ (fun n => rvBkt P rv' n) (1 : Qp).half Sc hnd Hscd $$ Hc
  imod Hk $$ %(fun n => rvBkt P rv' n) %(fun n hn => by
      rw [Hold n (Hscd n hn) hn]; exact hok n hn (HRB n (Hscd n hn))) Hc with HR
  ihave Hs := rbSide_mono γ P _ (tkI P st) (tkI P st') (fun n h hRB => by
    rcases h hRB with h1 | h1
    · exact Or.inl (hkI n hRB h1)
    · exact hcl n h1) $$ Hs
  imodintro
  rw [hS]
  iframe

/-! ### The mode of the batch lock's side -/

/-- **The batch lock's side in another mode** (A1.5): the same state, the mode fact of the new mode. Private
(A1 review MINOR 1): only `batchTxBuffered.Unlock`'s proof (`import all`) goes from mode `true` back to `false`;
clients have the two directions that are always harmless, `trkSide_mode_up` (`false → true`) and `trkSide_mode_win`
(either way inside the hook's window, where `cwOk` holds in both modes). -/
private theorem trkSide_mode (γ : BNames) (P : BParams) (st : BSess) (c c' : Bool)
    (h : cwOk c st → cwOk c' st) :
    trkSide (GF := GF) γ P st c ⊢ trkSide γ P st c' := by
  unfold trkSide rbrSide
  iintro ⟨Hh, Har, %Hd, %Hcw, Hb⟩
  iframe Hh Har Hb
  ipureintro
  exact ⟨Hd, h Hcw⟩

/-- **The batch lock's side, from the client-facing mode to the claimed one** (A1.5). -/
theorem trkSide_mode_up (γ : BNames) (P : BParams) (st : BSess) :
    trkSide (GF := GF) γ P st false ⊢ trkSide γ P st true :=
  trkSide_mode γ P st false true (fun _ h => by cases h)

/-- **The batch lock's side in the hook's window, in any mode** (`cwOk` holds in both there). -/
theorem trkSide_mode_win (γ : BNames) (P : BParams) (st : BSess) (c c' : Bool) (hw : st.cnt.hw = true) :
    trkSide (GF := GF) γ P st c ⊢ trkSide γ P st c' :=
  trkSide_mode γ P st c c' (fun _ _ h => by rw [hw] at h; cases h)

/-- **No claimed write recorded, once every tracked bucket is idle** (A1.5: `Unlock` with nothing pending):
the batch lock's side at `st.clrCw`, in the client-facing mode. -/
theorem trkSide_clr (γ : BNames) (P : BParams) (st : BSess) (c : Bool)
    (hT : ∀ n, P.RB n = true → st.tk n = .idle) :
    trkSide (GF := GF) γ P st c ⊢ trkSide γ P st.clrCw := by
  unfold trkSide rbrSide
  iintro ⟨Hh, Har, %Hd, -, Hb⟩
  isplitl [Hh]
  · iapply (show trkHalf (GF := GF) γ P st.S (tkI P st.clrCw) ⊢ trkHalf γ P st.clrCw.S (tkI P st.clrCw) from .rfl)
    iapply trkHalf_mono γ P st.S (tkI P st) (tkI P st.clrCw) (fun n _ hRB => Or.inl (hT n hRB)) $$ Hh
  iframe Har
  isplitr
  · ipureintro; exact Hd
  isplitr
  · ipureintro; exact fun _ _ _ => rfl
  iapply BigSepM.bigSepM_mono (fun {k} {_} _ => rbrOne_congr γ P st st.clrCw k rfl rfl) $$ Hb

/-! ### The claimed part at `Unlock` -/

/-- The claimed part of no bucket is nothing. -/
theorem rbPartR_nil (γ : BNames) (r : GMap GoString BktData) :
    ⊢ rbPartR (GF := GF) γ (fun n => n ∈ ([] : List GoString)) r := by
  unfold rbPartR rbPartRF
  iexists (fun _ => false)
  isplitr
  · ipureintro; intro n h; cases h
  isplitl []
  · refine BigSepM.bigSepM_intro (P := iprop(emp)) fun {k} {_} _ => ?_
    rw [if_neg (by simp)]
    iintro -
    itrivial
  · iapply (rbEls_empty (GF := GF) γ (fun n => n ∈ ([] : List GoString)) (fun n h => by cases h)
      (1 : Qp).half.half.half (fun n => (r.lookup n, false)))

/-- A claimed part's buckets are tracked buckets. -/
theorem rbPartR_RB (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (r : GMap GoString BktData) :
    trkSide (GF := GF) γ P st c ∗ rbPartR γ S r ⊢
      trkSide γ P st c ∗ rbPartR γ S r ∗ ⌜∀ n, S n → P.RB n = true⌝ := by
  unfold trkSide rbrSide rbPartR rbPartRF
  iintro ⟨⟨Hh, Har, %Hd, %Hcw, Hb⟩, %F, %Hs, Hp, He⟩
  iframe Hh Har Hb
  isplitr
  · ipureintro; exact ⟨Hd, Hcw⟩
  isplitl [Hp He]
  · iexists F
    iframe Hp He
    ipureintro; exact Hs
  · ipureintro; exact fun n h => Hd n (Hs n h)

/-- One claimed bucket's flag cleared (A6.2): with the claim invariant's half of its claim element. -/
private theorem rbcIdle_one (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData)
    (F Cl : GoString → Bool) (n : GoString) :
    iprop((∃ M : GMap GoString (Option (Option BktData × Bool)), ghostMapAuth (GF := GF) γ.rbc 1 M) ∗
      (rbClaimOne γ n (Cl n) ∗ (if S n then ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half)
        (some (r.lookup n, F n) : Option (Option BktData × Bool)) else iprop(True)))) ⊢
    |==> iprop((∃ M : GMap GoString (Option (Option BktData × Bool)), ghostMapAuth γ.rbc 1 M) ∗
      (rbClaimOne γ n (Cl n) ∗ (if S n then ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half)
        (some (r.lookup n, false) : Option (Option BktData × Bool)) else iprop(True)))) := by
  by_cases hS : S n
  · rw [if_pos hS, if_pos hS]
    iintro ⟨⟨%M, Ha⟩, Hn, Hp⟩
    cases hcl : Cl n
    · ihave Hn := (rbClaimOne_U γ n _ rfl).1 $$ Hn
      iunfold rbClaimU at Hn
      icases Hn with ⟨%c, %f, %v, -, -, Hcn, -⟩
      ihave %Hv := ghostMapElem_agree n γ.rbc _ _ _ _ $$ Hcn Hp
      cases Hv
    · ihave Hn := (rbClaimOne_C γ n _ rfl).1 $$ Hn
      iunfold rbClaimC at Hn
      icases Hn with ⟨%c, %w, Hk, Hcn, %Hw⟩
      icases gme_join γ.rbc n _ _ _ _ $$ [$Hcn $Hp] with ⟨Hc, %Hwe⟩
      obtain rfl := Option.some.inj Hwe
      ihave Hc := gme_frac γ.rbc n _ 1 _ q2_add $$ Hc
      imod ghost_map_update (some (r.lookup n, false) : Option (Option BktData × Bool)) $$ Ha Hc
        with ⟨Ha, Hc⟩
      ihave Hc := gme_frac γ.rbc n 1 _ _ q2_add.symm $$ Hc
      icases gme_split γ.rbc n _ _ _ $$ Hc with ⟨Hc1, Hc2⟩
      imodintro
      isplitl [Ha]
      · iexists _; iexact Ha
      iframe Hc2
      iapply (rbClaimOne_C γ n _ rfl).2
      iunfold rbClaimC
      iexists c, (r.lookup n, false)
      iframe
      ipureintro; exact Hw
  · rw [if_neg hS, if_neg hS]
    iintro H
    imodintro
    iexact H

/-- **`Unlock`'s ghost step on a claimed part** (A1.5): its flags cleared, at the session's end (as
`rbSide_idle` for an unclaimed part), through the claim invariant (A6.2). Private: only
`batchTxBuffered.Unlock`'s proof takes it (`import all`); used anywhere else it would assert an idleness Go
does not give. It takes `trkSide_idle`'s premise, the part's buckets untouched (A1 review MINOR 2), unused by
its proof: `rbOwnInR` grants nothing beyond `rbPartR` today, and the premise keeps any later law that reads a
readers' fact off a cleared claimed flag sound. -/
private theorem rbPartR_idle (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (r : GMap GoString BktData) (_hT : ∀ n, S n → P.RB n = true → st.tk n = .idle)
    (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(trkSide (GF := GF) γ P st c ∗ rbPartR γ S r) ⊢
      |={E}=> iprop(trkSide γ P st c ∗ rbOwnInR γ S r) := by
  unfold trkSide trkHalf rbSide rbPartR rbOwnInR rbPartRF
  iintro ⟨⟨⟨Hh, Hka, Hl, %Hbd, #Hinv⟩, Hr⟩, %F, %Hs, Hp, He⟩
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  ihave Hj := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq
    (Φ := fun n (_ : Unit) => rbClaimOne (GF := GF) γ n (Cl n))
    (Ψ := fun n (_ : Unit) => if S n then ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half)
      (some (r.lookup n, F n) : Option (Option BktData × Bool)) else iprop(True)) (m := γ.rbD))).2
    $$ [Hm Hp]
  · iframe
  imod map_upd_thread _ _ _ γ.rbD (fun n _ => rbcIdle_one γ S r F Cl n) $$ [Hac Hj] with ⟨Hac, Hj⟩
  · isplitl [Hac]
    · iexists Mc; iexact Hac
    · iexact Hj
  icases (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ Hj with ⟨Hm, Hp⟩
  icases Hac with ⟨%Mc', Hac⟩
  imod Hclose $$ [Hac Hm] with -
  · inext
    iunfold rbClaimInv
    iexists Mc', Cl
    iframe Hac Hm
    ipureintro; exact Hbt
  imodintro
  iframe Hh Hka Hl Hr
  isplitr
  · iframe Hinv; ipureintro; exact Hbd
  isplitr
  · ipureintro; exact Hs
  isplitl [Hp]
  · iexact Hp
  · iexact He

/-! ### The batch lock in a claimed session -/

/-- The client-facing batch lock is a claimed session's (the mode weakened). -/
theorem batchLocked_claimed (γ : BNames) (P : BParams) (b : Loc) (st : BSess) :
    batchLocked (GF := GF) γ P b st ⊢ batchLocked γ P b st true := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, %Hwf⟩
  ihave Hk := trkSide_mode_up γ P st $$ Hk
  iexists t, db
  iframe
  iframe #
  ipureintro; exact ⟨Hok, Hwf⟩

/-- The batch lock's mode fact. -/
theorem batchLocked_cwOk (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (c : Bool) :
    batchLocked (GF := GF) γ P b st c ⊢ batchLocked γ P b st c ∗ ⌜cwOk c st⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, %Hwf⟩
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
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, %Hwf⟩, Hp⟩
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
  iintro ⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩
  ihave Hk := trkSide_clr γ P st c hT $$ Hk
  iapply (show iprop(batchViewQ (GF := GF) γ P st ∗
      ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.C, st.R) : RView), false) ∗
        ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
        dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
        trkSide γ P st.clrCw ∗ fkHalf γ P st ∗ bufRc st ∗ ⌜bgOk P st fr n w u⌝) ⊢
    iprop(batchViewQ (GF := GF) γ P st.clrCw ∗
      ∃ (n w u : Nat), ghostVar γ.rvs (1 : Qp).half (((st.clrCw.C, st.clrCw.R) : RView), false) ∗
        ownTokAuth γ.wb n ∗ monoNatAuthOwn γ.wbc 1 w ∗ ghostVar γ.used (1 : Qp).half u ∗
        dghostVar γ.opn (DFrac.own (1 : Qp).half.half) false ∗
        trkSide γ P st.clrCw ∗ fkHalf γ P st.clrCw ∗ bufRc st.clrCw ∗ ⌜bgOk P st.clrCw fr n w u⌝) from .rfl)
  iframe Hv
  iexists n, w, u
  iframe
  iframe #
  ipureintro; exact Hok

/-! ### Claimed parts: split laws (A1.7) -/

/-- Congruence: a claimed part says nothing of the buckets outside its set. -/
theorem rbPartRF_congr (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (F F' : GoString → Bool) (hr : ∀ n, S n → r.lookup n = r'.lookup n) (hF : ∀ n, S n → F n = F' n) :
    rbPartRF (GF := GF) γ S r F ⊢ rbPartRF γ S r' F' := by
  unfold rbPartRF
  iintro ⟨%Hs, Hp, He⟩
  isplitr
  · ipureintro; exact Hs
  isplitl [Hp]
  · iapply BigSepM.bigSepM_mono (fun {k} {_} _ => ?_) $$ Hp
    by_cases h : S k
    · simp only [if_pos h, hr k h, hF k h]; exact .rfl
    · simp only [if_neg h]; exact .rfl
  · iapply (rbEls_congr γ S (1 : Qp).half.half.half (fun n => (r.lookup n, false))
      (fun n => (r'.lookup n, false)) (fun n hn _ => by simp only [hr n hn])).1 $$ He

/-- **The claimed parts of disjoint bucket sets, at the same flags, are the claimed part of their union.** -/
theorem rbPartRF_split (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (F : GoString → Bool) (hd : ∀ n, S n → S' n → False) :
    rbPartRF (GF := GF) γ (fun n => S n ∨ S' n) r F ⊣⊢ iprop(rbPartRF γ S r F ∗ rbPartRF γ S' r F) := by
  unfold rbPartRF
  dsimp only
  have he : ([∗map] n ↦ _u ∈ γ.rbD, (@ite _ (S n ∨ S' n) (Classical.propDecidable _) (ghostMapElem (GF := GF) γ.rbc n
      (DFrac.own (1 : Qp).half) (some (r.lookup n, F n) : Option (Option BktData × Bool))) iprop(True))) ⊣⊢
      iprop(([∗map] n ↦ _u ∈ γ.rbD, (if S n then ghostMapElem (GF := GF) γ.rbc n
        (DFrac.own (1 : Qp).half) (some (r.lookup n, F n) : Option (Option BktData × Bool)) else iprop(True))) ∗
       ([∗map] n ↦ _u ∈ γ.rbD, (if S' n then ghostMapElem (GF := GF) γ.rbc n
        (DFrac.own (1 : Qp).half) (some (r.lookup n, F n) : Option (Option BktData × Bool)) else iprop(True)))) := by
    constructor
    · refine (BigSepM.bigSepM_mono fun {k} {_} _ =>
        (ite_or_split (A := S k) (B := S' k) Iff.rfl _ (hd k)).1).trans
        (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
    · refine (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
        (BigSepM.bigSepM_mono fun {k} {_} _ => (ite_or_split (A := S k) (B := S' k) Iff.rfl _ (hd k)).2)
  have hE := rbEls_split (GF := GF) γ S S' (1 : Qp).half.half.half (fun n => (r.lookup n, false)) hd
  constructor
  · iintro ⟨%Hs, Hp, He⟩
    icases he.1 $$ Hp with ⟨H1, H2⟩
    icases hE.1 $$ He with ⟨E1, E2⟩
    isplitl [H1 E1]
    · isplitr
      · ipureintro; exact fun n h => Hs n (Or.inl h)
      · iframe H1 E1
    · isplitr
      · ipureintro; exact fun n h => Hs n (Or.inr h)
      · iframe H2 E2
  · iintro ⟨⟨%Hs1, H1, E1⟩, ⟨%Hs2, H2, E2⟩⟩
    isplitr
    · ipureintro
      rintro n (h | h)
      · exact Hs1 n h
      · exact Hs2 n h
    isplitl [H1 H2]
    · iapply he.2
      iframe
    · iapply hE.2
      iframe

/-- **The claimed parts of disjoint bucket sets are the claimed part of their union.** -/
theorem rbPartR_split (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (hd : ∀ n, S n → S' n → False) :
    rbPartR (GF := GF) γ (fun n => S n ∨ S' n) r ⊣⊢ iprop(rbPartR γ S r ∗ rbPartR γ S' r) := by
  unfold rbPartR
  constructor
  · iintro ⟨%F, H⟩
    icases (rbPartRF_split γ S S' r F hd).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists F; iexact H1
    · iexists F; iexact H2
  · iintro ⟨⟨%F1, H1⟩, ⟨%F2, H2⟩⟩
    iexists (fun n => if S n then F1 n else F2 n)
    iapply (rbPartRF_split γ S S' r _ hd).2
    isplitl [H1]
    · iapply rbPartRF_congr γ S r r F1 _ (fun _ _ => rfl) (fun n hS => by simp only [if_pos hS]) $$ H1
    · iapply rbPartRF_congr γ S' r r F2 _ (fun _ _ => rfl)
        (fun n hS' => by simp only [if_neg (fun hS => hd n hS hS')]) $$ H2

/-- **The idle claimed parts of disjoint bucket sets are the idle claimed part of their union.** -/
theorem rbOwnInR_split (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (hd : ∀ n, S n → S' n → False) :
    rbOwnInR (GF := GF) γ (fun n => S n ∨ S' n) r ⊣⊢ iprop(rbOwnInR γ S r ∗ rbOwnInR γ S' r) := by
  unfold rbOwnInR
  exact rbPartRF_split γ S S' r _ hd

/-- **An idle claimed part is a claimed part** (forgetting that nothing is pending). -/
theorem rbOwnInR_part (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) :
    rbOwnInR (GF := GF) γ S r ⊢ rbPartR γ S r := by
  unfold rbOwnInR rbPartR
  iintro H
  iexists _
  iexact H

/-- **Restriction**, of a claimed part. -/
theorem rbPartR_congr (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (h : ∀ n, S n → r.lookup n = r'.lookup n) :
    rbPartR (GF := GF) γ S r ⊢ rbPartR γ S r' := by
  unfold rbPartR
  iintro ⟨%F, H⟩
  iexists F
  iapply rbPartRF_congr γ S r r' F F h (fun _ _ => rfl) $$ H

/-- **Restriction**, of an idle claimed part. -/
theorem rbOwnInR_congr (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData)
    (h : ∀ n, S n → r.lookup n = r'.lookup n) :
    rbOwnInR (GF := GF) γ S r ⊢ rbOwnInR γ S r' := by
  unfold rbOwnInR
  exact rbPartRF_congr γ S r r' _ _ h (fun _ _ => rfl)

/-- **The same set**, extensionally, of a claimed part. -/
theorem rbPartR_set (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (h : ∀ n, S n ↔ S' n) : rbPartR (GF := GF) γ S r ⊣⊢ rbPartR γ S' r := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact .rfl

/-- **The same set**, extensionally, of an idle claimed part. -/
theorem rbOwnInR_set (γ : BNames) (S S' : GoString → Prop) (r : GMap GoString BktData)
    (h : ∀ n, S n ↔ S' n) : rbOwnInR (GF := GF) γ S r ⊣⊢ rbOwnInR γ S' r := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact .rfl

/-! ### The claim (A1.7, D3) -/

/-- The idle claimed part of no bucket is nothing. -/
theorem rbOwnInR_nil (γ : BNames) (r : GMap GoString BktData) :
    ⊢ rbOwnInR (GF := GF) γ (fun n => n ∈ ([] : List GoString)) r := by
  unfold rbOwnInR rbPartRF
  isplitr
  · ipureintro; intro n h; cases h
  isplitl []
  · refine BigSepM.bigSepM_intro (P := iprop(emp)) fun {k} {_} _ => ?_
    rw [if_neg (by simp)]
    iintro -
    itrivial
  · iapply (rbEls_empty (GF := GF) γ (fun n => n ∈ ([] : List GoString)) (fun n h => by cases h)
      (1 : Qp).half.half.half (fun n => (r.lookup n, false)))

/-! ### The claim tokens (A6.2 of `auth-schema-srv`, §R.1, 2026-11-17) -/

/-- **The claim tokens of disjoint bucket sets are those of their union.** -/
theorem rbClaimToks_split (γ : BNames) (P : BParams) (S S' : GoString → Prop)
    (hd : ∀ n, S n → S' n → False) :
    rbClaimToks (GF := GF) γ P (fun n => S n ∨ S' n) ⊣⊢
      iprop(rbClaimToks γ P S ∗ rbClaimToks γ P S') := by
  unfold rbClaimToks
  dsimp only
  have he : ([∗map] n ↦ _u ∈ γ.rbD, (@ite _ (S n ∨ S' n) (Classical.propDecidable _) (ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half) (none : Option (Option BktData × Bool)))
      iprop(True))) ⊣⊢
      iprop(([∗map] n ↦ _u ∈ γ.rbD, (if S n then ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half) (none : Option (Option BktData × Bool)) else iprop(True))) ∗
       ([∗map] n ↦ _u ∈ γ.rbD, (if S' n then ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half) (none : Option (Option BktData × Bool)) else iprop(True)))) := by
    constructor
    · refine (BigSepM.bigSepM_mono fun {k} {_} _ =>
        (ite_or_split (A := S k) (B := S' k) Iff.rfl _ (hd k)).1).trans
        (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1
    · refine (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
        (BigSepM.bigSepM_mono fun {k} {_} _ => (ite_or_split (A := S k) (B := S' k) Iff.rfl _ (hd k)).2)
  constructor
  · iintro ⟨#Hi, Hm⟩
    icases he.1 $$ Hm with ⟨H1, H2⟩
    iframe Hi H1 H2
  · iintro ⟨⟨#Hi, H1⟩, ⟨-, H2⟩⟩
    iframe Hi
    iapply he.2
    iframe

/-- **The same set**, extensionally. -/
theorem rbClaimToks_set (γ : BNames) (P : BParams) (S S' : GoString → Prop) (h : ∀ n, S n ↔ S' n) :
    rbClaimToks (GF := GF) γ P S ⊣⊢ rbClaimToks γ P S' := by
  have : S = S' := funext fun n => propext (h n)
  subst this; exact ⟨.rfl, .rfl⟩

/-- **Fewer claim tokens.** -/
theorem rbClaimToks_sub (γ : BNames) (P : BParams) (S S' : GoString → Prop) (h : ∀ n, S' n → S n) :
    rbClaimToks (GF := GF) γ P S ⊢ rbClaimToks γ P S' := by
  iintro H
  ihave H := (rbClaimToks_set γ P S (fun n => S' n ∨ (S n ∧ ¬ S' n)) (fun n =>
    ⟨fun hs => by
      by_cases e : S' n
      · exact Or.inl e
      · exact Or.inr ⟨hs, e⟩,
     fun hh => hh.elim (h n) And.left⟩)).1 $$ H
  icases (rbClaimToks_split γ P S' (fun n => S n ∧ ¬ S' n) (fun n h1 h2 => h2.2 h1)).1 $$ H with ⟨H, -⟩
  iexact H

/-- **The claim of one tracked bucket** (A6.2): the client's idle part of `n` and its claim token become its
claimed part and a quarter of the bucket's readers' element, at the part's contents: the claim invariant's
unclaimed branch (the token's half of the claim element with the branch's makes it whole; a claimed branch
holds `some`, which the token's `none` refutes), whose link gives the readers' contents (the flag is clear).
No batch lock: the client's quarter is deposited in the invariant for good. -/
theorem rbOwnIn_claim1 (γ : BNames) (P : BParams) (n : GoString) (r : GMap GoString BktData)
    (hBT : ∃ i, P.BT.lookup n = some i) (hRB : P.RB n = true) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(rbOwnIn (GF := GF) γ (fun k => k = n) r ∗ rbClaimToks γ P (fun k => k = n)) ⊢
      |={E}=> iprop(rbOwnInR γ (fun k => k = n) r ∗ rbRd γ n (1 : Qp).half (bktOf r n)) := by
  unfold rbClaimToks rbOwnIn
  iintro ⟨Hc, #Hinv, Ht⟩
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt, Hm⟩
  have hd : γ.rbD.lookup n ≠ none := by obtain ⟨i, hi⟩ := hBT; exact Hbt n i hi hRB
  ihave Hc := (rbPartF_one γ n r _ hd).1 $$ Hc
  ihave Ht := (mapIf_one γ.rbD (fun k => k = n) n (fun _ => Iff.rfl) hd (fun k =>
    ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half) (none : Option (Option BktData × Bool)))).2
    $$ Ht
  icases mapAcc γ.rbD (fun k => rbClaimOne (GF := GF) γ k (Cl k))
    (fun k => rbClaimOne (GF := GF) γ k (if k = n then true else Cl k)) n hd
    (fun k hk => by rw [if_neg hk]) $$ Hm with ⟨Hn, Hm⟩
  cases hcl : Cl n
  · ihave Hn := (rbClaimOne_U γ n _ rfl).1 $$ Hn
    iunfold rbClaimU at Hn
    icases Hn with ⟨%c, %f, %v, Hk, Hr, Hcn, %HL⟩
    icases gme_join γ.rbk n _ _ _ _ $$ [$Hk $Hc] with ⟨Hk, %Hke⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hke
    ihave Hk := gme_frac γ.rbk n _ _ _ q_claim $$ Hk
    icases gme_split γ.rbk n _ _ _ $$ Hk with ⟨Hk, He⟩
    have hv : v = bktOf r n := HL rfl
    subst hv
    icases gme_join γ.rbc n _ _ _ _ $$ [$Hcn $Ht] with ⟨Hc, -⟩
    ihave Hc := gme_frac γ.rbc n _ 1 _ q2_add $$ Hc
    imod ghost_map_update (some (r.lookup n, false) : Option (Option BktData × Bool)) $$ Hac Hc
      with ⟨Hac, Hc⟩
    ihave Hc := gme_frac γ.rbc n 1 _ _ q2_add.symm $$ Hc
    icases gme_split γ.rbc n _ _ _ $$ Hc with ⟨Hc1, Hc2⟩
    imod Hclose $$ [Hac Hm Hk Hc1] with -
    · inext
      iunfold rbClaimInv
      iexists _, (fun k => if k = n then true else Cl k)
      iframe Hac
      isplitr
      · ipureintro; exact Hbt
      iapply Hm
      iapply (rbClaimOne_C γ n _ (by rw [if_pos rfl])).2
      iunfold rbClaimC
      iexists r.lookup n, (r.lookup n, false)
      iframe Hk Hc1
      ipureintro; rfl
    imodintro
    isplitl [Hc2 He]
    · unfold rbOwnInR rbPartRF
      isplitr
      · ipureintro; intro k hk; subst hk; exact hd
      isplitl [Hc2]
      · iapply (mapIf_one γ.rbD (fun k => k = n) n (fun _ => Iff.rfl) hd (fun k =>
          ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half)
            (some (r.lookup k, false) : Option (Option BktData × Bool)))).1 $$ Hc2
      · iapply (rbEls_one γ n (1 : Qp).half.half.half (fun k => (r.lookup k, false)) hd).2
        iexact He
    · unfold rbRd
      isplitr
      · ipureintro; exact hd
      iexact Hr
  · ihave Hn := (rbClaimOne_C γ n _ rfl).1 $$ Hn
    iunfold rbClaimC at Hn
    icases Hn with ⟨%c, %w, -, Hcn, -⟩
    ihave %Hv := ghostMapElem_agree n γ.rbc _ _ _ _ $$ Hcn Ht
    cases Hv

/-- **The claim** (A6.2 of `auth-schema-srv`, §R.1, `notes/auth-schema-srv-a6-claim-scope.md`; replaces A1.7's
claim under the batch lock): an idle part of the tracked buckets `Sc` (each a bucket of the table) and their
claim tokens become the claimed part (`rbOwnInR`, which no trusted writer takes and which has no law back to
`rbPart`) and a quarter of each bucket's readers' element at the part's contents (`rbRd γ n ½`; `readTx.mu`
holds half, the batch lock a quarter, so every reader then sees them, `rtHeldF_rbRd`). **No batch lock**:
the claim invariant (`rbClaimInv`) links an unclaimed bucket's readers' contents to its writer's contents
while no write is pending. A bucket is claimed for good, and at most once (its token is consumed). -/
theorem rbOwnIn_claim (γ : BNames) (P : BParams) (r : GMap GoString BktData) (E : CoPset)
    (hE : ↑rbClaimN ⊆ E) :
    ∀ (Sc : List GoString), Sc.Nodup → (∀ n, n ∈ Sc → (∃ i, P.BT.lookup n = some i) ∧ P.RB n = true) →
    iprop(rbOwnIn (GF := GF) γ (fun k => k ∈ Sc) r ∗ rbClaimToks γ P (fun k => k ∈ Sc)) ⊢
      |={E}=> iprop(rbOwnInR γ (fun k => k ∈ Sc) r ∗ [∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (bktOf r n)) := by
  intro Sc
  induction Sc with
  | nil =>
    intro _ _
    iintro -
    imodintro
    isplitl []
    · iapply rbOwnInR_nil
    · iapply BigSepL.bigSepL_nil.2
      iempintro
  | cons m Sc ih =>
    intro hnd hS
    have hm : m ∉ Sc := (List.nodup_cons.1 hnd).1
    iintro ⟨Hc, Ht⟩
    ihave Hc := (rbOwnIn_set γ (fun k => k ∈ m :: Sc) (fun k => k = m ∨ k ∈ Sc) r (fun k => by simp)).1 $$ Hc
    icases (rbOwnIn_split γ (fun k => k = m) (fun k => k ∈ Sc) r
      (fun k h1 h2 => hm (h1 ▸ h2))).1 $$ Hc with ⟨Hcm, Hcs⟩
    ihave Ht := (rbClaimToks_set γ P (fun k => k ∈ m :: Sc) (fun k => k = m ∨ k ∈ Sc) (fun k => by simp)).1
      $$ Ht
    icases (rbClaimToks_split γ P (fun k => k = m) (fun k => k ∈ Sc)
      (fun k h1 h2 => hm (h1 ▸ h2))).1 $$ Ht with ⟨Htm, Hts⟩
    have ⟨hBT, hRB⟩ := hS m (by simp)
    imod rbOwnIn_claim1 γ P m r hBT hRB E hE $$ [$Hcm $Htm] with ⟨Hcm, Hrm⟩
    imod ih (List.nodup_cons.1 hnd).2 (fun n hn => hS n (List.mem_cons_of_mem _ hn)) $$ [$Hcs $Hts]
      with ⟨Hcs, Hrs⟩
    imodintro
    isplitl [Hcm Hcs]
    · iapply (rbOwnInR_set γ (fun k => k = m ∨ k ∈ Sc) (fun k => k ∈ m :: Sc) r (fun k => by simp)).1
      iapply (rbOwnInR_split γ (fun k => k = m) (fun k => k ∈ Sc) r (fun k h1 h2 => hm (h1 ▸ h2))).2
      iframe
    · iapply (BigSepL.bigSepL_cons).2
      iframe

/-! ### `Unlock`'s ghost steps at its end (A1.7: after the write-back or the commit) -/

/-- **`Unlock`'s ghost step on an unclaimed part** (`rbSide_idle`), at the session's end, where the part's
buckets are untouched (and the readers see the writer's contents there, `trkOk`: the claim invariant's link,
A6.2). Private: only `batchTxBuffered.Unlock`'s proof takes it (`import all`). -/
private theorem trkSide_idle (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (r : GMap GoString BktData) (hT : ∀ n, S n → P.RB n = true → st.tk n = .idle)
    (hok : trkOk P st st.tk) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(trkSide (GF := GF) γ P st c ∗ rbPart γ S r) ⊢ |={E}=> iprop(trkSide γ P st c ∗ rbOwnIn γ S r) := by
  unfold trkSide trkHalf
  iintro ⟨⟨⟨Hh, Hs⟩, Hr⟩, Hc⟩
  imod rbSide_idle γ P st c S r (tkI P st) (tkI P st) (fun _ h => h)
    (fun n hn hRB => Or.inl (hT n hn hRB))
    (fun n hn hRB => by
      rw [rvBkt_idle hok hRB (hT n hn hRB), rbData_lookup, hRB]
      rfl) E hE $$ [$Hs $Hr $Hc] with ⟨Hs, Hr, Hc⟩
  imodintro
  iframe

/-- **`Unlock`'s ghost steps on the free lock's ghost** (A1.7): the unclaimed part and the claimed part
handed in made idle, every tracked bucket untouched there (the free lock's `bgOk`). Private, as
`trkSide_idle`. -/
private theorem batchGhostAt_idle (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S Sr : GoString → Prop)
    (r rc : GMap GoString BktData) (hT : ∀ n, P.RB n = true → st.tk n = .idle) (E : CoPset)
    (hE : ↑rbClaimN ⊆ E) :
    iprop(batchGhostAt (GF := GF) γ P st true c ∗ rbPart γ S r ∗ rbPartR γ Sr rc) ⊢
      |={E}=> iprop(batchGhostAt γ P st true c ∗ rbOwnIn γ S r ∗ rbOwnInR γ Sr rc) := by
  unfold batchGhostAt
  iintro ⟨⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, Hp, Hpr⟩
  imod trkSide_idle γ P st c S r (fun n _ hRB => hT n hRB) Hok.2.2.2.2.2.2.2.2.2.2.1 E hE $$ [$Hk $Hp]
    with ⟨Hk, Hp⟩
  imod rbPartR_idle γ P st c Sr rc (fun n _ hRB => hT n hRB) E hE $$ [$Hk $Hpr] with ⟨Hk, Hpr⟩
  imodintro
  iframe Hv Hp Hpr
  iexists n, w, u
  iframe
  iframe #
  ipureintro; exact Hok

/-! ### A claimed part agrees with the batch lock (auth-schema-srv A6 (c), 2026-11-18) -/

/-- **One bucket of a claimed part agrees with the batch lock's writer's contents** (auth-schema-srv A6 (c), form
decided by the agent): the claim invariant's claimed branch holds five eighths (K-c) of the bucket's element at the
claimed part's contents (`rbClaimC`, `w.1 = c`), the batch lock's side the last quarter at the writer's contents.
An agreement law, not one of the four forbidden ones (soundness §6): it needs the batch lock, takes no `γ.rbk`
share of the client's, and changes no ghost state. -/
private theorem trkSide_rbPartR_agree (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (S : GoString → Prop)
    (r : GMap GoString BktData) (n : GoString) (hS : S n) (E : CoPset) (hE : ↑rbClaimN ⊆ E) :
    iprop(trkSide (GF := GF) γ P st c ∗ rbPartR γ S r) ⊢
      |={E}=> iprop(trkSide γ P st c ∗ rbPartR γ S r ∗ ⌜r.lookup n = (rbData P st.S).lookup n⌝) := by
  unfold trkSide trkHalf rbSide rbPartR rbPartRF rbPartF
  iintro ⟨⟨⟨Hh, Ha, ⟨%F, ⟨%Hl0, Hl⟩, %HF⟩, %Hbt, #Hinv⟩, Hr⟩, %G, %Hs, Hp, He⟩
  have hd := Hs n hS
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hd
  iinv Hinv with >Hb Hclose
  iunfold rbClaimInv at Hb
  icases Hb with ⟨%Mc, %Cl, Hac, %Hbt2, Hm⟩
  icases (BigSepM.bigSepM_lookup_acc
    (Φ := fun k (_ : Unit) => if S k then ghostMapElem (GF := GF) γ.rbc k (DFrac.own (1 : Qp).half)
      (some (r.lookup k, G k) : Option (Option BktData × Bool)) else iprop(True))
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ Hp with ⟨Hpn, Hp⟩
  ihave Hpn := (show (if S n then ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half)
      (some (r.lookup n, G n) : Option (Option BktData × Bool)) else iprop(True)) ⊢
    ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half) (some (r.lookup n, G n)) by
      rw [if_pos hS]) $$ Hpn
  ihave Hl := (rbEls_top γ _ _).1 $$ Hl
  icases (BigSepM.bigSepM_lookup_acc
    (Φ := fun k (_ : Unit) => ghostMapElem (GF := GF) γ.rbk k (DFrac.own (1 : Qp).half.half)
      ((fun n => ((rbData P st.S).lookup n, F n)) k))
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ Hl with ⟨Hln, Hl⟩
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun k (_ : Unit) => rbClaimOne (GF := GF) γ k (Cl k))
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ Hm with ⟨Hmn, Hm⟩
  cases hcl : Cl n
  · ihave Hmn := (rbClaimOne_U γ n _ rfl).1 $$ Hmn
    iunfold rbClaimU at Hmn
    icases Hmn with ⟨%c0, %f, %v, -, -, Hcn, -⟩
    ihave %Hv := ghostMapElem_agree n γ.rbc _ _ _ _ $$ Hcn Hpn
    cases Hv
  · ihave Hmn := (rbClaimOne_C γ n _ rfl).1 $$ Hmn
    iunfold rbClaimC at Hmn
    icases Hmn with ⟨%c0, %w, Hk, Hcn, %Hw⟩
    icombine Hcn Hpn gives %Hag1
    icombine Hk Hln gives %Hag2
    have h1 : w = (r.lookup n, G n) := Option.some.inj Hag1.2
    have h2 : (c0, false) = ((rbData P st.S).lookup n, F n) := Hag2.2
    have hres : r.lookup n = (rbData P st.S).lookup n := by
      rw [← (Prod.mk.inj h2).1, ← Hw, h1]
    ihave Hmn : rbClaimOne γ n true $$ [Hk Hcn]
    · iapply (rbClaimOne_C γ n _ rfl).2
      iunfold rbClaimC
      iexists c0, w
      iframe Hk Hcn
      ipureintro; exact Hw
    ihave Hm := Hm $$ Hmn
    imod Hclose $$ [Hac Hm] with -
    · inext
      iunfold rbClaimInv
      iexists Mc, Cl
      iframe Hac Hm
      ipureintro; exact Hbt2
    ihave Hpn := (show ghostMapElem (GF := GF) γ.rbc n (DFrac.own (1 : Qp).half)
        (some (r.lookup n, G n) : Option (Option BktData × Bool)) ⊢
      (if S n then ghostMapElem γ.rbc n (DFrac.own (1 : Qp).half) (some (r.lookup n, G n)) else iprop(True)) by
        rw [if_pos hS]) $$ Hpn
    ihave Hp := Hp $$ Hpn
    ihave Hl := Hl $$ Hln
    ihave Hl := (rbEls_top γ _ _).2 $$ Hl
    imodintro
    iframe Hh Ha Hr Hinv Hl Hp He
    ipureintro
    exact ⟨⟨⟨Hl0, HF⟩, Hbt⟩, Hs, hres⟩

/-- **A claimed part agrees with the batch lock's writer's contents**, one bucket `n` of it (as
`trkSide_rbPartR_agree`). None of the four forbidden laws (`notes/auth-schema-srv-a1-soundness.md` §6; checked
2026-11-19, the (c) forms' acceptance by etcd-grove-03): (i) it states no exclusivity between a claimed resource and a
`γ.rbk` share (only an equality of contents); (ii) it is no reader law (it needs the batch lock, not `rbOwnIn`);
(iii) it opens nothing (the batch lock is held); (iv) it updates no ghost state (both sides come back unchanged). -/
theorem batchLocked_rbPartR_agree (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (c : Bool)
    (S : GoString → Prop) (r : GMap GoString BktData) (n : GoString) (hS : S n) (E : CoPset)
    (hE : ↑rbClaimN ⊆ E) :
    batchLocked (GF := GF) γ P b st c ∗ rbPartR γ S r ⊢
      |={E}=> batchLocked γ P b st c ∗ rbPartR γ S r ∗ ⌜r.lookup n = (rbData P st.S).lookup n⌝ := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n0, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, %Hwf⟩, Hp⟩
  imod trkSide_rbPartR_agree γ P st c S r n hS E hE $$ [$Hk $Hp] with ⟨Hk, Hp, %Hag⟩
  imodintro
  iframe Hp
  isplitl
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hwf⟩
  · ipureintro; exact Hag

/-- **A claimed part agrees with any part of the tracked buckets** (K-c, STOP 6 of auth-schema-srv A6, decided by
etcd-grove-03, 2026-11-19): where both have a bucket, their contents are equal (the claimed part's eighth of the
bucket's `γ.rbk` element and the part's quarter agree). Pure, with no update, so a fupd-free observation (a
snapshot's, handed the batch lock's `rbOwn`) learns the claimed contents (`authBkLend`). None of the four
forbidden laws (`notes/auth-schema-srv-a1-soundness.md` §6, amended for K-c after an independent check): (i) it
states only an equality of **contents**, no exclusivity, and not the part's flags (so no idleness of a claimed
bucket); (ii) no reader law; (iii) opens nothing; (iv) both sides come back unchanged. -/
theorem rbPartRF_rbPart_agree (γ : BNames) (S S' : GoString → Prop) (r r' : GMap GoString BktData)
    (F : GoString → Bool) :
    rbPartRF (GF := GF) γ S r F ∗ rbPart γ S' r' ⊢
      rbPartRF γ S r F ∗ rbPart γ S' r' ∗ ⌜∀ n, S n → S' n → r.lookup n = r'.lookup n⌝ := by
  unfold rbPartRF rbPart rbPartF
  iintro ⟨⟨%Hs, Hc, He⟩, %G, %Hs', Hl⟩
  icases rbEls_agree γ S S' _ _ _ _ $$ [$He $Hl] with ⟨He, Hl, %Hag⟩
  isplitl [Hc He]
  · iframe Hc He
    ipureintro; exact Hs
  isplitl [Hl]
  · iexists G
    iframe Hl
    ipureintro; exact Hs'
  · ipureintro
    intro n hS hS'
    exact congrArg Prod.fst (Hag n hS hS' (Hs n hS))

/-- `rbPartRF_rbPart_agree`, of a claimed part. -/
theorem rbPartR_rbPart_agree (γ : BNames) (S S' : GoString → Prop) (r r' : GMap GoString BktData) :
    rbPartR (GF := GF) γ S r ∗ rbPart γ S' r' ⊢
      rbPartR γ S r ∗ rbPart γ S' r' ∗ ⌜∀ n, S n → S' n → r.lookup n = r'.lookup n⌝ := by
  unfold rbPartR
  iintro ⟨⟨%F, Hc⟩, Hl⟩
  icases rbPartRF_rbPart_agree γ S S' r r' F $$ [$Hc $Hl] with ⟨Hc, Hl, %Hag⟩
  isplitl [Hc]
  · iexists F; iexact Hc
  iframe Hl
  ipureintro; exact Hag

/-- `rbPartRF_rbPart_agree`, of an idle claimed part. -/
theorem rbOwnInR_rbPart_agree (γ : BNames) (S S' : GoString → Prop) (r r' : GMap GoString BktData) :
    rbOwnInR (GF := GF) γ S r ∗ rbPart γ S' r' ⊢
      rbOwnInR γ S r ∗ rbPart γ S' r' ∗ ⌜∀ n, S n → S' n → r.lookup n = r'.lookup n⌝ :=
  rbPartRF_rbPart_agree γ S S' r r' _

/-- `rbPartRF_rbPart_agree`, of an idle claimed part and the client's half of every bucket (`rbOwn`). -/
theorem rbOwnInR_rbOwn_agree (γ : BNames) (S : GoString → Prop) (r r' : GMap GoString BktData) :
    rbOwnInR (GF := GF) γ S r ∗ rbOwn γ r' ⊢
      rbOwnInR γ S r ∗ rbOwn γ r' ∗ ⌜∀ n, S n → r.lookup n = r'.lookup n⌝ := by
  unfold rbOwn
  iintro H
  icases rbOwnInR_rbPart_agree γ S (fun _ => True) r r' $$ H with ⟨H1, H2, %Hag⟩
  iframe H1 H2
  ipureintro; exact fun n h => Hag n h trivial

/-! ### `Unlock`'s confirmation of the claimed buckets (auth-schema-srv A6 (c), 2026-11-18) -/

/-- **A claiming client's confirmation window** for the buckets `Sc` at the contents `f` (auth-schema-srv A6
(c), form decided by the agent): from `Rr`, its readers' halves at their current contents `old` with the mask
`⊤` narrowed to `E`, and back to `Rr'` and `⊤` given that `old` is `f` on `Sc` (the halves unchanged). `Unlock`
runs it once, at its end, with `f` the writer's contents: so the client learns that the readers see the
writer's contents on every claimed bucket after `Unlock` (the accessor `rbAcc` alone allows a bucket only
deleted from to keep its old contents at each of its windows, and its client cannot tell the last window). -/
def rbConf (γ : BNames) (Sc : List GoString) (f : GoString → BktData) (Rr Rr' : IProp GF) (E : CoPset) :
    IProp GF :=
  iprop(Rr -∗ |={⊤, E}=> ∃ old : GoString → BktData,
    ([∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (old n)) ∗
    (⌜∀ n, n ∈ Sc → old n = f n⌝ -∗ ([∗list] n ∈ Sc, rbRd γ n (1 : Qp).half (old n)) -∗
      |={E, ⊤}=> Rr'))

/-- The confirmation of no bucket, around any mask. -/
theorem rbConf_nil (γ : BNames) (f : GoString → BktData) (Rr : IProp GF) (E : CoPset) :
    ⊢ rbConf γ [] f Rr Rr E := by
  unfold rbConf
  iintro HR
  imod (fupd_mask_subseteq (PROP := IProp GF) (E1 := ⊤) (E2 := E) CoPset.subseteq_top) with Hcl
  imodintro
  iexists (fun _ => (∅ : BktData))
  isplitr
  · exact BigSepL.bigSepL_nil_intro
  · iintro %_ -
    imod Hcl
    imodintro
    iexact HR

/-- The batch lock's side agrees with a client's share of a tracked bucket's readers' contents. -/
private theorem rbrSide_rbRd (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (n : GoString) (q : Qp)
    (v : BktData) :
    iprop(rbrSide (GF := GF) γ P st c ∗ rbRd γ n q v) ⊢
      iprop(rbrSide γ P st c ∗ rbRd γ n q v ∗ ⌜v = rvBkt P (st.C, st.R) n⌝) := by
  unfold rbrSide rbRd
  iintro ⟨⟨Ha, %Hd, %Hcw, Hb⟩, ⟨%Hn, H⟩⟩
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp Hn
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun k (_ : Unit) => rbrOne (GF := GF) γ P st k)
    (m := γ.rbD) (i := n) (x := u) hu).1 $$ Hb with ⟨Ho, Hb⟩
  unfold rbrOne
  icombine H Ho gives %Hag
  ihave Hb := Hb $$ Ho
  iframe Ha Hb H
  ipureintro
  exact ⟨⟨Hd, Hcw⟩, Hn, Hag.2⟩

/-- The same of a list of claimed buckets. -/
private theorem rbrSide_rbRdL (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (q : Qp)
    (old : GoString → BktData) : ∀ Sc : List GoString,
    iprop(rbrSide (GF := GF) γ P st c ∗ [∗list] n ∈ Sc, rbRd γ n q (old n)) ⊢
      iprop(rbrSide γ P st c ∗ ([∗list] n ∈ Sc, rbRd γ n q (old n)) ∗
        ⌜∀ n, n ∈ Sc → old n = rvBkt P (st.C, st.R) n⌝)
  | [] => by
    iintro ⟨Hs, Hl⟩
    iframe Hs Hl
    ipureintro; intro n h; cases h
  | m :: Sc => by
    iintro ⟨Hs, Hl⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hm, Hl⟩
    icases rbrSide_rbRd γ P st c m q (old m) $$ [$Hs $Hm] with ⟨Hs, Hm, %h1⟩
    icases rbrSide_rbRdL γ P st c q old Sc $$ [$Hs $Hl] with ⟨Hs, Hl, %h2⟩
    iframe Hs
    isplitl [Hm Hl]
    · iapply (BigSepL.bigSepL_cons).2; iframe Hm Hl
    ipureintro
    intro n hn
    rcases List.mem_cons.1 hn with rfl | hn
    · exact h1
    · exact h2 n hn

/-- **`Unlock`'s confirmation on the batch lock's side**: the client's halves agree with the batch lock's
quarters, which are at the readers' contents of the state `st`. Private, as `trkSide_idle`. -/
private theorem trkSide_conf (γ : BNames) (P : BParams) (st : BSess) (c : Bool) (Sc : List GoString)
    (f : GoString → BktData) (Rr Rr' : IProp GF) (E : CoPset)
    (hf : ∀ n, n ∈ Sc → rvBkt P (st.C, st.R) n = f n) :
    iprop(trkSide (GF := GF) γ P st c ∗ Rr ∗ rbConf γ Sc f Rr Rr' E) ⊢
      |={⊤}=> iprop(trkSide γ P st c ∗ Rr') := by
  unfold trkSide
  iintro ⟨⟨Hh, Hs⟩, HR, Hc⟩
  unfold rbConf
  imod Hc $$ HR with ⟨%old, Hl, Hk⟩
  icases rbrSide_rbRdL γ P st c _ old Sc $$ [$Hs $Hl] with ⟨Hs, Hl, %Ho⟩
  imod Hk $$ %(fun n hn => (Ho n hn).trans (hf n hn)) Hl with HR
  imodintro
  iframe

/-- **`Unlock`'s confirmation on the free lock's ghost**, every claimed bucket untouched there (so the readers
see the writer's contents, `trkOk`). Private, as `trkSide_idle`. -/
private theorem batchGhostAt_conf (γ : BNames) (P : BParams) (st : BSess) (fr c : Bool) (Sc : List GoString)
    (f : GoString → BktData) (Rr Rr' : IProp GF) (E : CoPset)
    (hf : ∀ n, n ∈ Sc → P.RB n = true ∧ st.tk n = .idle ∧ bktOf st.S n = f n) :
    iprop(batchGhostAt (GF := GF) γ P st fr c ∗ Rr ∗ rbConf γ Sc f Rr Rr' E) ⊢
      |={⊤}=> iprop(batchGhostAt γ P st fr c ∗ Rr') := by
  unfold batchGhostAt
  iintro ⟨⟨Hv, %n, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, #Hbr, %Hok⟩, HR, Hc⟩
  imod trkSide_conf γ P st c Sc f Rr Rr' E (fun m hm => by
      obtain ⟨h1, h2, h3⟩ := hf m hm
      rw [rvBkt_idle Hok.2.2.2.2.2.2.2.2.2.2.1 h1 h2, h3]) $$ [$Hk $HR $Hc] with ⟨Hk, HR⟩
  imodintro
  iframe Hv HR
  iexists n, w, u
  iframe
  iframe #
  ipureintro; exact Hok

end claimed

end backend
end EtcdGrove
end Perennial
