/-
Written trees (`wtreeQ`, `SpillDefs.lean`) assembled during the spill: a written page and its
children's separately held trees give the page's tree (`wtreeQ_branch`, `wtreeQ_leaf`), the
tokens' separation giving the pages' disjointness (`viewUnique`); an old tree of the view is
one (`wtreeQ_old`); bounds can be widened (`wtreeQ_widen`) and an old tree's lower bound raised
to its first key (`treeKeys_first`); and at the end a tree whose pages are among `P` (the view's
and the dirty ones) is `wtree` (`wtree_of_Q`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillDefs
public import Proof.go_etcd_io.bbolt.ShapeOpen
public import Proof.go_etcd_io.bbolt.ShapeRoute
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-! ### Reach (as `DBWrite.lean`'s, without its section's variables) -/

theorem has_transfer (P P' : GMap Nat (List w8)) :
    ∀ a d, treeHas P a d → (∀ x, treeHas P a x → P' !! x = P !! x) → treeHas P' a d := by
  intro a d h
  induction h using treeHas.rec
    (motive_2 := fun pg d _ => (∀ x, pageHas P pg x → P' !! x = P !! x) → pageHas P' pg d)
    (motive_3 := fun v d _ => (∀ x, bucketHas P v x → P' !! x = P !! x) → bucketHas P' v d) with
  | root r pg hpg =>
    intro hag; exact .root r pg (by rw [hag r (.root r pg hpg)]; exact hpg)
  | sub r pg id hpg hph ih =>
    intro hag
    exact .sub r pg id (by rw [hag r (.root r pg hpg)]; exact hpg)
      (ih (fun x hx => hag x (.sub r pg x hpg hx)))
  | child pg i id hf hi ht ih =>
    rename_i hag; exact .child pg i id hf hi (ih (fun x hx => hag x (.child pg i x hf hi hx)))
  | bucket pg i id hf hi hb hbh ih =>
    rename_i hag; exact .bucket pg i id hf hi hb (ih (fun x hx => hag x (.bucket pg i x hf hi hb hx)))
  | file v id hr ht ih =>
    rename_i hag; exact .file v id hr (ih (fun x hx => hag x (.file v x hr hx)))
  | inline v id hr hp ih =>
    rename_i hag; exact .inline v id hr (ih (fun x hx => hag x (.inline v x hr hx)))

theorem has_isSome (P : GMap Nat (List w8)) (a d : Nat) (h : treeHas P a d) :
    (P !! d).isSome := by
  induction h using treeHas.rec
    (motive_2 := fun _ d _ => (P !! d).isSome)
    (motive_3 := fun _ d _ => (P !! d).isSome) with
  | root root pg hpg => rw [hpg]; rfl
  | sub _ _ _ _ _ ih => exact ih
  | child _ _ _ _ _ _ ih => exact ih
  | bucket _ _ _ _ _ _ _ ih => exact ih
  | file _ _ _ _ ih => exact ih
  | inline _ _ _ _ ih => exact ih

/-! ### Reach, monotone in the pages -/

theorem has_mono (Q P : GMap Nat (List w8)) (hs : Q ⊆ P) :
    ∀ a d, treeHas Q a d → treeHas P a d := by
  intro a d h
  induction h using treeHas.rec
    (motive_2 := fun pg d _ => pageHas P pg d)
    (motive_3 := fun v d _ => bucketHas P v d) with
  | root r pg hpg => exact .root r pg (hs r pg hpg)
  | sub r pg id hpg _ ih => exact .sub r pg id (hs r pg hpg) ih
  | child pg i id hf hi _ ih => exact .child pg i id hf hi ih
  | bucket pg i id hf hi hb _ ih => exact .bucket pg i id hf hi hb ih
  | file v id hr _ ih => exact .file v id hr ih
  | inline v id hr _ ih => exact .inline v id hr ih

theorem bucketHas_mono (Q P : GMap Nat (List w8)) (hs : Q ⊆ P) :
    ∀ v d, bucketHas Q v d → bucketHas P v d := by
  intro v d h
  induction h using bucketHas.rec
    (motive_1 := fun a d _ => treeHas P a d)
    (motive_2 := fun pg d _ => pageHas P pg d) with
  | root r pg hpg => exact .root r pg (hs r pg hpg)
  | sub r pg id hpg _ ih => exact .sub r pg id (hs r pg hpg) ih
  | child pg i id hf hi _ ih => exact .child pg i id hf hi ih
  | bucket pg i id hf hi hb _ ih => exact .bucket pg i id hf hi hb ih
  | file v id hr _ ih => exact .file v id hr ih
  | inline v id hr _ ih => exact .inline v id hr ih

theorem leaf_branch_ne : leafPageFlag ≠ branchPageFlag := by
  unfold leafPageFlag branchPageFlag; decide

/-- In a well-formed tree of `Q`, the reach in a larger map is the reach in `Q`. -/
theorem has_of_wf (Q P : GMap Nat (List w8)) (h : Nat) (hs : Q ⊆ P) (x : Nat)
    (hw : treeWF Q h x) : ∀ d, treeHas P x d → treeHas Q x d := by
  induction hw using treeWF.rec
    (motive_2 := fun pg _ _ => ∀ d, pageHas P pg d → pageHas Q pg d)
    (motive_3 := fun v _ => ∀ d, bucketHas P v d → bucketHas Q v d) with
  | page root pg _ hpg _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | root _ _ _ => exact .root root pg hpg
    | sub _ pg' _ hpg' hph =>
      rw [hs root pg hpg] at hpg'; cases hpg'
      exact .sub root pg d hpg (ih d hph)
  | leaf pg len hfl _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | child _ _ _ hb _ _ => rw [hfl] at hb; exact absurd hb leaf_branch_ne
    | bucket _ i _ hl hi hf hbh => exact .bucket pg i d hl hi hf (ih i hi hf d hbh)
  | branch pg len hfl _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | child _ i _ hb hi ht => exact .child pg i d hb hi (ih i hi d ht)
    | bucket _ _ _ hl _ _ _ => rw [hfl] at hl; exact absurd hl leaf_branch_ne.symm
  | file v _ hr _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | file _ _ _ ht => exact .file v d hr (ih d ht)
    | inline _ _ hr0 _ => exact absurd hr0 hr
  | inline v _ hr _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | file _ _ hr1 _ => exact absurd hr hr1
    | inline _ _ _ hp => exact .inline v d hr (ih d hp)

theorem bucketHas_of_wf (Q P : GMap Nat (List w8)) (h : Nat) (hs : Q ⊆ P) (v : List w8)
    (hw : bucketWF Q h v) : ∀ d, bucketHas P v d → bucketHas Q v d := by
  induction hw using bucketWF.rec
    (motive_1 := fun x _ => ∀ d, treeHas P x d → treeHas Q x d)
    (motive_2 := fun pg _ _ => ∀ d, pageHas P pg d → pageHas Q pg d) with
  | page root pg _ hpg _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | root _ _ _ => exact .root root pg hpg
    | sub _ pg' _ hpg' hph =>
      rw [hs root pg hpg] at hpg'; cases hpg'
      exact .sub root pg d hpg (ih d hph)
  | leaf pg len hfl _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | child _ _ _ hb _ _ => rw [hfl] at hb; exact absurd hb leaf_branch_ne
    | bucket _ i _ hl hi hf hbh => exact .bucket pg i d hl hi hf (ih i hi hf d hbh)
  | branch pg len hfl _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | child _ i _ hb hi ht => exact .child pg i d hb hi (ih i hi d ht)
    | bucket _ _ _ hl _ _ _ => rw [hfl] at hl; exact absurd hl leaf_branch_ne.symm
  | file v _ hr _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | file _ _ _ ht => exact .file v d hr (ih d ht)
    | inline _ _ hr0 _ => exact absurd hr0 hr
  | inline v _ hr _ _ ih =>
    first | intro d hd | rename_i d hd
    cases hd with
    | file _ _ hr1 _ => exact absurd hr hr1
    | inline _ _ _ hp => exact .inline v d hr (ih d hp)

/-- A subtree of a well-formed tree is well-formed. -/
theorem treeWF_sub (P : GMap Nat (List w8)) (h : Nat) :
    ∀ x a, treeHas P x a → treeWF P h x → treeWF P h a := by
  intro x a hx
  induction hx using treeHas.rec
    (motive_2 := fun pg a _ => ∀ len, pageTreeWF P h pg len → treeWF P h a)
    (motive_3 := fun v a _ => bucketWF P h v → treeWF P h a) with
  | root _ _ _ => exact id
  | sub r pg id hpg _ ih =>
    first | intro hw | rename_i hw
    cases hw with
    | page _ pg' _ hpg' _ hpt => rw [hpg] at hpg'; cases hpg'; exact ih _ hpt
  | child pg i id hf hi _ ih =>
    first | intro len hp | rename_i len hp
    cases hp with
    | leaf _ _ hfl _ _ => rw [hfl] at hf; exact absurd hf leaf_branch_ne
    | branch _ _ _ _ hk => exact ih (hk i hi)
  | bucket pg i id hl hi hb _ ih =>
    first | intro len hp | rename_i len hp
    cases hp with
    | leaf _ _ _ _ hbw => exact ih (hbw i hi hb)
    | branch _ _ hfl _ _ => rw [hfl] at hl; exact absurd hl leaf_branch_ne.symm
  | file v id hr _ ih =>
    first | intro hb | rename_i hb
    cases hb with
    | file _ _ _ ht => exact ih ht
    | inline _ _ hr0 _ _ => exact absurd hr0 hr
  | inline v id hr _ ih =>
    first | intro hb | rename_i hb
    cases hb with
    | file _ _ hr1 _ => exact absurd hr hr1
    | inline _ _ _ _ hp => exact ih _ hp

theorem treeWF_lt (P : GMap Nat (List w8)) (h x y : Nat) (hw : treeWF P h x)
    (hy : treeHas P x y) : y < h := by
  have := treeWF_sub P h x y hy hw
  cases this with
  | page _ _ hlt _ _ _ => exact hlt

theorem treeWF_root (P : GMap Nat (List w8)) (h x : Nat) (hw : treeWF P h x) :
    ∃ pg, P !! x = some pg := by
  cases hw with
  | page _ pg _ hpg _ _ => exact ⟨pg, hpg⟩

/-- A well-formed tree stays one in a map agreeing on it, under a high-water mark above its
pages. -/
theorem treeWF_transfer (P P' : GMap Nat (List w8)) (h h' x : Nat) (hw : treeWF P h x) :
    (∀ y, treeHas P x y → P' !! y = P !! y ∧ y < h') → treeWF P' h' x := by
  induction hw using treeWF.rec
    (motive_2 := fun pg len _ => (∀ y, pageHas P pg y → P' !! y = P !! y ∧ y < h') →
      pageTreeWF P' h' pg len)
    (motive_3 := fun v _ => (∀ y, bucketHas P v y → P' !! y = P !! y ∧ y < h') →
      bucketWF P' h' v) with
  | page root pg _ hpg hid _ ih =>
    first | intro hag | rename_i hag
    have h0 := hag root (.root root pg hpg)
    exact .page root pg h0.2 (by rw [h0.1]; exact hpg) hid
      (ih (fun y hy => hag y (.sub root pg y hpg hy)))
  | leaf pg len hfl hw _ ih =>
    first | intro hag | rename_i hag
    exact .leaf pg len hfl hw (fun i hi hf => ih i hi hf
      (fun y hy => hag y (.bucket pg i y hfl hi hf hy)))
  | branch pg len hfl hw hk ih =>
    first | intro hag | rename_i hag
    refine .branch pg len hfl ?_ (fun i hi => ih i hi
      (fun y hy => hag y (.child pg i y hfl hi hy)))
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw
    refine ⟨h1, h2, h3, fun i hi => ⟨(h4 i hi).1, (h4 i hi).2.1, ?_⟩, h5⟩
    obtain ⟨cpg, hc⟩ := treeWF_root P h _ (hk i hi)
    exact (hag _ (.child pg i _ hfl hi (.root _ cpg hc))).2
  | file v hl hr _ ih =>
    first | intro hag | rename_i hag
    exact .file v hl hr (ih (fun y hy => hag y (.file v y hr hy)))
  | inline v hl hr hfl _ ih =>
    first | intro hag | rename_i hag
    exact .inline v hl hr hfl (ih (fun y hy => hag y (.inline v y hr hy)))

/-- A tree's keys in a map agreeing on it. -/
theorem treeKeys_transfer (P P' : GMap Nat (List w8)) (x : Nat) (lo hi : Option (List w8))
    (hk : treeKeys P x lo hi) : (∀ y, treeHas P x y → P' !! y = P !! y) → treeKeys P' x lo hi := by
  induction hk with
  | leaf root pg lo hi hpg hfl hks _ ih =>
    first | intro hag | rename_i hag
    refine .leaf root pg lo hi (by rw [hag root (.root root pg hpg)]; exact hpg) hfl hks
      (fun i hi hf hr => ih i hi hf hr (fun y hy => hag y
        (.sub root pg y hpg (.bucket pg i y hfl hi hf (.file _ y hr hy)))))
  | branch root pg lo hi kind hpg hfl hn hks hc _ ih =>
    first | intro hag | rename_i hag
    refine .branch root pg lo hi kind (by rw [hag root (.root root pg hpg)]; exact hpg) hfl hn
      hks (fun i hi => ?_) (fun i hi => ih i hi (fun y hy => hag y
        (.sub root pg y hpg (.child pg i y hfl hi hy))))
    obtain ⟨cpg, hcp, h1, h2, h3⟩ := hc i hi
    refine ⟨cpg, ?_, h1, h2, h3⟩
    rw [hag _ (.sub root pg _ hpg (.child pg i _ hfl hi (.root _ cpg hcp)))]
    exact hcp

/-! ### Keys and bounds -/

theorem lt_of_lt_le {k a b : List w8} (h1 : go.GoStringLt k a) (h2 : ¬ go.GoStringLt b a) :
    go.GoStringLt k b := by
  rcases goStringLt_trichot_r a b with h | h | h
  · exact goStringLt_trans h1 h
  · subst h; exact h1
  · exact absurd h h2

theorem hiLe_refl (hi : Option (List w8)) : hiLe hi hi :=
  fun h hh => ⟨h, hh, goStringLt_irrefl_r h⟩

theorem keyIn_widen' (lo hi lo' hi' : Option (List w8)) (k : List w8) (h : keyIn lo hi k)
    (hlo : ∀ l', lo' = some l' → ∃ l, lo = some l ∧ ¬ go.GoStringLt l l') (hhi : hiLe hi hi') :
    keyIn lo' hi' k := by
  refine ⟨fun l' hl' hk => ?_, fun h' hh' => ?_⟩
  · obtain ⟨l, hl, hle⟩ := hlo l' hl'
    exact h.1 l hl (lt_of_lt_le hk hle)
  · obtain ⟨h0, hh0, hle⟩ := hhi h' hh'
    exact lt_of_lt_le (h.2 h0 hh0) hle

open Classical in
theorem treePages_hasT (P : GMap Nat (List w8)) (x id : Nat) (v : List w8)
    (h : treePages P x !! id = some v) : treeHas P x id := by
  unfold treePages at h
  rw [GMap.lookup_filter] at h
  cases hP : P !! id with
  | none => rw [hP] at h; cases h
  | some v' =>
    rw [hP] at h
    simp only [Option.filter] at h
    split at h
    · rename_i hd; exact of_decide_eq_true hd
    · cases h

theorem treePages_get (P : GMap Nat (List w8)) (x y : Nat) (hy : treeHas P x y) :
    treePages P x !! y = P !! y := by
  unfold treePages
  rw [GMap.lookup_filter]
  cases P !! y with
  | none => rfl
  | some v => simp [Option.filter, hy]

theorem treePages_lk (P : GMap Nat (List w8)) (root id : Nat) (pg : List w8)
    (h : treePages P root !! id = some pg) : P !! id = some pg := by
  unfold treePages at h
  rw [GMap.lookup_filter] at h
  cases hP : P !! id with
  | none => rw [hP] at h; cases h
  | some v =>
    rw [hP] at h
    simp only [Option.filter] at h
    split at h
    · exact h
    · cases h

theorem treePages_sub (P : GMap Nat (List w8)) (x : Nat) : treePages P x ⊆ P :=
  fun k v h => treePages_lk P x k v h

theorem viewUnique_sub (Q P : GMap Nat (List w8)) (hs : Q ⊆ P) (hu : viewUnique P) :
    viewUnique Q := by
  obtain ⟨hb, hl⟩ := hu
  refine ⟨fun id pg h hf => ⟨fun i j hi hj hij d h1 h2 =>
      (hb id pg (hs _ _ h) hf).1 i j hi hj hij d (has_mono Q P hs _ _ h1) (has_mono Q P hs _ _ h2),
    fun i hi h1 => (hb id pg (hs _ _ h) hf).2 i hi (has_mono Q P hs _ _ h1)⟩,
    fun id pg h hf => ⟨fun i j hi hj hij hfi hfj d h1 h2 =>
      (hl id pg (hs _ _ h) hf).1 i j hi hj hij hfi hfj d (bucketHas_mono Q P hs _ _ h1)
        (bucketHas_mono Q P hs _ _ h2),
    fun i hi hf' h1 => (hl id pg (hs _ _ h) hf).2 i hi hf' (bucketHas_mono Q P hs _ _ h1)⟩⟩


/-- `lo'` is at most `lo` (`none`: no bound). -/
def loLe (lo' lo : Option (List w8)) : Prop :=
  ∀ l', lo' = some l' → ∃ l, lo = some l ∧ ¬ go.GoStringLt l l'

/-- Bounds can be widened. -/
theorem treeKeys_widen (P : GMap Nat (List w8)) (x : Nat) (lo hi lo' hi' : Option (List w8))
    (h : treeKeys P x lo hi) (hlo : loLe lo' lo) (hhi : hiLe hi hi') : treeKeys P x lo' hi' := by
  induction h generalizing lo' hi' with
  | leaf root pg lo0 hi0 hpg hfl hks hn _ =>
    exact .leaf root pg lo' hi' hpg hfl (fun i hi => keyIn_widen' _ _ _ _ _ (hks i hi) hlo hhi) hn
  | branch root pg lo0 hi0 kind hpg hfl hn hks hc _ ih =>
    refine .branch root pg lo' hi' kind hpg hfl hn
      (fun i hi => keyIn_widen' _ _ _ _ _ (hks i hi) hlo hhi) hc (fun i hi => ih i hi _ _ ?_ ?_)
    · unfold childLo
      split
      · exact hlo
      · intro l' hl'; exact ⟨l', hl', goStringLt_irrefl_r l'⟩
    · unfold childHi
      split
      · exact hiLe_refl _
      · exact hhi

/-- The keys of a well-formed tree are not below its root page's first key. -/
theorem treeKeys_first (P : GMap Nat (List w8)) (hwm x : Nat) (pg : List w8)
    (lo hi : Option (List w8)) (hw : treeWF P hwm x) (hk : treeKeys P x lo hi)
    (hpg : P !! x = some pg) (hn : 0 < pageCount pg) :
    treeKeys P x (some (pageKey pg 0)) hi := by
  revert hw hpg hn pg
  induction hk with
  | leaf root pg0 lo0 hi0 hpg0 hfl hks hn' _ =>
    intro pg hw hpg hn
    have e := Option.some.inj (hpg.symm.trans hpg0); subst e
    obtain ⟨-, -, -, hk⟩ := treeWF_page _ _ _ _ hw hpg
    have hlw : leafWF pg pg.length := by
      rcases hk with ⟨_, h, _⟩ | ⟨hb, _, _⟩
      · exact h
      · rw [hfl] at hb; exact absurd hb leaf_branch_ne
    refine .leaf root pg _ hi0 hpg hfl (fun i hi => ⟨?_, (hks i hi).2⟩) hn'
    intro l hl hlt
    cases hl
    unfold pageKey at hlt
    rw [if_pos hfl] at hlt
    by_cases hi0 : i = 0
    · subst hi0; exact goStringLt_irrefl_r _ hlt
    · exact goStringLt_irrefl_r _ (goStringLt_trans (hlw.2.2.2 0 i (by omega) hi) hlt)
  | branch root pg0 lo0 hi0 kind hpg0 hfl hn2 hks hc hch ih =>
    intro pg hw hpg hn
    have e := Option.some.inj (hpg.symm.trans hpg0); subst e
    obtain ⟨-, -, -, hk⟩ := treeWF_page _ _ _ _ hw hpg
    obtain ⟨hbw, hcw⟩ : branchWF pg pg.length hwm ∧ ∀ i < pageCount pg, treeWF P hwm (branchPgid pg i) := by
      rcases hk with ⟨hl, _, _⟩ | ⟨_, h1, h2⟩
      · rw [hfl] at hl; exact absurd hl leaf_branch_ne.symm
      · exact ⟨h1, h2⟩
    have hpk : pageKey pg 0 = branchKey pg 0 := by
      unfold pageKey; rw [if_neg (by rw [hfl]; exact leaf_branch_ne.symm)]
    refine .branch root pg _ hi0 kind hpg hfl hn2 (fun i hi => ⟨?_, (hks i hi).2⟩) hc (fun i hi => ?_)
    · intro l hl hlt
      cases hl
      rw [hpk] at hlt
      by_cases hi0 : i = 0
      · subst hi0; exact goStringLt_irrefl_r _ hlt
      · exact goStringLt_irrefl_r _ (goStringLt_trans (hbw.2.2.2.2 0 i (by omega) hi) hlt)
    · by_cases hi0 : i = 0
      · subst hi0
        obtain ⟨cpg, hcpg, hcn, -, hck⟩ := hc 0 hi
        have := ih 0 hi cpg (hcw 0 hi) hcpg hcn
        rw [hck] at this
        unfold childLo
        rw [if_pos rfl, hpk]
        exact this
      · have := hch i hi
        unfold childLo at this ⊢
        rw [if_neg hi0] at this ⊢
        exact this

/-- An old tree of the pages `P` (strict, its keys bounded) has the facts of a written one
over its own pages. -/
theorem wtreeF0_old (P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8))
    (hw : treeWF P hwm x) (hs : pagesStrict P) (hk : treeKeys P x lo hi) (hb : hwm ≤ 2 ^ 64) :
    wtreeF0 (treePages P x) x lo hi := by
  have hss := treePages_sub P x
  have hreach : ∀ d, treeHas (treePages P x) x d ↔ treeHas P x d :=
    fun d => ⟨has_mono _ _ hss x d, fun h => has_transfer P _ x d h
      (fun y hy => treePages_get P x y hy)⟩
  refine ⟨fun id => ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hreach]
    constructor
    · intro h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
      exact treePages_hasT P x id v hv
    · intro h; rw [treePages_get P x id h]; exact has_isSome P x id h
  · exact treeWF_transfer P _ hwm _ x hw (fun y hy => ⟨treePages_get P x y hy,
      Nat.lt_of_lt_of_le (treeWF_lt P hwm x y hw hy) hb⟩)
  · intro id pg h; exact hs.1 id pg (hss _ _ h)
  · exact viewUnique_sub _ _ hss hs.2
  · exact treeKeys_transfer P _ x lo hi hk (fun y hy => treePages_get P x y hy)

theorem wtreeF0_widen (Q : GMap Nat (List w8)) (x : Nat) (lo hi lo' hi' : Option (List w8))
    (h : wtreeF0 Q x lo hi) (hlo : loLe lo' lo) (hhi : hiLe hi hi') : wtreeF0 Q x lo' hi' :=
  ⟨h.1, h.2.1, h.2.2.1, treeKeys_widen Q x lo hi lo' hi' h.2.2.2 hlo hhi⟩

/-- A written tree whose pages are among `P` (agreeing), in which no two pages share a slot and
every page is below `hwm`, is a `wtree` there. -/
theorem wtreeF0_sub (Q P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8))
    (h : wtreeF0 Q x lo hi) (hsub : Q ⊆ P) (hd : pagesDisjoint P)
    (hb : ∀ id pg, P !! id = some pg → id < hwm) :
    treePages P x = Q ∧ treeWF P hwm x ∧ pagesStrict (treePages P x) ∧ treeKeys P x lo hi ∧
      pagesDisjoint (treePages P x) := by
  obtain ⟨hdom, hw, hst, hk⟩ := h
  have hQP : ∀ y, treeHas Q x y → P !! y = Q !! y := by
    intro y hy
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (has_isSome Q x y hy)
    rw [hv, hsub y v hv]
  have hreach : ∀ d, treeHas P x d ↔ treeHas Q x d :=
    fun d => ⟨has_of_wf Q P _ hsub x hw d, has_mono Q P hsub x d⟩
  have he : treePages P x = Q := by
    apply GMap.ext; intro k
    show treePages P x !! k = Q !! k
    cases hq : Q !! k with
    | none =>
      have hn : ¬ treeHas P x k := fun h => by
        have := (hdom k).2 ((hreach k).1 h); rw [hq] at this; cases this
      cases hp : treePages P x !! k with
      | none => rfl
      | some v => exact absurd (treePages_hasT P x k v hp) hn
    | some v =>
      have hr : treeHas Q x k := (hdom k).1 (by rw [hq]; rfl)
      rw [treePages_get P x k ((hreach k).2 hr), hsub k v hq]
  refine ⟨he, treeWF_transfer Q P _ hwm x hw (fun y hy => ⟨hQP y hy, ?_⟩), by rw [he]; exact hst,
    treeKeys_transfer Q P x lo hi hk hQP, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (has_isSome Q x y hy)
    exact hb y v (by rw [hQP y hy]; exact hv)
  · intro id1 pg1 id2 pg2 h1 h2 hne
    exact hd id1 pg1 id2 pg2 (treePages_lk _ _ _ _ h1) (treePages_lk _ _ _ _ h2) hne

/-! ### Unions of written trees -/

/-- The maps `f 0, ..., f (n-1)`, together. -/
def unionF (f : Nat → GMap Nat (List w8)) : Nat → GMap Nat (List w8)
  | 0 => ∅
  | n + 1 => unionF f n ∪ f n

/-- Two maps with no id in common. -/
def gdisj (A B : GMap Nat (List w8)) : Prop := ∀ id, (A !! id).isSome → (B !! id).isSome → False

theorem unionF_some (f : Nat → GMap Nat (List w8)) :
    ∀ n id v, unionF f n !! id = some v → ∃ i < n, f i !! id = some v := by
  intro n
  induction n with
  | zero => intro id v h; simp [unionF] at h
  | succ n ih =>
    intro id v h
    simp only [unionF, GMap.lookup_union] at h
    cases hu : unionF f n !! id with
    | some w =>
      rw [hu] at h; simp only [Option.some_or] at h
      obtain ⟨i, hi, h'⟩ := ih id v (hu.trans h)
      exact ⟨i, by omega, h'⟩
    | none =>
      rw [hu] at h; simp only [Option.none_or] at h
      exact ⟨n, by omega, h⟩

theorem unionF_sub (f : Nat → GMap Nat (List w8)) :
    ∀ n, (∀ i j, i < n → j < n → i ≠ j → gdisj (f i) (f j)) → ∀ i < n, f i ⊆ unionF f n := by
  intro n
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro hd i hi id v hv
    show (unionF f n ∪ f n) !! id = some v
    rw [GMap.lookup_union]
    by_cases e : i = n
    · subst e
      cases hu : unionF f i !! id with
      | some w =>
        obtain ⟨j, hj, hjv⟩ := unionF_some f i id w hu
        exact (hd j i (by omega) (by omega) (by omega) id (by rw [hjv]; rfl) (by rw [hv]; rfl)).elim
      | none => simp only [Option.none_or]; exact hv
    · have := ih (fun a b ha hb hab => hd a b (by omega) (by omega) hab) i (by omega) id v hv
      rw [this]; rfl

/-- The pages of a page `pg` at `x` and of the trees `Qs i` (`i < n`). -/
def pageU (x : Nat) (pg : List w8) (Qs : Nat → GMap Nat (List w8)) (n : Nat) :
    GMap Nat (List w8) :=
  {[x := pg]} ∪ unionF Qs n

theorem pageU_x (x : Nat) (pg : List w8) (Qs : Nat → GMap Nat (List w8)) (n : Nat) :
    pageU x pg Qs n !! x = some pg := by
  simp [pageU]

theorem pageU_sub (x : Nat) (pg : List w8) (Qs : Nat → GMap Nat (List w8)) (n : Nat)
    (hd : ∀ i j, i < n → j < n → i ≠ j → gdisj (Qs i) (Qs j)) (hxn : ∀ i < n, Qs i !! x = none)
    (i : Nat) (hi : i < n) : Qs i ⊆ pageU x pg Qs n := by
  intro id v hv
  have hne : x ≠ id := by intro e; subst e; rw [hxn i hi] at hv; cases hv
  show ({[x := pg]} ∪ unionF Qs n) !! id = some v
  rw [GMap.lookup_union, GMap.lookup_singleton_ne pg hne]
  simp only [Option.none_or]
  exact unionF_sub Qs n hd i hi id v hv

theorem pageU_some (x : Nat) (pg : List w8) (Qs : Nat → GMap Nat (List w8)) (n : Nat) (id : Nat)
    (v : List w8) (h : pageU x pg Qs n !! id = some v) :
    (id = x ∧ v = pg) ∨ ∃ i < n, Qs i !! id = some v := by
  unfold pageU at h
  rw [GMap.lookup_union] at h
  by_cases e : x = id
  · subst e; rw [GMap.lookup_singleton] at h; simp only [Option.some_or] at h; cases h
    exact Or.inl ⟨rfl, rfl⟩
  · rw [GMap.lookup_singleton_ne pg e] at h; simp only [Option.none_or] at h
    exact Or.inr (unionF_some Qs n id v h)

/-- What the union `Q` needs of its parts for its pages beside `x`. -/
theorem strict_union (Q : GMap Nat (List w8)) (x : Nat) (pg : List w8)
    (Qs : Nat → GMap Nat (List w8)) (n : Nat)
    (hsub : ∀ i < n, Qs i ⊆ Q)
    (hsome : ∀ id v, Q !! id = some v → (id = x ∧ v = pg) ∨ ∃ i < n, Qs i !! id = some v)
    (hwf : ∀ i < n, ∀ a, (Qs i !! a).isSome → treeWF (Qs i) (2 ^ 64) a)
    (hst : ∀ i < n, pagesStrict (Qs i))
    (hgood : pageGood pg)
    (hxb : pageFlags pg = branchPageFlag →
      (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → ∀ d,
        treeHas Q (branchPgid pg i) d → ¬ treeHas Q (branchPgid pg j) d) ∧
      (∀ i < pageCount pg, ¬ treeHas Q (branchPgid pg i) x))
    (hxl : pageFlags pg = leafPageFlag →
      (∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → leafFlags pg i % 2 = bucketLeafFlag →
        leafFlags pg j % 2 = bucketLeafFlag → ∀ d, bucketHas Q (leafValue pg i) d →
          ¬ bucketHas Q (leafValue pg j) d) ∧
      (∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag → ¬ bucketHas Q (leafValue pg i) x)) :
    pagesStrict Q := by
  refine ⟨fun id v hv => ?_, fun id v hv hb => ?_, fun id v hv hl => ?_⟩
  · rcases hsome id v hv with ⟨-, rfl⟩ | ⟨i, hi, hv'⟩
    · exact hgood
    · exact (hst i hi).1 id v hv'
  · rcases hsome id v hv with ⟨rfl, rfl⟩ | ⟨i, hi, hv'⟩
    · exact hxb hb
    · have hw := hwf i hi id (by rw [hv']; rfl)
      obtain ⟨-, -, -, hk⟩ := treeWF_page _ _ _ _ hw hv'
      have hcw : ∀ j < pageCount v, treeWF (Qs i) (2 ^ 64) (branchPgid v j) := by
        rcases hk with ⟨hl, _, _⟩ | ⟨_, _, h2⟩
        · rw [hb] at hl; exact absurd hl leaf_branch_ne.symm
        · exact h2
      have back : ∀ j < pageCount v, ∀ d, treeHas Q (branchPgid v j) d →
          treeHas (Qs i) (branchPgid v j) d :=
        fun j hj d h => has_of_wf (Qs i) Q _ (hsub i hi) _ (hcw j hj) d h
      obtain ⟨u1, u2⟩ := (hst i hi).2.1 id v hv' hb
      exact ⟨fun a b ha hb' hab d h1 h2 => u1 a b ha hb' hab d (back a ha d h1) (back b hb' d h2),
        fun a ha h1 => u2 a ha (back a ha id h1)⟩
  · rcases hsome id v hv with ⟨rfl, rfl⟩ | ⟨i, hi, hv'⟩
    · exact hxl hl
    · have hw := hwf i hi id (by rw [hv']; rfl)
      obtain ⟨-, -, -, hk⟩ := treeWF_page _ _ _ _ hw hv'
      have hbw : ∀ j < pageCount v, leafFlags v j % 2 = bucketLeafFlag →
          bucketWF (Qs i) (2 ^ 64) (leafValue v j) := by
        rcases hk with ⟨_, _, h2⟩ | ⟨hb, _, _⟩
        · exact h2
        · rw [hl] at hb; exact absurd hb leaf_branch_ne
      have back : ∀ j < pageCount v, leafFlags v j % 2 = bucketLeafFlag → ∀ d,
          bucketHas Q (leafValue v j) d → bucketHas (Qs i) (leafValue v j) d :=
        fun j hj hf d h => bucketHas_of_wf (Qs i) Q _ (hsub i hi) _ (hbw j hj hf) d h
      obtain ⟨u1, u2⟩ := (hst i hi).2.2 id v hv' hl
      exact ⟨fun a b ha hb' hab hfa hfb d h1 h2 =>
          u1 a b ha hb' hab hfa hfb d (back a ha hfa d h1) (back b hb' hfb d h2),
        fun a ha hfa h1 => u2 a ha hfa (back a ha hfa id h1)⟩

/-- A written branch page and its children's written trees (`wtreeQ_branch`'s pure part). -/
theorem wtreeF0_branch (x : Nat) (pg : List w8) (lo hi : Option (List w8)) (kind : Nat)
    (Qs : Nat → GMap Nat (List w8)) (Hs : Nat → Option (List w8))
    (hf : pageFlags pg = branchPageFlag) (hn : 2 ≤ pageCount pg)
    (hid : pageId pg = x) (hx : x < 2 ^ 64) (hwfb : branchWF pg pg.length (2 ^ 64))
    (hks : ∀ i < pageCount pg, 0 < branchKsize pg i)
    (hin : ∀ i < pageCount pg, keyIn lo hi (branchKey pg i))
    (hc : ∀ i < pageCount pg, ∃ cpg, Qs i !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧
      pageFlags cpg = kind ∧ pageKey cpg 0 = branchKey pg i)
    (hH : ∀ i < pageCount pg, hiLe (Hs i) (childHi hi (branchKey pg) (pageCount pg) i))
    (hQ : ∀ i < pageCount pg, wtreeF0 (Qs i) (branchPgid pg i) (some (branchKey pg i)) (Hs i))
    (hd : ∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → gdisj (Qs i) (Qs j))
    (hxn : ∀ i < pageCount pg, Qs i !! x = none) :
    wtreeF0 (pageU x pg Qs (pageCount pg)) x lo hi := by
  have hQx := pageU_x x pg Qs (pageCount pg)
  have hsub := pageU_sub x pg Qs (pageCount pg) hd hxn
  have hwf : ∀ i < pageCount pg, ∀ a, (Qs i !! a).isSome → treeWF (Qs i) (2 ^ 64) a :=
    fun i hi a ha => treeWF_sub _ _ _ a (((hQ i hi).1 a).1 ha) (hQ i hi).2.1
  have hcin : ∀ i < pageCount pg, (Qs i !! branchPgid pg i).isSome := by
    intro i hi; obtain ⟨cpg, h, -⟩ := hc i hi; rw [h]; rfl
  have back : ∀ i < pageCount pg, ∀ d, treeHas (pageU x pg Qs (pageCount pg)) (branchPgid pg i) d →
      treeHas (Qs i) (branchPgid pg i) d :=
    fun i hi d h => has_of_wf _ _ _ (hsub i hi) _ (hQ i hi).2.1 d h
  have hagree : ∀ i < pageCount pg, ∀ y, treeHas (Qs i) (branchPgid pg i) y →
      pageU x pg Qs (pageCount pg) !! y = Qs i !! y := by
    intro i hi y hy
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (has_isSome _ _ _ hy)
    rw [hv, hsub i hi y v hv]
  refine ⟨fun id => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    rcases pageU_some x pg Qs _ id v hv with ⟨rfl, -⟩ | ⟨i, hi, hv'⟩
    · exact .root id pg hQx
    · exact .sub x pg id hQx (.child pg i id hf hi
        (has_mono _ _ (hsub i hi) _ _ (((hQ i hi).1 id).1 (by rw [hv']; rfl))))
  · cases h with
    | root _ _ hr => rw [hr]; rfl
    | sub _ pg' _ hpg' hph =>
      rw [hQx] at hpg'; cases hpg'
      cases hph with
      | child _ i _ _ hi ht =>
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (has_isSome _ _ _ (back i hi id ht))
        rw [hsub i hi id v hv]; rfl
      | bucket _ _ _ hl _ _ _ => rw [hf] at hl; exact absurd hl leaf_branch_ne.symm
  · exact .page x pg hx hQx hid (.branch pg pg.length hf hwfb (fun i hi =>
      treeWF_transfer _ _ _ _ _ (hQ i hi).2.1 (fun y hy =>
        ⟨hagree i hi y hy, treeWF_lt _ _ _ _ (hQ i hi).2.1 hy⟩)))
  · refine strict_union _ x pg Qs (pageCount pg) hsub (pageU_some x pg Qs _) hwf
      (fun i hi => (hQ i hi).2.2.1) ⟨fun hl => ?_, fun _ => hks⟩ (fun _ => ⟨?_, ?_⟩) (fun hl => ?_)
    · rw [hf] at hl; exact absurd hl leaf_branch_ne.symm
    · intro i j hi hj hij d h1 h2
      have a := has_isSome _ _ _ (back i hi d h1)
      have b := has_isSome _ _ _ (back j hj d h2)
      exact hd i j hi hj hij d a b
    · intro i hi h1
      have a := has_isSome _ _ _ (back i hi x h1)
      rw [hxn i hi] at a; cases a
    · rw [hf] at hl; exact absurd hl leaf_branch_ne.symm
  · refine .branch x pg lo hi kind hQx hf hn hin (fun i hi => ?_) (fun i hi => ?_)
    · obtain ⟨cpg, h1, h2, h3, h4⟩ := hc i hi
      exact ⟨cpg, hsub i hi _ _ h1, h2, h3, h4⟩
    · refine treeKeys_widen _ _ _ _ _ _ (treeKeys_transfer _ _ _ _ _ (hQ i hi).2.2.2 (hagree i hi))
        ?_ (hH i hi)
      unfold childLo
      split
      · intro l' hl'
        exact ⟨branchKey pg i, rfl, (hin i hi).1 l' hl'⟩
      · intro l' hl'; cases hl'; exact ⟨_, rfl, goStringLt_irrefl_r _⟩

theorem bucketLeafFlag_ne_zero : (0 : Nat) ≠ bucketLeafFlag := by unfold bucketLeafFlag; decide

/-- A written leaf page and its nested buckets' written trees (`wtreeQ_leaf`'s pure part). -/
theorem wtreeF0_leaf (x : Nat) (pg : List w8) (lo hi : Option (List w8))
    (Qs : Nat → GMap Nat (List w8))
    (hf : pageFlags pg = leafPageFlag) (hid : pageId pg = x) (hx : x < 2 ^ 64)
    (hwfl : leafWF pg pg.length) (hks : ∀ i < pageCount pg, 0 < leafKsize pg i)
    (hin : ∀ i < pageCount pg, keyIn lo hi (leafKey pg i))
    (hb : ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag →
      16 ≤ (leafValue pg i).length ∧
      (inBucketRoot (leafValue pg i) = 0 → inlineGood (inlinePage (leafValue pg i))))
    (hQ : ∀ i < pageCount pg, (leafFlags pg i % 2 = bucketLeafFlag ∧
        inBucketRoot (leafValue pg i) ≠ 0 →
        wtreeF0 (Qs i) (inBucketRoot (leafValue pg i)) none none) ∧
      (¬ (leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0) → Qs i = ∅))
    (hd : ∀ i j, i < pageCount pg → j < pageCount pg → i ≠ j → gdisj (Qs i) (Qs j))
    (hxn : ∀ i < pageCount pg, Qs i !! x = none) :
    wtreeF0 (pageU x pg Qs (pageCount pg)) x lo hi := by
  have hQx := pageU_x x pg Qs (pageCount pg)
  have hsub := pageU_sub x pg Qs (pageCount pg) hd hxn
  have hnon : ∀ i < pageCount pg, ∀ a, (Qs i !! a).isSome →
      leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0 := by
    intro i hi a ha
    apply Classical.byContradiction
    intro hn
    rw [(hQ i hi).2 hn] at ha; simp at ha
  have hwf : ∀ i < pageCount pg, ∀ a, (Qs i !! a).isSome → treeWF (Qs i) (2 ^ 64) a := by
    intro i hi a ha
    have hq := (hQ i hi).1 (hnon i hi a ha)
    exact treeWF_sub _ _ _ a ((hq.1 a).1 ha) hq.2.1
  have hst : ∀ i < pageCount pg, pagesStrict (Qs i) := by
    intro i hi
    by_cases h : leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0
    · exact ((hQ i hi).1 h).2.2.1
    · rw [(hQ i hi).2 h]
      exact ⟨fun id v hv => by simp at hv, fun id v hv => by simp at hv, fun id v hv => by simp at hv⟩
  /- A nested bucket's pages in the union are its tree's. -/
  have bkt : ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag → ∀ d,
      bucketHas (pageU x pg Qs (pageCount pg)) (leafValue pg i) d → (Qs i !! d).isSome := by
    intro i hi hfi d h
    cases h with
    | file _ _ hr ht =>
      have hq := (hQ i hi).1 ⟨hfi, hr⟩
      exact has_isSome _ _ _ (has_of_wf _ _ _ (hsub i hi) _ hq.2.1 d ht)
    | inline _ _ hr0 hp =>
      have hig := (hb i hi hfi).2 hr0
      cases hp with
      | child _ _ _ hbr _ _ => rw [hig.2.1] at hbr; exact absurd hbr leaf_branch_ne
      | bucket _ j _ _ hj hfj _ =>
        have := (hig.2.2.2.2 j hj).2
        rw [this] at hfj; exact absurd hfj bucketLeafFlag_ne_zero
  have hagree : ∀ i < pageCount pg, ∀ y, (Qs i !! y).isSome →
      pageU x pg Qs (pageCount pg) !! y = Qs i !! y := by
    intro i hi y hy
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hy
    rw [hv, hsub i hi y v hv]
  refine ⟨fun id => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    rcases pageU_some x pg Qs _ id v hv with ⟨rfl, -⟩ | ⟨i, hi, hv'⟩
    · exact .root id pg hQx
    · have hnb := hnon i hi id (by rw [hv']; rfl)
      have hq := (hQ i hi).1 hnb
      exact .sub x pg id hQx (.bucket pg i id hf hi hnb.1 (.file _ id hnb.2
        (has_mono _ _ (hsub i hi) _ _ ((hq.1 id).1 (by rw [hv']; rfl)))))
  · cases h with
    | root _ _ hr => rw [hr]; rfl
    | sub _ pg' _ hpg' hph =>
      rw [hQx] at hpg'; cases hpg'
      cases hph with
      | child _ _ _ hbr _ _ => rw [hf] at hbr; exact absurd hbr leaf_branch_ne
      | bucket _ i _ _ hi hfi hbh =>
        have := bkt i hi hfi id hbh
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
        rw [hsub i hi id v hv]; rfl
  · refine .page x pg hx hQx hid (.leaf pg pg.length hf hwfl (fun i hi hfi => ?_))
    by_cases hr : inBucketRoot (leafValue pg i) = 0
    · have hig := (hb i hi hfi).2 hr
      exact .inline _ (hb i hi hfi).1 hr hig.2.1 (.leaf _ _ hig.2.1 hig.2.2.1 (fun j hj hfj => by
        have := (hig.2.2.2.2 j hj).2
        rw [this] at hfj; exact absurd hfj bucketLeafFlag_ne_zero))
    · have hq := (hQ i hi).1 ⟨hfi, hr⟩
      exact .file _ (hb i hi hfi).1 hr (treeWF_transfer _ _ _ _ _ hq.2.1 (fun y hy =>
        ⟨hagree i hi y (has_isSome _ _ _ hy), treeWF_lt _ _ _ _ hq.2.1 hy⟩))
  · refine strict_union _ x pg Qs (pageCount pg) hsub (pageU_some x pg Qs _) hwf hst
      ⟨fun _ i hi => ⟨hks i hi, fun hfi hr => (hb i hi hfi).2 hr⟩,
        fun hb' => by rw [hf] at hb'; exact absurd hb' leaf_branch_ne⟩
      (fun hb' => by rw [hf] at hb'; exact absurd hb' leaf_branch_ne) (fun _ => ⟨?_, ?_⟩)
    · intro i j hi hj hij hfi hfj d h1 h2
      exact hd i j hi hj hij d (bkt i hi hfi d h1) (bkt j hj hfj d h2)
    · intro i hi hfi h1
      have a := bkt i hi hfi x h1
      rw [hxn i hi] at a; cases a
  · refine .leaf x pg lo hi hQx hf hin (fun i hi hfi hr => ?_)
    have hq := (hQ i hi).1 ⟨hfi, hr⟩
    exact treeKeys_transfer _ _ _ _ _ hq.2.2.2 (fun y hy => hagree i hi y (has_isSome _ _ _ hy))


/-! ### Heights (all leaves at one depth) -/

theorem hts_restrict (Q P : GMap Nat (List w8)) (pht : Nat → Nat) (hs : Q ⊆ P)
    (h : pageHts P pht) : pageHts Q pht :=
  fun id pg hq => h id pg (hs id pg hq)

/-- A written tree's pages hold its branches' children. -/
theorem wtreeF0_closed (Q : GMap Nat (List w8)) (c : Nat) (lo hi : Option (List w8))
    (h : wtreeF0 Q c lo hi) :
    ∀ id v, Q !! id = some v → pageFlags v = branchPageFlag → ∀ j < pageCount v,
      (Q !! branchPgid v j).isSome := by
  intro id v hv hb j hj
  have hid : treeHas Q c id := (h.1 id).1 (by rw [hv]; rfl)
  have hw := treeWF_sub Q _ c id hid h.2.1
  obtain ⟨-, -, -, hk⟩ := treeWF_page Q _ id v hw hv
  rcases hk with ⟨hl, -⟩ | ⟨-, -, hch⟩
  · rw [hb] at hl; exact absurd hl (by unfold branchPageFlag leafPageFlag; decide)
  · obtain ⟨cpg, hc⟩ := treeWF_root Q _ _ (hch j hj)
    rw [hc]; rfl

open Classical in
/-- The heights of a page `pg` at `x` and of the trees `Qs i` under it (`pageU`), `x`'s `hx`. -/
theorem hts_pageU (x : Nat) (pg : List w8) (Qs : Nat → GMap Nat (List w8)) (n hx : Nat)
    (phts : Nat → Nat → Nat)
    (hd : ∀ i j, i < n → j < n → i ≠ j → gdisj (Qs i) (Qs j)) (hxn : ∀ i < n, Qs i !! x = none)
    (hts : ∀ i < n, pageHts (Qs i) (phts i))
    (hcl : ∀ i < n, ∀ id v, Qs i !! id = some v → pageFlags v = branchPageFlag →
      ∀ j < pageCount v, (Qs i !! branchPgid v j).isSome)
    (hxl : pageFlags pg = leafPageFlag → hx = 0)
    (hxb : pageFlags pg = branchPageFlag → ∀ j < pageCount pg, ∃ i < n,
      (Qs i !! branchPgid pg j).isSome ∧ phts i (branchPgid pg j) + 1 = hx) :
    ∃ pht, pageHts (pageU x pg Qs n) pht ∧ pht x = hx := by
  let pht : Nat → Nat := fun y =>
    if y = x then hx else
    if h : ∃ i, i < n ∧ (Qs i !! y).isSome then phts (Classical.choose h) y else 0
  have hat : ∀ i < n, ∀ y, (Qs i !! y).isSome → pht y = phts i y := by
    intro i hi y hy
    have hyx : y ≠ x := by
      intro e; subst e; rw [hxn i hi] at hy; cases hy
    have hex : ∃ i, i < n ∧ (Qs i !! y).isSome := ⟨i, hi, hy⟩
    show (if y = x then hx else
      if h : ∃ i, i < n ∧ (Qs i !! y).isSome then phts (Classical.choose h) y else 0) = phts i y
    rw [if_neg hyx, dif_pos hex]
    obtain ⟨hi', hy'⟩ := Classical.choose_spec hex
    by_cases e : Classical.choose hex = i
    · rw [e]
    · exact (hd _ i hi' hi e y hy' hy).elim
  refine ⟨pht, fun id v hv => ?_, by show (if x = x then hx else _) = hx; rw [if_pos rfl]⟩
  rcases pageU_some x pg Qs n id v hv with ⟨rfl, rfl⟩ | ⟨i, hi, hq⟩
  · have hpx : pht id = hx := by show (if id = id then hx else _) = hx; rw [if_pos rfl]
    refine ⟨fun hl => by rw [hpx]; exact hxl hl, fun hb j hj => ?_⟩
    obtain ⟨i, hi, hs, he⟩ := hxb hb j hj
    rw [hat i hi _ hs, hpx]; exact he
  · have hs : (Qs i !! id).isSome := by rw [hq]; rfl
    rw [hat i hi id hs]
    obtain ⟨h1, h2⟩ := hts i hi id v hq
    refine ⟨h1, fun hb j hj => ?_⟩
    rw [hat i hi _ (hcl i hi id v hq hb j hj)]
    exact h2 hb j hj

/-- An old tree of the pages `P`, whose pages have heights, has the facts of a written one over
its own pages, and its height. -/
theorem wtreeF_old (P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8))
    (hw : treeWF P hwm x) (hs : pagesStrict P) (hk : treeKeys P x lo hi) (hb : hwm ≤ 2 ^ 64)
    (pht : Nat → Nat) (hh : pageHts P pht) :
    wtreeF (treePages P x) x lo hi ∧ qHt (treePages P x) x (pht x) :=
  have hq : qHt (treePages P x) x (pht x) := ⟨pht, hts_restrict _ _ pht (treePages_sub P x) hh, rfl⟩
  ⟨⟨wtreeF0_old P hwm x lo hi hw hs hk hb, _, hq⟩, hq⟩

theorem wtreeF_widen (Q : GMap Nat (List w8)) (x : Nat) (lo hi lo' hi' : Option (List w8))
    (h : wtreeF Q x lo hi) (hlo : loLe lo' lo) (hhi : hiLe hi hi') : wtreeF Q x lo' hi' :=
  ⟨wtreeF0_widen Q x lo hi lo' hi' h.1 hlo hhi, h.2⟩

/-- A written tree whose pages are among `P` (see `wtreeF0_sub`), its leaves at one depth. -/
theorem wtreeF_sub (Q P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8))
    (h : wtreeF Q x lo hi) (hsub : Q ⊆ P) (hd : pagesDisjoint P)
    (hb : ∀ id pg, P !! id = some pg → id < hwm) :
    treePages P x = Q ∧ treeWF P hwm x ∧ pagesStrict (treePages P x) ∧ treeKeys P x lo hi ∧
      pagesDisjoint (treePages P x) ∧ ∃ pht, pageHts (treePages P x) pht := by
  obtain ⟨he, h1, h2, h3, h4⟩ := wtreeF0_sub Q P hwm x lo hi h.1 hsub hd hb
  obtain ⟨-, pht, hp, -⟩ := h.2
  exact ⟨he, h1, h2, h3, h4, pht, by rw [he]; exact hp⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- Tokens of two sets of pages are of disjoint sets. -/
theorem pgToks_disj (γ : GName) (Q1 Q2 : GMap Nat (List w8)) :
    pgToks (GF := GF) γ Q1 ∗ pgToks γ Q2 ⊢ ⌜∀ id, (Q1 !! id).isSome → (Q2 !! id).isSome → False⌝ := by
  by_cases h : ∀ id, (Q1 !! id).isSome → (Q2 !! id).isSome → False
  · iintro _; ipureintro; exact h
  · have hex : ∃ id, (Q1 !! id).isSome ∧ (Q2 !! id).isSome := by
      apply Classical.byContradiction
      intro hn; exact h (fun id a b => hn ⟨id, a, b⟩)
    obtain ⟨id, h1, h2⟩ := hex
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h2
    unfold pgToks
    iintro ⟨H1, H2⟩
    icases (BigSepM.bigSepM_delete (M := GMap Nat)
      (Φ := fun id (_ : List w8) => iprop(id ↪[γ] ())) (show Std.get? Q1 id = some a from ha)).1
      $$ H1 with ⟨T1, -⟩
    icases (BigSepM.bigSepM_delete (M := GMap Nat)
      (Φ := fun id (_ : List w8) => iprop(id ↪[γ] ())) (show Std.get? Q2 id = some b from hb)).1
      $$ H2 with ⟨T2, -⟩
    ihave %Hne := ghostMapElem_ne (GF := GF) γ id id (DFrac.own 1) () () $$ T1 T2
    exact absurd rfl Hne

theorem pgToks_union (γ : GName) (Q1 Q2 : GMap Nat (List w8))
    (hd : ∀ id, (Q1 !! id).isSome → (Q2 !! id).isSome → False) :
    pgToks (GF := GF) γ Q1 ∗ pgToks γ Q2 ⊣⊢ pgToks γ (Q1 ∪ Q2) := by
  unfold pgToks
  rw [gmap_union_eq]
  exact (BigSepM.bigSepM_union (M := GMap Nat) (fun k ⟨h1, h2⟩ => hd k h1 h2)).symm

/-! ### Lists of resources over `range n` -/

theorem bigSepL_range_choose {T : Type} (d : T) (Φ : Nat → T → IProp GF) :
    ∀ n, ([∗list] i ∈ List.range n, ∃ t, Φ i t) ⊢ ∃ f : Nat → T, [∗list] i ∈ List.range n, Φ i (f i) := by
  intro n
  induction n with
  | zero =>
    rw [List.range_zero]
    iintro _
    iexists (fun _ => d)
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n ih =>
    rw [List.range_succ]
    iintro H
    icases (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ H with ⟨H, ⟨%t, Ht⟩⟩
    ihave H := ih $$ H
    icases H with ⟨%f, H⟩
    iexists (fun i => if i = n then t else f i)
    iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    isplitl [H]
    · iapply (BigSepL.bigSepL_mono (PROP := IProp GF) ?_) $$ H
      intro k i hk
      have hi : i < n := by
        have := List.mem_range.1 (List.mem_of_getElem? hk); exact this
      simp only [show i ≠ n by omega, if_false]
      exact .rfl
    · simp only [List.length_range, if_true]
      iexact Ht

theorem bigSepL_range_pure (φ : Nat → Prop) (R : Nat → IProp GF) (n : Nat) :
    ([∗list] i ∈ List.range n, ⌜φ i⌝ ∗ R i) ⊢ ⌜∀ i < n, φ i⌝ ∗ [∗list] i ∈ List.range n, R i := by
  iintro H
  icases (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).1 $$ H with ⟨Hp, H⟩
  ihave %Hp := (BigSepL.bigSepL_pure_intro (PROP := IProp GF)) $$ Hp
  iframe H
  ipureintro
  intro i hi
  exact Hp i i (List.getElem?_range hi)

theorem pgToks_disjK (γ : GName) (Q1 Q2 : GMap Nat (List w8)) :
    pgToks (GF := GF) γ Q1 ∗ pgToks γ Q2 ⊢ ⌜gdisj Q1 Q2⌝ ∗ pgToks γ Q1 ∗ pgToks γ Q2 := by
  by_cases h : gdisj Q1 Q2
  · iintro H; iframe H; ipureintro; exact h
  · iintro H
    ihave %h' := pgToks_disj γ Q1 Q2 $$ H
    exact absurd h' h

theorem pgToks_emptyT (γ : GName) : ⊢ pgToks (GF := GF) γ (∅ : GMap Nat (List w8)) := by
  unfold pgToks
  iapply (BigSepM.bigSepM_empty (M := GMap Nat) (PROP := IProp GF)).2
  iempintro

theorem toks_range (γ : GName) (f : Nat → GMap Nat (List w8)) :
    ∀ n, ([∗list] i ∈ List.range n, pgToks (GF := GF) γ (f i)) ⊢
      ⌜∀ i j, i < n → j < n → i ≠ j → gdisj (f i) (f j)⌝ ∗ pgToks γ (unionF f n) := by
  intro n
  induction n with
  | zero =>
    iintro _
    isplitr
    · ipureintro; intro i _ hi; omega
    · show iprop(emp) ⊢ pgToks γ (∅ : GMap Nat (List w8))
      exact pgToks_emptyT γ
  | succ n ih =>
    rw [List.range_succ]
    iintro H
    icases (BigSepL.bigSepL_snoc (PROP := IProp GF)).1 $$ H with ⟨H, Hn⟩
    ihave H := ih $$ H
    icases H with ⟨%hd, H⟩
    icases pgToks_disjK γ (unionF f n) (f n) $$ [H Hn] with ⟨%hdn, H, Hn⟩
    · iframe
    isplitr
    · ipureintro
      have hj : ∀ j < n, gdisj (f j) (f n) := fun j hj id a b =>
        hdn id (by obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 a
                   rw [unionF_sub f n hd j hj id v hv]; rfl) b
      intro i j hi hj' hij
      by_cases ei : i = n
      · subst ei
        have : j < i := by omega
        exact fun id a b => hj j this id b a
      · by_cases ej : j = n
        · subst ej; exact hj i (by omega)
        · exact hd i j (by omega) (by omega) hij
    · show _ ⊢ pgToks γ (unionF f n ∪ f n)
      iapply (pgToks_union γ (unionF f n) (f n) hdn).1

theorem pgToks_singleT (γ : GName) (x : Nat) (pg : List w8) :
    (x ↪[γ] () : IProp GF) ⊢ pgToks γ ({[x := pg]} : GMap Nat (List w8)) := by
  unfold pgToks
  exact (BigSepM.bigSepM_singleton (M := GMap Nat) (PROP := IProp GF)
    (Φ := fun id (_ : List w8) => iprop(id ↪[γ] ()))).2

/-- The facts of a branch's child `i` (its tree's pages, root page, upper bound, height `h`). -/
def brFact (pg : List w8) (hi : Option (List w8)) (kind h : Nat) (i : Nat)
    (t : GMap Nat (List w8) × List w8 × Option (List w8)) : Prop :=
  t.1 !! branchPgid pg i = some t.2.1 ∧ 0 < pageCount t.2.1 ∧ pageFlags t.2.1 = kind ∧
  pageKey t.2.1 0 = branchKey pg i ∧ hiLe t.2.2 (childHi hi (branchKey pg) (pageCount pg) i) ∧
  wtreeF0 t.1 (branchPgid pg i) (some (branchKey pg i)) t.2.2 ∧ qHt t.1 (branchPgid pg i) h

/-- The facts of a leaf's entry `i` (its nested bucket's tree's pages, if any). -/
def lfFact (pg : List w8) (i : Nat) (Q : GMap Nat (List w8)) : Prop :=
  (leafFlags pg i % 2 = bucketLeafFlag → 16 ≤ (leafValue pg i).length ∧
    (inBucketRoot (leafValue pg i) = 0 → inlineGood (inlinePage (leafValue pg i)))) ∧
  (leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0 →
    wtreeF Q (inBucketRoot (leafValue pg i)) none none) ∧
  (¬ (leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0) → Q = ∅)

/-- The page's token and its parts' tokens: disjoint, the parts not holding `x`. -/
theorem toks_page (γ : GName) (x : Nat) (pg : List w8) (Qs : Nat → GMap Nat (List w8)) (n : Nat) :
    (x ↪[γ] () : IProp GF) ∗ ([∗list] i ∈ List.range n, pgToks γ (Qs i)) ⊢
      ⌜(∀ i j, i < n → j < n → i ≠ j → gdisj (Qs i) (Qs j)) ∧ ∀ i < n, Qs i !! x = none⌝ ∗
      pgToks γ (pageU x pg Qs n) := by
  iintro ⟨Hx, Hl⟩
  ihave Hx := pgToks_singleT γ x pg $$ Hx
  icases toks_range γ Qs n $$ Hl with ⟨%hd, Hu⟩
  icases pgToks_disjK γ ({[x := pg]} : GMap Nat (List w8)) (unionF Qs n) $$ [Hx Hu] with ⟨%hxd, Hx, Hu⟩
  · iframe
  isplitr
  · ipureintro
    refine ⟨hd, fun i hi => ?_⟩
    cases h : Qs i !! x with
    | none => rfl
    | some v =>
      exact (hxd x (by simp) (by rw [unionF_sub Qs n hd i hi x v h]; rfl)).elim
  · unfold pageU
    iapply (pgToks_union γ _ _ hxd).1
    iframe


/-- An old tree of the view, its pages with heights `pht`: its tokens are a written tree, of
height `pht x`. -/
theorem wtreeQ_old (γ : GName) (P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8))
    (hw : treeWF P hwm x) (hs : pagesStrict P) (hk : treeKeys P x lo hi) (hb : hwm ≤ 2 ^ 64)
    (pht : Nat → Nat) (hh : pageHts P pht) :
    pgToks (GF := GF) γ (treePages P x) ⊢
      wtreeQ γ (treePages P x) x lo hi ∗ ⌜qHt (treePages P x) x (pht x)⌝ := by
  iintro H
  unfold wtreeQ
  iframe H
  ipureintro
  exact ⟨(wtreeF_old P hwm x lo hi hw hs hk hb pht hh).1, (wtreeF_old P hwm x lo hi hw hs hk hb pht hh).2⟩

/-- The end: a written tree whose pages are among `P` is `wtree` there. -/
theorem wtree_of_Q (γ : GName) (Q P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8))
    (hsub : Q ⊆ P) (hd : pagesDisjoint P) (hb : ∀ id pg, P !! id = some pg → id < hwm) :
    wtreeQ (GF := GF) γ Q x lo hi ⊢ wtree γ P hwm x lo hi := by
  unfold wtreeQ wtree
  iintro ⟨H, %Hf⟩
  obtain ⟨he, h1, h2, h3, h4, h5⟩ := wtreeF_sub Q P hwm x lo hi Hf hsub hd hb
  rw [he]
  iframe H
  ipureintro
  rw [← he]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A written branch page `pg` at `x` (its token), its children's written trees (child `i`
from its key, below the next key or `hi`; their roots of one kind, with the branch's keys as
their first keys; all of height `h`): the branch's written tree, of height `h + 1`. -/
theorem wtreeQ_branch (γ : GName) (x : Nat) (pg : List w8) (lo hi : Option (List w8))
    (kind h : Nat) (hf : pageFlags pg = branchPageFlag) (hn : 2 ≤ pageCount pg)
    (hid : pageId pg = x) (hx : x < 2 ^ 64) (hwf : branchWF pg pg.length (2 ^ 64))
    (hks : ∀ i < pageCount pg, 0 < branchKsize pg i)
    (hin : ∀ i < pageCount pg, keyIn lo hi (branchKey pg i)) :
    (x ↪[γ] () : IProp GF) ∗
      ([∗list] i ∈ List.range (pageCount pg), ∃ Q cpg H,
        ⌜Q !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧ pageFlags cpg = kind ∧
          pageKey cpg 0 = branchKey pg i ∧ hiLe H (childHi hi (branchKey pg) (pageCount pg) i) ∧
          qHt Q (branchPgid pg i) h⌝ ∗
        wtreeQ γ Q (branchPgid pg i) (some (branchKey pg i)) H) ⊢
    ∃ Q, ⌜Q !! x = some pg ∧ qHt Q x (h + 1)⌝ ∗ wtreeQ γ Q x lo hi := by
  iintro ⟨Hx, Hl⟩
  ihave Hl := (BigSepL.bigSepL_mono (PROP := IProp GF)
    (Ψ := fun _ i => iprop(∃ t : GMap Nat (List w8) × List w8 × Option (List w8),
      ⌜brFact pg hi kind h i t⌝ ∗ pgToks γ t.1)) ?_) $$ Hl
  · intro k i _
    iintro ⟨%Q, %cpg, %H, %hf, HQ⟩
    unfold wtreeQ
    icases HQ with ⟨HQ, %hw⟩
    iexists (Q, cpg, H)
    iframe
    ipureintro
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hw.1, hf.2.2.2.2.2⟩
  ihave Hl := bigSepL_range_choose ((∅ : GMap Nat (List w8)), ([] : List w8), (none : Option (List w8)))
    (fun i t => iprop(⌜brFact pg hi kind h i t⌝ ∗ pgToks (GF := GF) γ t.1)) (pageCount pg) $$ Hl
  icases Hl with ⟨%f, Hl⟩
  icases bigSepL_range_pure (fun i => brFact pg hi kind h i (f i)) (fun i => pgToks (GF := GF) γ (f i).1)
    (pageCount pg) $$ Hl with ⟨%hfs, Hl⟩
  icases toks_page γ x pg (fun i => (f i).1) (pageCount pg) $$ [Hx Hl] with ⟨%hd, Ht⟩
  · iframe
  have hch : ∀ i, ∃ p : Nat → Nat, i < pageCount pg →
      pageHts (f i).1 p ∧ p (branchPgid pg i) = h := by
    intro i
    by_cases hi' : i < pageCount pg
    · obtain ⟨p, hp, hpv⟩ := (hfs i hi').2.2.2.2.2.2
      exact ⟨p, fun _ => ⟨hp, hpv⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hi'⟩
  have hq : qHt (pageU x pg (fun i => (f i).1) (pageCount pg)) x (h + 1) :=
    hts_pageU x pg (fun i => (f i).1) (pageCount pg) (h + 1) (fun i => Classical.choose (hch i))
      hd.1 hd.2 (fun i hi' => (Classical.choose_spec (hch i) hi').1)
      (fun i hi' => wtreeF0_closed _ _ _ _ (hfs i hi').2.2.2.2.2.1)
      (fun hl => by rw [hf] at hl; exact absurd hl (by unfold branchPageFlag leafPageFlag; decide))
      (fun _ j hj => ⟨j, hj, by rw [(hfs j hj).1]; rfl,
        by rw [(Classical.choose_spec (hch j) hj).2]⟩)
  iexists (pageU x pg (fun i => (f i).1) (pageCount pg))
  isplitr
  · ipureintro; exact ⟨pageU_x _ _ _ _, hq⟩
  unfold wtreeQ
  iframe
  ipureintro
  exact ⟨wtreeF0_branch x pg lo hi kind (fun i => (f i).1) (fun i => (f i).2.2) hf hn hid hx hwf hks hin
    (fun i hi' => ⟨(f i).2.1, (hfs i hi').1, (hfs i hi').2.1, (hfs i hi').2.2.1, (hfs i hi').2.2.2.1⟩)
    (fun i hi' => (hfs i hi').2.2.2.2.1) (fun i hi' => (hfs i hi').2.2.2.2.2.1) hd.1 hd.2, _, hq⟩

/-- A written leaf page `pg` at `x` (its token), its nested buckets' written values: the leaf's
written tree, of height 0. -/
theorem wtreeQ_leaf (γ : GName) (x : Nat) (pg : List w8) (lo hi : Option (List w8))
    (hf : pageFlags pg = leafPageFlag) (hid : pageId pg = x) (hx : x < 2 ^ 64)
    (hwf : leafWF pg pg.length) (hks : ∀ i < pageCount pg, 0 < leafKsize pg i)
    (hin : ∀ i < pageCount pg, keyIn lo hi (leafKey pg i)) :
    (x ↪[γ] () : IProp GF) ∗
      ([∗list] i ∈ List.range (pageCount pg),
        if leafFlags pg i % 2 = bucketLeafFlag then wbktQ γ (leafValue pg i) else emp) ⊢
    ∃ Q, ⌜Q !! x = some pg ∧ qHt Q x 0⌝ ∗ wtreeQ γ Q x lo hi := by
  iintro ⟨Hx, Hl⟩
  ihave Hl := (BigSepL.bigSepL_mono (PROP := IProp GF)
    (Ψ := fun _ i => iprop(∃ Q : GMap Nat (List w8), ⌜lfFact pg i Q⌝ ∗ pgToks γ Q)) ?_) $$ Hl
  · intro k i _
    by_cases hfi : leafFlags pg i % 2 = bucketLeafFlag
    · rw [if_pos hfi]
      unfold wbktQ
      by_cases hr : inBucketRoot (leafValue pg i) = 0
      · rw [if_pos hr]
        iintro ⟨%hlen, %hig⟩
        iexists (∅ : GMap Nat (List w8))
        isplitr
        · ipureintro; exact ⟨fun _ => ⟨hlen, fun _ => hig⟩, fun h => absurd hr h.2, fun _ => rfl⟩
        · iapply pgToks_emptyT
      · rw [if_neg hr]
        iintro ⟨%hlen, %Q, HQ⟩
        unfold wtreeQ
        icases HQ with ⟨HQ, %hw⟩
        iexists Q
        iframe
        ipureintro
        exact ⟨fun _ => ⟨hlen, fun h => absurd h hr⟩, fun _ => hw, fun h => absurd ⟨hfi, hr⟩ h⟩
    · rw [if_neg hfi]
      iintro _
      iexists (∅ : GMap Nat (List w8))
      isplitr
      · ipureintro; exact ⟨fun h => absurd h hfi, fun h => absurd h.1 hfi, fun _ => rfl⟩
      · iapply pgToks_emptyT
  ihave Hl := bigSepL_range_choose (∅ : GMap Nat (List w8))
    (fun i Q => iprop(⌜lfFact pg i Q⌝ ∗ pgToks (GF := GF) γ Q)) (pageCount pg) $$ Hl
  icases Hl with ⟨%f, Hl⟩
  icases bigSepL_range_pure (fun i => lfFact pg i (f i)) (fun i => pgToks (GF := GF) γ (f i))
    (pageCount pg) $$ Hl with ⟨%hfs, Hl⟩
  icases toks_page γ x pg f (pageCount pg) $$ [Hx Hl] with ⟨%hd, Ht⟩
  · iframe
  have hch : ∀ i, ∃ p : Nat → Nat, i < pageCount pg → pageHts (f i) p ∧
      ∀ id v, f i !! id = some v → pageFlags v = branchPageFlag →
        ∀ j < pageCount v, (f i !! branchPgid v j).isSome := by
    intro i
    by_cases hi' : i < pageCount pg
    · by_cases hn : leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0
      · have hw := (hfs i hi').2.1 hn
        obtain ⟨-, p, hp, -⟩ := hw.2
        exact ⟨p, fun _ => ⟨hp, wtreeF0_closed _ _ _ _ hw.1⟩⟩
      · have he := (hfs i hi').2.2 hn
        refine ⟨fun _ => 0, fun _ => ⟨fun id v hv => ?_, fun id v hv => ?_⟩⟩ <;>
          rw [he] at hv <;> simp at hv
    · exact ⟨fun _ => 0, fun h' => absurd h' hi'⟩
  have hq : qHt (pageU x pg f (pageCount pg)) x 0 :=
    hts_pageU x pg f (pageCount pg) 0 (fun i => Classical.choose (hch i))
      hd.1 hd.2 (fun i hi' => (Classical.choose_spec (hch i) hi').1)
      (fun i hi' => (Classical.choose_spec (hch i) hi').2)
      (fun _ => rfl)
      (fun hb => by rw [hf] at hb; exact absurd hb (by unfold branchPageFlag leafPageFlag; decide))
  iexists (pageU x pg f (pageCount pg))
  isplitr
  · ipureintro; exact ⟨pageU_x _ _ _ _, hq⟩
  unfold wtreeQ
  iframe
  ipureintro
  exact ⟨wtreeF0_leaf x pg lo hi f hf hid hx hwf hks hin (fun i hi' => (hfs i hi').1)
    (fun i hi' => ⟨fun hn => ((hfs i hi').2.1 hn).1, (hfs i hi').2.2⟩) hd.1 hd.2, _, hq⟩

end own

end bbolt
end EtcdGrove
end Perennial
