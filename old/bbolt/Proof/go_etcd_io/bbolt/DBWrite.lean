/-
The writer writes pages to the file (`Tx.write`, `Tx.writeMeta`): the database's facts are kept
when only slots no view covers change (`dbOK_bytes`: not the metas, nor the current tree's, a
reader's or the writer's), and the mapped cells of such slots, which the database holds whole
(its half: `rem s = halfQ`, no view taking a part), are lent out page by page (`cellsIf_runs`)
for `WriteAt` and given back with the new bytes.
-/
module

public import Proof.go_etcd_io.bbolt.DBAlloc
public import Proof.go_etcd_io.bbolt.DBBegin
public import Proof.go_etcd_io.bbolt.WriteTxModel
public import Spec.go_etcd_io.bbolt.DB__allocate
public import Proof.go_etcd_io.bbolt.MetaInj

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ### The trees a file's pages reach -/

/-- A tree's pages in `P` are in `P'` if `P'` agrees with `P` on them. -/
theorem treeHas_transfer (P P' : GMap Nat (List w8)) :
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

/-- A tree's pages in `P'` are in `P` if both have the same ids and `P'` agrees with `P` on
`P`'s tree. -/
theorem treeHas_back (P P' : GMap Nat (List w8))
    (hdom : ∀ x, (P !! x).isSome = (P' !! x).isSome) :
    ∀ a d, treeHas P' a d → (∀ x, treeHas P a x → P' !! x = P !! x) → treeHas P a d := by
  intro a d h
  induction h using treeHas.rec
    (motive_2 := fun pg d _ => (∀ x, pageHas P pg x → P' !! x = P !! x) → pageHas P pg d)
    (motive_3 := fun v d _ => (∀ x, bucketHas P v x → P' !! x = P !! x) → bucketHas P v d) with
  | root r pg hpg =>
    intro _
    obtain ⟨pg0, h0⟩ := Option.isSome_iff_exists.1 (show (P !! r).isSome by rw [hdom, hpg]; rfl)
    exact .root r pg0 h0
  | sub r pg id hpg hph ih =>
    intro hag
    obtain ⟨pg0, h0⟩ := Option.isSome_iff_exists.1 (show (P !! r).isSome by rw [hdom, hpg]; rfl)
    have e := hag r (.root r pg0 h0)
    rw [hpg, h0] at e
    obtain rfl := Option.some.inj e
    exact .sub r pg id h0 (ih (fun x hx => hag x (.sub r pg x h0 hx)))
  | child pg i id hf hi ht ih =>
    rename_i hag; exact .child pg i id hf hi (ih (fun x hx => hag x (.child pg i x hf hi hx)))
  | bucket pg i id hf hi hb hbh ih =>
    rename_i hag; exact .bucket pg i id hf hi hb (ih (fun x hx => hag x (.bucket pg i x hf hi hb hx)))
  | file v id hr ht ih =>
    rename_i hag; exact .file v id hr (ih (fun x hx => hag x (.file v x hr hx)))
  | inline v id hr hp ih =>
    rename_i hag; exact .inline v id hr (ih (fun x hx => hag x (.inline v x hr hx)))

theorem treeHas_isSome (P : GMap Nat (List w8)) (a d : Nat) (h : treeHas P a d) :
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

/-- Maps with the same ids, agreeing on a tree's pages, have the same tree. -/
theorem treePages_congr (P P' : GMap Nat (List w8)) (root : Nat)
    (hdom : ∀ x, (P !! x).isSome = (P' !! x).isSome)
    (hag : ∀ x, treeHas P root x → P' !! x = P !! x) :
    treePages P' root = treePages P root := by
  apply GMap.ext; intro k
  show (treePages P' root) !! k = (treePages P root) !! k
  unfold treePages
  rw [GMap.lookup_filter, GMap.lookup_filter]
  by_cases hk : treeHas P root k
  · rw [hag k hk]
    have hk' := treeHas_transfer P P' root k hk hag
    cases P !! k <;> simp [Option.filter, hk, hk']
  · have hk' : ¬ treeHas P' root k := fun h => hk (treeHas_back P P' hdom root k h hag)
    cases h1 : P !! k <;> cases h2 : P' !! k <;> simp [Option.filter, hk, hk']

/-! ### Pages are their slots -/

theorem take_drop_slots (bs : List w8) (ps : Nat) :
    ∀ (k id : Nat), (bs.drop (id * ps)).take (k * ps) =
      ((List.range' id k).map (slotAt bs ps)).flatten := by
  intro k
  induction k with
  | zero => intro id; simp
  | succ k ih =>
    intro id
    have Hsplit : (bs.drop (id * ps)).take ((k + 1) * ps) =
        slotAt bs ps id ++ (bs.drop ((id + 1) * ps)).take (k * ps) := by
      unfold slotAt
      rw [show (k + 1) * ps = ps + k * ps by rw [Nat.succ_mul, Nat.add_comm], List.take_add,
        List.drop_drop, Nat.succ_mul]
    rw [Hsplit, ih (id + 1), List.range'_succ]
    simp

/-- A page whose first slot and span agree in two files is the same in both. -/
theorem pageAt_congr (bs bs' : List w8) (ps id : Nat)
    (h : ∀ j < pageSpan bs ps id, slotAt bs' ps (id + j) = slotAt bs ps (id + j)) :
    pageSpan bs' ps id = pageSpan bs ps id ∧ pageAt bs' ps id = pageAt bs ps id := by
  have hsp : pageSpan bs' ps id = pageSpan bs ps id := by
    have h0 := h 0 (by unfold pageSpan; omega)
    rw [Nat.add_zero] at h0
    unfold pageSpan
    rw [h0]
  refine ⟨hsp, ?_⟩
  unfold pageAt
  rw [hsp, take_drop_slots, take_drop_slots]
  congr 1
  apply List.map_congr_left
  intro s hs
  rw [List.mem_range'_1] at hs
  have := h (s - id) (by omega)
  rwa [show id + (s - id) = s by omega] at this

/-! ### The database's facts when slots no view covers change -/

/-- The current tree's pages (of the meta `db.meta()` picks). -/
def curPages (σ : DBState) (v0 v1 : internal.common.Meta) : GMap Nat (List w8) :=
  treePages (filePages σ.bs σ.ps (uint.nat (if metaPick v0 v1 then v1 else v0).pgid'))
    (uint.nat (if metaPick v0 v1 then v1 else v0).root'.root')

/-- Slot `s` is one of the current meta's freelist page. -/
def inFlPage (σ : DBState) (v0 v1 : internal.common.Meta) (s : Nat) : Prop :=
  uint.nat (if metaPick v0 v1 then v1 else v0).freelist' ≤ s ∧
  s < uint.nat (if metaPick v0 v1 then v1 else v0).freelist' +
    pageSpan σ.bs σ.ps (uint.nat (if metaPick v0 v1 then v1 else v0).freelist')

/-- A slot some view covers: a meta, the current tree's, a reader's, the writer's, or the current
freelist page's. -/
def slotSeen (σ : DBState) (v0 v1 : internal.common.Meta) (s : Nat) : Prop :=
  s < 2 ∨ coversSlot (curPages σ v0 v1) s ∨
  (∃ k r, σ.readers !! k = some r ∧ coversSlot r.pages s) ∨
  (∃ w, σ.wr = some w ∧ coversSlot w.pages s) ∨ inFlPage σ v0 v1 s

/-- The pages of a view of the file, slot by slot the same in `bs'`, are the same there. -/
theorem view_congr (bs bs' : List w8) (ps : Nat) (hps : 16 ≤ ps) (P : GMap Nat (List w8))
    (hP : ∀ id pg, P !! id = some pg → pageAt bs ps id = pg)
    (hs : ∀ s, coversSlot P s → slotAt bs' ps s = slotAt bs ps s) :
    ∀ id pg, P !! id = some pg →
      pageSpan bs' ps id = pageSpan bs ps id ∧ pageAt bs' ps id = pageAt bs ps id := by
  intro id pg hid
  apply pageAt_congr
  intro j hj
  apply hs
  refine ⟨id, pg, hid, by omega, ?_⟩
  rw [span_of_pageAt bs ps id pg hps (hP id pg hid).symm]; omega

/-- The database's facts are kept when only slots no view covers change. -/
theorem dbOK_bytes (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (bs' : List w8) (hlen : bs'.length = σ.bs.length)
    (hsame : ∀ s, slotSeen σ v0 v1 s → slotAt bs' σ.ps s = slotAt σ.bs σ.ps s) :
    dbOK { σ with bs := bs' } v0 v1 := by
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h
  have hps16 : 16 ≤ σ.ps := by omega
  have hns : ({ σ with bs := bs' } : DBState).nslots = σ.nslots := by
    unfold DBState.nslots; simp only [hlen]
  -- a reader's view keeps its facts
  have hread : ∀ r, readerOK σ r → (∀ s, coversSlot r.pages s → slotAt bs' σ.ps s = slotAt σ.bs σ.ps s) →
      readerOK { σ with bs := bs' } r := by
    intro r hr hs
    obtain ⟨rwf, rdisj, rin⟩ := hr
    have hc := view_congr σ.bs bs' σ.ps hps16 r.pages (fun id pg hid => (rin id pg hid).1) hs
    refine ⟨rwf, rdisj, fun id pg hid => ?_⟩
    obtain ⟨h1, h2⟩ := hc id pg hid
    show pageAt bs' σ.ps id = pg ∧ id + pageSpan bs' σ.ps id ≤ min ({ σ with bs := bs' } : DBState).nslots r.hwm
    rw [h1, h2, hns]; exact rin id pg hid
  -- the current tree
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow, cagree⟩ := hcur
  have hcs : ∀ s, coversSlot (curPages σ v0 v1) s → slotAt bs' σ.ps s = slotAt σ.bs σ.ps s :=
    fun s hs => hsame s (Or.inr (Or.inl hs))
  have hcP : ∀ id pg, curPages σ v0 v1 !! id = some pg → pageAt σ.bs σ.ps id = pg := by
    intro id pg hid
    exact (filePages_some _ _ _ _ _ (treePages_lookup _ _ id pg hid)).symm
  have hcc := view_congr σ.bs bs' σ.ps hps16 _ hcP hcs
  have hfp : treePages (filePages bs' σ.ps (uint.nat (if metaPick v0 v1 then v1 else v0).pgid'))
      (uint.nat (if metaPick v0 v1 then v1 else v0).root'.root') = curPages σ v0 v1 := by
    unfold curPages
    apply treePages_congr
    · intro x; rw [filePages_lookup, filePages_lookup]
      by_cases hx : x < uint.nat (if metaPick v0 v1 then v1 else v0).pgid'
      · rw [if_pos hx, if_pos hx]; rfl
      · rw [if_neg hx, if_neg hx]
    · intro x hx
      have hx' : curPages σ v0 v1 !! x = some (pageAt σ.bs σ.ps x) := by
        unfold curPages treePages
        rw [GMap.lookup_filter]
        have hxl : x < uint.nat (if metaPick v0 v1 then v1 else v0).pgid' := by
          have := treeHas_isSome _ _ _ hx
          rw [filePages_lookup] at this; split at this <;> simp_all
        rw [filePages_lookup, if_pos hxl]
        simp [Option.filter, hx]
      have hxl : x < uint.nat (if metaPick v0 v1 then v1 else v0).pgid' := by
        have := treeHas_isSome _ _ _ hx
        rw [filePages_lookup] at this; split at this <;> simp_all
      rw [filePages_lookup, filePages_lookup, if_pos hxl, if_pos hxl, (hcc x _ hx').2]
  refine ⟨hps, hps2, by rw [hns]; exact hn, ⟨hsz.1, by show bs'.length < 2 ^ 62; omega⟩, hdc,
    ?_, ?_, hv, ?_, fun k r hk => hread r (hrd k r hk) (fun s hs => hsame s (Or.inr (Or.inr
      (Or.inl ⟨k, r, hk, hs⟩)))), hmv, fun s hs => hsl s (by rw [hns] at hs; exact hs), hfl,
    hro, hrs, ⟨hwr.1, fun w hw => ⟨hread w (hwr.2 w hw).1 (fun s hs => hsame s (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨w, hw, hs⟩))))), (hwr.2 w hw).2⟩⟩⟩
  · unfold metaIn; show ((slotAt bs' σ.ps 0).drop 16).take 64 = _
    rw [hsame 0 (Or.inl (by omega))]; exact hm0
  · unfold metaIn; show ((slotAt bs' σ.ps 1).drop 16).take 64 = _
    rw [hsame 1 (Or.inl (by omega))]; exact hm1
  · show currentOK { σ with bs := bs' } v0 v1
    unfold currentOK
    simp only
    rw [hfp]
    obtain ⟨cagree, crb, cfl⟩ := cagree
    refine ⟨cwf, cdisj, fun id pg hid => ?_, calloc, cfree, cbelow, cagree, crb, ?_⟩
    · rw [(hcc id pg hid).1, hns]
      exact cin id pg hid
    · -- the freelist page: its slots unchanged
      have hfl := pageAt_congr σ.bs bs' σ.ps (uint.nat (if metaPick v0 v1 then v1 else v0).freelist')
        (fun j hj => hsame _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))
      unfold flCurOK at cfl ⊢
      simp only
      rw [hfl.1, hfl.2, hns]
      exact cfl


/-! ### Bytes written inside a file -/

theorem writeBytes_get (F : List w8) (o : Nat) (d : List w8) (h : o + d.length ≤ F.length)
    (i : Nat) :
    (writeBytes F o d)[i]? = if o ≤ i ∧ i < o + d.length then d[i - o]? else F[i]? := by
  unfold writeBytes
  have hr : List.replicate (o - F.length) (0 : w8) = [] := by
    rw [show o - F.length = 0 by omega]; rfl
  rw [hr, List.append_nil]
  by_cases h1 : i < o
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h1, if_neg (by omega)]
  · by_cases h2 : i < o + d.length
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega),
        if_pos (by omega)]
      simp only [List.length_take]; congr 1; omega
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop, if_neg (by omega)]
      simp only [List.length_append, List.length_take]; congr 1; omega

theorem writeBytes_length_in (F : List w8) (o : Nat) (d : List w8) (h : o + d.length ≤ F.length) :
    (writeBytes F o d).length = F.length := by
  unfold writeBytes; simp; omega

/-- `n` bytes from `a`, given elementwise. -/
theorem seg_ext (F X : List w8) (a n : Nat) (hn : X.length = n) (hf : a + n ≤ F.length)
    (h : ∀ i < n, F[a + i]? = X[i]?) : (F.drop a).take n = X := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < n
  · rw [if_pos hi]; exact h i hi
  · rw [if_neg hi, List.getElem?_eq_none (by omega)]

theorem seg_get (F : List w8) (a n i : Nat) (hi : i < n) : ((F.drop a).take n)[i]? = F[a + i]? := by
  rw [List.getElem?_take, if_pos hi, List.getElem?_drop]

/-- The bytes `mapRange` holds of `[lo, hi)`, inside the mapping. -/
theorem mapRange_seg (F : List w8) (sz lo hi : Nat) (hs : hi ≤ sz) :
    ((F.take sz).take hi).drop lo = (F.drop lo).take (hi - lo) := by
  apply List.ext_getElem?; intro i
  simp only [List.getElem?_drop, List.getElem?_take]
  by_cases h1 : lo + i < hi
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

end pure

/-! ### The mapped cells of slots no view covers -/

section cells
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Classical in
/-- The cells of the slots below `n` not in `S`, at the database's fractions. -/
def cellsOut (data : Loc) (bs : List w8) (ps : Nat) (rem : Nat → Qp) (S : Nat → Prop) (n : Nat) :
    IProp GF :=
  [∗list] s ∈ List.range n, if S s then emp else cellAt data bs ps (rem s) s

open Classical in
/-- The database's slots: those not in `S`, and those in `S`, which it holds at half (no view
takes a part of them). -/
theorem slots_out (data : Loc) (bs : List w8) (ps : Nat) (rem : Nat → Qp) (S : Nat → Prop)
    (n : Nat) (hS : ∀ s < n, S s → rem s = halfQ) :
    slotsView (GF := GF) data bs ps rem (List.range n) ⊣⊢
      cellsOut data bs ps rem S n ∗ cellsIf data bs ps halfQ S n := by
  unfold slotsView cellsOut cellsIf
  refine Iris.BI.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  refine bigSepL_congr_mem fun _ x hx => ?_
  have hxn : x < n := List.mem_range.1 hx
  by_cases h : S x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h), hS x hxn h]
    unfold cellAt; exact emp_sep.symm
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    unfold cellAt; exact emp_sep_eqv' _

open Classical in
/-- The cells outside `S` of two files that agree there. -/
theorem cellsOut_congr (data : Loc) (bs bs' : List w8) (ps : Nat) (rem : Nat → Qp)
    (S : Nat → Prop) (n : Nat) (h : ∀ s < n, ¬ S s → slotAt bs' ps s = slotAt bs ps s) :
    cellsOut (GF := GF) data bs ps rem S n ⊣⊢ cellsOut data bs' ps rem S n := by
  unfold cellsOut
  refine bigSepL_congr_mem fun _ x hx => ?_
  have hxn : x < n := List.mem_range.1 hx
  by_cases hS : S x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hS), ite_eq_left_of_eq_true _ _ (eq_true hS)]
    exact .rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hS), ite_eq_right_of_eq_false _ _ (eq_false hS)]
    unfold cellAt; rw [h x hxn hS]; exact .rfl

/-- The slots of the runs `R` (a first slot and a number of slots each). -/
def inRuns (R : List (Nat × Nat)) (s : Nat) : Prop := ∃ r ∈ R, r.1 ≤ s ∧ s < r.1 + r.2

/-- The bytes of a run. -/
def runBytes (bs : List w8) (ps : Nat) (r : Nat × Nat) : List w8 :=
  (bs.drop (r.1 * ps)).take (r.2 * ps)

open Classical in
/-- The cells of disjoint runs of slots (inside the file) are the runs' bytes. -/
theorem cellsIf_runs (data : Loc) (bs : List w8) (ps : Nat) (q : Qp) (n : Nat)
    (hfit : n * ps ≤ bs.length) :
    ∀ (R : List (Nat × Nat)), (∀ r ∈ R, r.1 + r.2 ≤ n) →
    R.Pairwise (fun r1 r2 => r1.1 + r1.2 ≤ r2.1 ∨ r2.1 + r2.2 ≤ r1.1) →
    cellsIf (GF := GF) data bs ps q (inRuns R) n ⊣⊢
      [∗list] r ∈ R, bytesPointsto (data +ₗ ((r.1 * ps : Nat) : Int)) (DFrac.own q)
        (runBytes bs ps r) := by
  intro R
  induction R with
  | nil =>
    intro _ _
    refine (cellsIf_ext data bs ps q _ (fun _ => False) n (fun s _ => by simp [inRuns])).trans ?_
    exact (cellsIf_false data bs ps q n).trans BigSepL.bigSepL_nil.symm
  | cons r R ih =>
    intro hin hpw
    obtain ⟨hr, hpw'⟩ := List.pairwise_cons.1 hpw
    have hcov : ∀ s < n, (inRuns (r :: R) s ↔ ((r.1 ≤ s ∧ s < r.1 + r.2) ∨ inRuns R s)) := by
      intro s _
      unfold inRuns
      constructor
      · rintro ⟨r', hr', h1, h2⟩
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨r', hr', h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨r', hr', h1, h2⟩)
        · exact ⟨r, List.mem_cons_self, h1, h2⟩
        · exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩
    have hd : ∀ s < n, (r.1 ≤ s ∧ s < r.1 + r.2) → inRuns R s → False := by
      rintro s _ ⟨h1, h2⟩ ⟨r', hr', h3, h4⟩
      rcases hr r' hr' with h5 | h5 <;> omega
    have hr0 := hin r List.mem_cons_self
    refine (cellsIf_ext data bs ps q _ _ n hcov).trans ?_
    refine (cellsIf_or data bs ps q _ _ n hd).trans ?_
    refine (sep_congr (cellsIf_range data bs ps q r.1 r.2 n hr0)
      (ih (fun r' h => hin r' (List.mem_cons_of_mem _ h)) hpw')).trans ?_
    refine Iris.BI.BiEntails.trans ?_ BigSepL.bigSepL_cons.symm
    refine sep_congr ?_ .rfl
    refine (slots_bytes data bs ps q r.2 r.1 ?_).symm
    have := Nat.mul_le_mul_right ps hr0; omega

end cells


/-! ### The writer's dirty pages -/

section dirty
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Slot `s` is no meta and no view sees it: no reader, not the writer, not the current tree
(of the metas the database's facts hold of). -/
def slotUnseen (σ : DBState) (s : Nat) : Prop :=
  2 ≤ s ∧ (∀ k r, σ.readers !! k = some r → ¬ coversSlot r.pages s) ∧
  (∀ w, σ.wr = some w → ¬ coversSlot w.pages s) ∧
  ∀ v0 v1, dbOK σ v0 v1 → ¬ coversSlot (curPages σ v0 v1) s

/-- The number of slots of a page buffer: one and its overflow (read from its header). -/
def dspan (b : List w8) : Nat := 1 + pageOverflow b

/-- The transaction's dirty pages can be written: each page buffer is its `1 + overflow` slots
long, its header's id is its id in the page cache, its slots are inside the mapping and the
file and seen by no view; distinct pages have disjoint slots. -/
def dirtyOK (σ : DBState) (T : WTx) : Prop :=
  (∀ id b, (T.pm !! id).isSome → T.bufs !! id = some b →
    b.length = dspan b * σ.ps ∧ pageId b = uint.nat id ∧
    ∀ k < dspan b, uint.nat id + k < σ.nslots ∧ slotUnseen σ (uint.nat id + k) ∧
      ∀ v0 v1, dbOK σ v0 v1 → ¬ inFlPage σ v0 v1 (uint.nat id + k)) ∧
  ∀ i1 b1 i2 b2, (T.pm !! i1).isSome → T.bufs !! i1 = some b1 → (T.pm !! i2).isSome →
    T.bufs !! i2 = some b2 → i1 ≠ i2 →
    uint.nat i1 + dspan b1 ≤ uint.nat i2 ∨ uint.nat i2 + dspan b2 ≤ uint.nat i1

/-- Slot `s` is one of a dirty page's. -/
def dirtySlot (T : WTx) (s : Nat) : Prop :=
  ∃ id b, (T.pm !! id).isSome ∧ T.bufs !! id = some b ∧ uint.nat id ≤ s ∧ s < uint.nat id + dspan b

/-- `bs'` is the file `bs` with (some of) the dirty pages' bytes written: its other slots are
the same. -/
def dirtyOnly (T : WTx) (ps : Nat) (bs bs' : List w8) : Prop :=
  bs'.length = bs.length ∧ ∀ s, ¬ dirtySlot T s → slotAt bs' ps s = slotAt bs ps s

/-- Every dirty page is written in `bs'`, at its id. -/
def dirtyAll (T : WTx) (ps : Nat) (bs' : List w8) : Prop :=
  ∀ id b, (T.pm !! id).isSome → T.bufs !! id = some b →
    (bs'.drop (uint.nat id * ps)).take b.length = b

/-- The dirty slots no view sees. -/
theorem dirty_unseen (σ : DBState) (T : WTx) (h : dirtyOK σ T) (s : Nat) (hs : dirtySlot T s) :
    s < σ.nslots ∧ slotUnseen σ s ∧ ∀ v0 v1, dbOK σ v0 v1 → ¬ inFlPage σ v0 v1 s := by
  obtain ⟨id, b, hp, hb, h1, h2⟩ := hs
  have := (h.1 id b hp hb).2.2 (s - uint.nat id) (by omega)
  rwa [show uint.nat id + (s - uint.nat id) = s by omega] at this

/-- The database's facts with the dirty slots changed. -/
theorem dbOK_dirty (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1) (T : WTx)
    (hd : dirtyOK σ T) (bs' : List w8) (hw : dirtyOnly T σ.ps σ.bs bs') :
    dbOK { σ with bs := bs' } v0 v1 := by
  refine dbOK_bytes σ v0 v1 h bs' hw.1 (fun s hs => hw.2 s (fun hds => ?_))
  obtain ⟨-, ⟨h2, hr, hwr, hc⟩, hnf⟩ := dirty_unseen σ T hd s hds
  rcases hs with hs | hs | ⟨k, r, hk, hs⟩ | ⟨w, hw', hs⟩ | hs
  · omega
  · exact hc v0 v1 h hs
  · exact hr k r hk hs
  · exact hwr w hw' hs
  · exact hnf v0 v1 h hs

/-! ### The slots an allocation takes -/

/-- No reader is newer than the current tree: their high-water marks are at most its. -/
theorem dbOK_readers_below (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1) :
    ∀ k r, σ.readers !! k = some r → r.hwm ≤ uint.nat (if metaPick v0 v1 then v1 else v0).pgid' := by
  obtain ⟨-, -, -, -, -, -, -, -, hcur, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, crb, -⟩ := hcur
  exact crb

/-- A view whose pages are the file's, ending below `H`, covers only slots below `H`. -/
theorem view_covers_lt (σ : DBState) (P : GMap Nat (List w8)) (H : Nat) (hps : 16 ≤ σ.ps)
    (hin : ∀ id pg, P !! id = some pg → pageAt σ.bs σ.ps id = pg ∧ id + pageSpan σ.bs σ.ps id ≤ H)
    (s : Nat) (hc : coversSlot P s) : s < H := by
  obtain ⟨id, pg, hid, h1, h2⟩ := hc
  have := span_of_pageAt σ.bs σ.ps id pg hps (hin id pg hid).1.symm
  have := (hin id pg hid).2
  omega

/-- The slots `db.allocate` takes (`allocOK`, for the writer `w` whose meta's high-water mark is
at least its view's) are seen by no view and are none of the current freelist page's: free ones
(which no view sees), or ones from the high-water mark on. -/
theorem allocOK_unseen (σ σ' : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (mv mv' : internal.common.Meta) (txid id : w64) (n : Nat)
    (hmv : w.hwm ≤ uint.nat mv.pgid') (hal : allocOK σ σ' w mv mv' txid id n) :
    ∀ k < n, unseenBy σ (curPages σ v0 v1) (uint.nat id + k) ∧ ¬ inFlPage σ v0 v1 (uint.nat id + k) := by
  intro k hk
  have hok := h
  obtain ⟨hps, -, -, hsz, -, -, -, -, hcur, hrd, hmvc, -, -, -, -, hwr⟩ := h
  obtain ⟨-, -, cin, -, cfree, cbelow, -, crb, cfl⟩ := hcur
  obtain ⟨-, -, -, b4, -, -, -⟩ := cbelow
  have hps16 : 16 ≤ σ.ps := by omega
  have hwo := (hwr.2 w hw)
  obtain ⟨hid2, -, -, -, -, hidn, hcases⟩ := hal
  have z1 : uint.Z id = ((uint.nat id : Nat) : Int) := rfl
  have z2 : uint.Z mv'.pgid' = ((uint.nat mv'.pgid' : Nat) : Int) := rfl
  have hidk : uint.nat id + k < 2 ^ 64 := by
    have := dbp_uint_nat_lt mv'.pgid'
    omega
  rcases hcases with ⟨hcan, -, -⟩ | ⟨hidm, -, -⟩
  · -- a free run
    have hf : W64 ((uint.nat id + k : Nat) : Int) ∈ σ.fl.free := by
      have e : uint.Z (W64 ((uint.nat id + k : Nat) : Int)) = ((uint.nat id + k : Nat) : Int) := by
        generalize uint.nat id + k = s at hidk ⊢
        word
      apply hcan.2
      unfold inRun
      rw [e, z1]; omega
    refine ⟨⟨fun kr r hk' hc => ((hmvc kr r hk').2 _ hc).2.1 hf,
      fun w' hw' hc => ((hwr.2 w' hw').2.2 _ hc).2.1 hf, fun hc => (cfree _ hc).2.1 hf⟩, fun hin => ?_⟩
    exact (cfl.2.2.2.1 _ hin.1 hin.2).2.1 hf
  · -- at the high-water mark: no view reaches it
    have hb4 := (b4 w hw).1
    have hge : uint.nat (if metaPick v0 v1 then v1 else v0).pgid' ≤ uint.nat id + k := by
      rw [← hb4]; have : uint.nat id = uint.nat mv.pgid' := by rw [hidm]
      omega
    refine ⟨⟨fun kr r hk' hc => ?_, fun w' hw' hc => ?_, fun hc => ?_⟩, fun hin => ?_⟩
    · have := view_covers_lt σ r.pages r.hwm hps16
        (fun i pg hi => ⟨((hrd kr r hk').2.2 i pg hi).1, by
          have := ((hrd kr r hk').2.2 i pg hi).2; exact Nat.le_trans this (Nat.min_le_right _ _)⟩) _ hc
      have := crb kr r hk'
      omega
    · obtain rfl := Option.some.inj (hw.symm.trans hw')
      have := view_covers_lt σ w.pages w.hwm hps16
        (fun i pg hi => ⟨((hwo.1).2.2 i pg hi).1, by
          have := ((hwo.1).2.2 i pg hi).2; exact Nat.le_trans this (Nat.min_le_right _ _)⟩) _ hc
      omega
    · unfold curPages at hc
      have := view_covers_lt σ _ (uint.nat (if metaPick v0 v1 then v1 else v0).pgid') hps16
        (fun i pg hi => ⟨(filePages_some _ _ _ _ _ (treePages_lookup _ _ i pg hi)).symm, by
          have := cin i pg hi; exact Nat.le_trans this (Nat.min_le_right _ _)⟩) _ hc
      omega
    · have := Nat.le_min.1 cfl.2.2.1
      unfold inFlPage at hin
      omega

/-- The database's facts determine its metas from the file. -/
theorem dbOK_metas_same (σ σ' : DBState) (v0 v1 v0' v1' : internal.common.Meta) (h : dbOK σ v0 v1)
    (h' : dbOK σ' v0' v1') (hbs : σ'.bs = σ.bs) (hps : σ'.ps = σ.ps) : v0' = v0 ∧ v1' = v1 := by
  obtain ⟨-, -, -, -, -, m0, m1, -⟩ := h
  obtain ⟨-, -, -, -, -, m0', m1', -⟩ := h'
  unfold metaIn at m0 m1 m0' m1'
  rw [hbs, hps] at m0' m1'
  exact ⟨metaBytes_inj _ _ (m0'.symm.trans m0), metaBytes_inj _ _ (m1'.symm.trans m1)⟩

/-- What `db.allocate` keeps of the database: the file, page size, readers and writer. -/
theorem allocOK_same (σ σ' : DBState) (w : Reader) (mv mv' : internal.common.Meta) (txid id : w64)
    (n : Nat) (h : allocOK σ σ' w mv mv' txid id n) :
    σ'.bs = σ.bs ∧ σ'.ps = σ.ps ∧ σ'.readers = σ.readers ∧ σ'.wr = σ.wr := by
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, rfl | ⟨d', sz', -, rfl⟩⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The allocated slots, seen by no view of the database after the allocation and none of its
current freelist page's (for any metas its facts hold of). -/
theorem allocOK_unseen' (σ σ' : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (mv mv' : internal.common.Meta) (txid id : w64) (n : Nat)
    (hmv : w.hwm ≤ uint.nat mv.pgid') (hal : allocOK σ σ' w mv mv' txid id n) :
    ∀ k < n, ∀ v0' v1', dbOK σ' v0' v1' →
      unseenBy σ' (curPages σ' v0' v1') (uint.nat id + k) ∧ ¬ inFlPage σ' v0' v1' (uint.nat id + k) := by
  intro k hk v0' v1' h'
  obtain ⟨hbs, hps, hrd, hwr⟩ := allocOK_same σ σ' w mv mv' txid id n hal
  obtain ⟨e0, e1⟩ := dbOK_metas_same σ σ' v0 v1 v0' v1' h h' hbs hps
  rw [e0, e1]
  obtain ⟨⟨u1, u2, u3⟩, hnf⟩ := allocOK_unseen σ σ' v0 v1 h w hw mv mv' txid id n hmv hal k hk
  have hc : curPages σ' v0 v1 = curPages σ v0 v1 := by unfold curPages; rw [hbs, hps]
  refine ⟨⟨fun kr r hk' => u1 kr r (by rw [← hrd]; exact hk'), fun w' hw' => u2 w' (by rw [← hwr]; exact hw'),
    by rw [hc]; exact u3⟩, ?_⟩
  unfold inFlPage at hnf ⊢
  rw [hbs, hps]; exact hnf

end dirty

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database's facts, out of its predicate. -/
theorem ownDB_dbOK (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) :
    ownDB I dbl γ σ ⊢ ⌜∃ v0 v1, dbOK σ v0 v1⌝ := by
  iintro Hdb
  isimp only [ownDB] at Hdb
  iNamed Hdb
  ipureintro
  exact ⟨v0, v1, Hok⟩

end own

end bbolt
end EtcdGrove
end Perennial

