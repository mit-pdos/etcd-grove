/-
A read transaction begins: the database's state with a new reader (`DBState.addReader`), and
its facts kept (`dbOK_addReader`).

The new reader sees the current tree (`newReader`), and takes `beginQ σ` of each slot it sees
and of the shared fields: half the least the database holds of any slot or of the fields.
-/
module

public import Proof.go_etcd_io.bbolt.DBLemmas
public import Proof.go_etcd_io.bbolt.SlotsCarve
public import Proof.go_etcd_io.raft.v3.ProjSimps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-- The lesser fraction. -/
def qmin (a b : Qp) : Qp := if a.val ≤ b.val then a else b

theorem qmin_le_left (a b : Qp) : qmin a b ≤ a := by
  unfold qmin; split <;> simp only [Qp.le_iff] <;> grind

theorem qmin_le_right (a b : Qp) : qmin a b ≤ b := by
  unfold qmin; split <;> simp only [Qp.le_iff] <;> grind

/-- The least of `rem s` for `s < n` (1 if none). -/
def minRem (rem : Nat → Qp) : Nat → Qp
  | 0 => 1
  | n + 1 => qmin (rem n) (minRem rem n)

theorem minRem_le (rem : Nat → Qp) (n s : Nat) (h : s < n) : minRem rem n ≤ rem s := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold minRem
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · have := ih h; have := qmin_le_right (rem n) (minRem rem n)
      simp only [Qp.le_iff] at *; grind
    · exact qmin_le_left _ _

theorem half_lt (q : Qp) : q.half < q := by
  simp only [Qp.lt_iff, Qp.val_half]; have := q.2; grind

/-- `a` less `b` (`b < a`). -/
def qsub (a b : Qp) : Qp :=
  if h : b.val < a.val then Classical.choose (Qp.lt_iff_exists_add.1 (Qp.lt_iff.2 h)) else a

theorem qsub_add (a b : Qp) (h : b < a) : a = qsub a b + b := by
  unfold qsub
  split
  · rename_i h'
    have := Classical.choose_spec (Qp.lt_iff_exists_add.1 (Qp.lt_iff.2 h'))
    simp only [Qp.ext_iff, Qp.val_add] at this ⊢; grind
  · rename_i h'; exact absurd (Qp.lt_iff.1 h) h'

/-- What a beginning reader takes: half the least the database holds. -/
def beginQ (σ : DBState) : Qp := (qmin σ.frem (minRem σ.rem σ.nslots)).half

theorem beginQ_lt_rem (σ : DBState) (s : Nat) (h : s < σ.nslots) : beginQ σ < σ.rem s := by
  have h1 := minRem_le σ.rem σ.nslots s h
  have h2 := qmin_le_right σ.frem (minRem σ.rem σ.nslots)
  have h3 := half_lt (qmin σ.frem (minRem σ.rem σ.nslots))
  unfold beginQ; simp only [Qp.le_iff, Qp.lt_iff] at *; grind

theorem beginQ_lt_frem (σ : DBState) : beginQ σ < σ.frem := by
  have h2 := qmin_le_left σ.frem (minRem σ.rem σ.nslots)
  have h3 := half_lt (qmin σ.frem (minRem σ.rem σ.nslots))
  unfold beginQ; simp only [Qp.le_iff, Qp.lt_iff] at *; grind

theorem le_sum_of_mem (l : List Nat) (x : Nat) (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- A key not in `m`. -/
def freshKey {V : Type} (m : GMap Nat V) : Nat := m.domList.sum + 1

theorem freshKey_none {V : Type} (m : GMap Nat V) : m !! freshKey m = none := by
  cases h : m !! freshKey m with
  | none => rfl
  | some v =>
    exfalso
    have hm : freshKey m ∈ m.domList := (GMap.mem_dom_list m _).2 (by rw [h]; rfl)
    have := le_sum_of_mem _ _ hm
    unfold freshKey at this; omega

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The reader that begins from the current meta (of `v0`, `v1`), with the fraction `q`. -/
def newReader (σ : DBState) (v0 v1 : internal.common.Meta) (q : Qp) : Reader :=
  let m := if metaPick v0 v1 then v1 else v0
  { txid := m.txid', root := uint.nat m.root'.root', hwm := uint.nat m.pgid',
    pages := treePages (filePages σ.bs σ.ps (uint.nat m.pgid')) (uint.nat m.root'.root'), q := q }

/-- The database with the reader `r` (key `k`) begun: `r` takes its fraction of the slots it
sees and of the fields, and is a read-only transaction of the freelist. -/
def DBState.addReader (σ : DBState) (k : Nat) (r : Reader) : DBState :=
  { σ with
    readers := <[k := r]> σ.readers
    rem := fun s => if r.sees s then qsub (σ.rem s) r.q else σ.rem s
    frem := qsub σ.frem r.q
    fl := { σ.fl with readonly := σ.fl.readonly ++ [r.txid] } }

proj_simps DBState.addReader

theorem nslots_addReader (σ : DBState) (k : Nat) (r : Reader) :
    (σ.addReader k r).nslots = σ.nslots := rfl

theorem treePages_lookup (P : GMap Nat (List w8)) (root id : Nat) (pg : List w8)
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

theorem filePages_some (bs : List w8) (ps n id : Nat) (pg : List w8)
    (h : filePages bs ps n !! id = some pg) : pg = pageAt bs ps id := by
  rw [filePages_lookup] at h
  by_cases hl : id < n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; exact (Option.some.inj h).symm
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; cases h

/-- The new reader's pages are the file's current tree's. -/
theorem newReader_pages (σ : DBState) (v0 v1 : internal.common.Meta) (q : Qp) (id : Nat)
    (pg : List w8) (h : (newReader σ v0 v1 q).pages !! id = some pg) :
    pg = pageAt σ.bs σ.ps id :=
  filePages_some _ _ _ _ _ (treePages_lookup _ _ id pg h)

/-- A page's slots: its id and its overflow (a page of the file). -/
theorem span_of_pageAt (bs : List w8) (ps id : Nat) (pg : List w8) (hps : 16 ≤ ps)
    (h : pg = pageAt bs ps id) : 1 + pageOverflow pg = pageSpan bs ps id := by
  rw [h, pageOverflow_pageAt bs ps id hps]; rfl

theorem dbOK_addReader (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hsize : σ.readers.size + 1 < Int.toNat sync.rwmutex.actualMaxReaders) :
    dbOK (σ.addReader (freshKey σ.readers) (newReader σ v0 v1 (beginQ σ))) v0 v1 := by
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs⟩ := h
  have hk := freshKey_none σ.readers
  have hcur' := hcur
  obtain ⟨cwf, cdisj, cin, cfree⟩ := hcur'
  have hps16 : 16 ≤ σ.ps := by omega
  -- what the new reader sees: the current tree's slots
  have hsees : ∀ s, (newReader σ v0 v1 (beginQ σ)).sees s = true →
      s < σ.nslots ∧ 2 ≤ s ∧ W64 s ∉ σ.fl.free ∧
      ∀ t pd, σ.fl.pending !! t = some pd → W64 s ∉ pd.ids := by
    intro s hs
    simp only [Reader.sees, decide_eq_true_eq] at hs
    have hc := cfree s hs
    obtain ⟨id, pg, hid, h1, h2⟩ := hs
    have hspan := span_of_pageAt σ.bs σ.ps id pg hps16 (newReader_pages σ v0 v1 _ id pg hid)
    have hin := cin id pg hid
    exact ⟨by omega, hc⟩
  refine ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the readers' facts
    intro k' r' hk'
    rw [DBState.addReader, GMap.lookup_insert_Some] at hk'
    rcases hk' with ⟨_, rfl⟩ | ⟨_, hk'⟩
    · exact ⟨cwf, cdisj, fun id pg hid =>
        ⟨(newReader_pages σ v0 v1 _ id pg hid).symm, cin id pg hid⟩⟩
    · exact hrd k' r' hk'
  · -- MVCC
    intro k' r' s hk' hs
    rw [DBState.addReader, GMap.lookup_insert_Some] at hk'
    rcases hk' with ⟨_, rfl⟩ | ⟨_, hk'⟩
    · obtain ⟨_, h2, h3, h4⟩ := hsees s hs
      exact ⟨h2, h3, fun t pd ht hin => absurd hin (h4 t pd ht)⟩
    · exact hmv k' r' s hk' hs
  · -- the slots
    intro s hs
    show fracSum (if (newReader σ v0 v1 (beginQ σ)).sees s then
        qsub (σ.rem s) (newReader σ v0 v1 (beginQ σ)).q else σ.rem s)
      (readersQ (<[freshKey σ.readers := newReader σ v0 v1 (beginQ σ)]> σ.readers)
        (fun r => r.sees s)) halfQ
    rw [readersQ_insert _ _ _ _ hk]
    unfold readersStep
    cases hrs' : (newReader σ v0 v1 (beginQ σ)).sees s
    · simp only [hrs', Bool.false_eq_true, ↓reduceIte]
      exact hsl s hs
    · simp only [hrs', ↓reduceIte]
      exact fracSum_take _ _ _ _ _ (hsl s hs) (qsub_add _ _ (beginQ_lt_rem σ s hs))
  · -- the fields
    show fracSum (qsub σ.frem (newReader σ v0 v1 (beginQ σ)).q)
      (readersQ (<[freshKey σ.readers := newReader σ v0 v1 (beginQ σ)]> σ.readers)
        (fun _ => true)) 1
    rw [readersQ_insert _ _ _ _ hk]
    unfold readersStep
    simp only [↓reduceIte]
    exact fracSum_take _ _ _ _ _ hfl (qsub_add _ _ (beginQ_lt_frem σ))
  · -- the freelist's read-only transactions
    show (σ.fl.readonly ++ [(newReader σ v0 v1 (beginQ σ)).txid]).Perm
      ((GMap.toList (<[freshKey σ.readers := newReader σ v0 v1 (beginQ σ)]> σ.readers)).map
        (·.2.txid))
    have hp := (GMap.mapToList_insert σ.readers _ (newReader σ v0 v1 (beginQ σ)) hk).map
      (fun kr => kr.2.txid)
    refine List.Perm.trans ?_ hp.symm
    refine (List.perm_append_singleton _ _).trans ?_
    exact List.Perm.cons _ hro
  · -- the number of readers
    show (<[freshKey σ.readers := newReader σ v0 v1 (beginQ σ)]> σ.readers).size <
      Int.toNat sync.rwmutex.actualMaxReaders
    rw [GMap.map_size_insert_None _ _ _ hk]; exact hsize

theorem fmap_insert {V V' : Type} (f : V → V') (m : GMap Nat V) (k : Nat) (v : V) :
    GMap.fmap f (<[k := v]> m) = <[k := f v]> (GMap.fmap f m) := by
  apply GMap.map_eq; intro k'
  simp only [GMap.lookup_fmap, GMap.lookup_insert_eq_iff]
  split <;> rfl

theorem nslots_mul_le (σ : DBState) : σ.nslots * σ.ps ≤ σ.bs.length := by
  unfold DBState.nslots
  have := Nat.div_mul_le_self (min σ.sz σ.bs.length) σ.ps
  omega

/-- No reader sees a meta page: the database holds its whole half. -/
theorem rem_meta (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1) (s : Nat)
    (hs : s < 2) : σ.rem s = halfQ := by
  obtain ⟨_, _, hn, _, _, _, _, _, _, _, hmv, hsl, _⟩ := h
  have := hsl s (by omega)
  rwa [readersQ_none _ _ (fun k r hk => by
    cases hr : r.sees s
    · rfl
    · exact absurd (hmv k r s hk hr).1 (by omega))] at this

open Iris.ProofMode in
/-- The two metas, taken out of the database's slots (and given back). -/
theorem slots_metas (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1) :
    slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ⊢
      (σ.data +ₗ 16) ↦{DFrac.own halfQ} v0 ∗
      (σ.data +ₗ ((σ.ps + 16 : Nat) : Int)) ↦{DFrac.own halfQ} v1 ∗
      ((σ.data +ₗ 16) ↦{DFrac.own halfQ} v0 -∗
        (σ.data +ₗ ((σ.ps + 16 : Nat) : Int)) ↦{DFrac.own halfQ} v1 -∗
        slotsView σ.data σ.bs σ.ps σ.rem (List.range σ.nslots)) := by
  have h' := h
  obtain ⟨hps, _, hn, _, hdc, hm0, hm1, _⟩ := h'
  have Hr : List.range σ.nslots = 0 :: 1 :: List.range' 2 (σ.nslots - 2) := by
    have Hm : ∀ m, List.range (m + 2) = 0 :: 1 :: List.range' 2 m := fun m => by
      rw [List.range_eq_range']; rfl
    rw [← Hm, show σ.nslots - 2 + 2 = σ.nslots by omega]
  have hfit := nslots_mul_le σ
  have hl0 : 80 ≤ (slotAt σ.bs σ.ps 0).length := by
    rw [slot_length _ _ _ (by have := Nat.mul_le_mul_right σ.ps (show 1 ≤ σ.nslots by omega); omega)]
    exact hps
  have hl1 : 80 ≤ (slotAt σ.bs σ.ps 1).length := by
    rw [slot_length _ _ _ (by have := Nat.mul_le_mul_right σ.ps (show 2 ≤ σ.nslots by omega); omega)]
    exact hps
  have hc1 : (σ.data +ₗ ((1 * σ.ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hdc
  have hc0 : (σ.data +ₗ ((0 * σ.ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hdc
  have ha0 : σ.data +ₗ ((0 * σ.ps : Nat) : Int) +ₗ 16 = σ.data +ₗ 16 := by simp
  have ha1 : σ.data +ₗ ((1 * σ.ps : Nat) : Int) +ₗ 16 = σ.data +ₗ ((σ.ps + 16 : Nat) : Int) := by
    rw [loc_add_assoc]; congr 1; push_cast; omega
  unfold slotsView
  rw [Hr]
  iintro ⟨H0, H1, Hrest⟩
  rw [rem_meta σ v0 v1 h 0 (by omega), rem_meta σ v0 v1 h 1 (by omega)]
  icases slot_meta_acc (hG := hG) _ _ _ v0 hc0 hl0 hm0 $$ H0 with ⟨Hm0, Hb0⟩
  icases slot_meta_acc (hG := hG) _ _ _ v1 hc1 hl1 hm1 $$ H1 with ⟨Hm1, Hb1⟩
  rw [ha0, ha1]
  iframe Hm0 Hm1
  iintro Hm0 Hm1
  ihave H0 := Hb0 $$ Hm0
  ihave H1 := Hb1 $$ Hm1
  iframe
  rw [rem_meta σ v0 v1 h 0 (by omega), rem_meta σ v0 v1 h 1 (by omega)]
  iframe

/-- A points-to at `a + b` is one at `a` and one at `b`. -/
theorem pointsto_split {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (a b : Qp) :
    (l ↦{DFrac.own (a + b)} v : IProp GF) ⊣⊢ l ↦{DFrac.own a} v ∗ l ↦{DFrac.own b} v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own a) (DFrac.own b)

theorem pointsto_split' {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (a b c : Qp)
    (h : c = a + b) :
    (l ↦{DFrac.own c} v : IProp GF) ⊣⊢ l ↦{DFrac.own a} v ∗ l ↦{DFrac.own b} v := by
  rw [h]; exact pointsto_split l v a b

open Iris.ProofMode in
/-- What a beginning reader takes of the database: its pages and its part of the fields. -/
theorem begin_carve (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (k : Nat) (dbl : Loc) :
    slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own σ.frem} σ.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{DFrac.own σ.frem} W64 σ.ps ⊢
    slotsView σ.data σ.bs σ.ps (σ.addReader k (newReader σ v0 v1 (beginQ σ))).rem
        (List.range σ.nslots) ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own (σ.addReader k (newReader σ v0 v1 (beginQ σ))).frem}
        σ.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{DFrac.own (σ.addReader k (newReader σ v0 v1 (beginQ σ))).frem}
        W64 σ.ps ∗
      pagesView σ.data σ.ps (beginQ σ) (newReader σ v0 v1 (beginQ σ)).pages ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own (beginQ σ)} σ.data ∗
      structFieldRef DB go!"pageSize" dbl ↦{DFrac.own (beginQ σ)} W64 σ.ps := by
  have h' := h
  obtain ⟨hps, _, _, _, _, _, _, _, ⟨_, cdisj, cin, _⟩, _⟩ := h'
  have Hcarve := slots_carve (GF := GF) σ.data σ.bs σ.ps σ.rem
    (σ.addReader k (newReader σ v0 v1 (beginQ σ))).rem (beginQ σ) σ.nslots
    (newReader σ v0 v1 (beginQ σ)).pages (by omega) (nslots_mul_le σ)
    (fun id pg hid => ⟨newReader_pages σ v0 v1 _ id pg hid, cin id pg hid⟩) cdisj
    (fun s hs hc => by
      show σ.rem s = (if (newReader σ v0 v1 (beginQ σ)).sees s then
        qsub (σ.rem s) (newReader σ v0 v1 (beginQ σ)).q else σ.rem s) + beginQ σ
      rw [show (newReader σ v0 v1 (beginQ σ)).sees s = true by
        unfold Reader.sees; simp only [decide_eq_true_eq]; exact hc]
      exact qsub_add _ _ (beginQ_lt_rem σ s hs))
    (fun s _ hc => by
      show σ.rem s = (if (newReader σ v0 v1 (beginQ σ)).sees s then
        qsub (σ.rem s) (newReader σ v0 v1 (beginQ σ)).q else σ.rem s)
      rw [show (newReader σ v0 v1 (beginQ σ)).sees s = false by
        unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hc]
      rfl)
  have Hf := qsub_add σ.frem (beginQ σ) (beginQ_lt_frem σ)
  have Hfr : (σ.addReader k (newReader σ v0 v1 (beginQ σ))).frem = qsub σ.frem (beginQ σ) := rfl
  rw [Hfr]
  iintro ⟨Hs, Hd, Hp⟩
  icases Hcarve.1 $$ Hs with ⟨Hs, Hpg⟩
  icases (pointsto_split' _ _ _ _ _ Hf).1 $$ Hd with ⟨Hd, Hd'⟩
  icases (pointsto_split' _ _ _ _ _ Hf).1 $$ Hp with ⟨Hp, Hp'⟩
  iframe

end defs

end bbolt
end EtcdGrove
end Perennial
