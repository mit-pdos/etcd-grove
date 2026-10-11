/-
The key index (`index.go`): a `treeIndex` is a btree of `*keyIndex` (the verified k8s btree,
`cache/v3/InvBtree.lean`) under a `sync.RWMutex`. Lean-first (no Rocq counterpart).

**Representation.** The btree's items are the `*keyIndex` pointers, modelled with their keys
(`kiItemIs p (p, k)`: `kiKey`, persistent) and ordered by key (`kiItemLess`); the mutable part
of each key index (`ownKi`) is held beside the tree. `ownTree t L q` holds both at fraction `q`
for the entries `L` (pointer, key, model). It is `Fractional` (through the btree's
`ownBTree_combine`), so it can be the resource of the `RWMutex`.

**The lock invariant** (`idxLockInv`) ties the tree to the index's *history* (`Hist.lean`): the
tree holds `indexOf` of the events of `ilog ++ [pend]`, where `ilog` is the log the writer had
committed and `pend` the pending revision's changes it had put, at the last write; a lower bound
of the history ghost (`monoListLbOwn γ.hist (histShape ilog pend)`) and the number of events
(`monoNatAuthOwn γ.nev`, at the lock's fraction) record it. The **writer** (`idxWriter γ ilog
pend`, held by the store's write transaction: the batch lock serializes writers) owns the
history's authority and a lower bound of the count. Committing a revision is a ghost step
(`idxWriter_commit`, outside the index lock: `storeTxnWrite.End` does not take it), which yields
the **certificate** `idxCert γ log` of the committed log: its history is a prefix of the index's.
A **reader** (`idxReader`: one of the `RWMutex`'s reader tokens) with the certificate of `log₀`
reads at a revision below `log₀.length` what `log₀` determines (`reader_answer`): the index's
history is comparable with `histOf log₀`, and either `log₀`'s events are a prefix (later events
have higher mains: `kiGet_reader`) or the index has exactly `log₀`'s events (the count).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ### Countability (for the history ghost) -/

def Rev.enc (r : Rev) : w64 × w64 := (r.main, r.sub)

theorem Rev.enc_inj : Function.Injective Rev.enc := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Rev.enc, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

instance Rev.countable : Pos.Countable Rev :=
  .ofInjective (fun r => Pos.Countable.encode r.enc) (fun _ _ h => Rev.enc_inj (Pos.encode_inj h))

def Ev.enc (e : Ev) : Rev × GoString × Bool := (e.rev, e.key, e.tomb)

theorem Ev.enc_inj : Function.Injective Ev.enc := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Ev.enc, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

instance Ev.countable : Pos.Countable Ev :=
  .ofInjective (fun e => Pos.Countable.encode e.enc) (fun _ _ h => Ev.enc_inj (Pos.encode_inj h))

def HistItem.enc : HistItem → Option Ev
  | .ev e => some e
  | .commit => none

theorem HistItem.enc_inj : Function.Injective HistItem.enc := by
  intro x y h
  cases x <;> cases y <;> simp only [HistItem.enc] at h
  · rw [Option.some.inj h]
  · cases h
  · cases h
  · rfl

instance HistItem.countable : Pos.Countable HistItem :=
  .ofInjective (fun x => Pos.Countable.encode x.enc)
    (fun _ _ h => HistItem.enc_inj (Pos.encode_inj h))

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ### The btree's items: `*keyIndex` pointers, by key -/

/-- The btree's item type: `*keyIndex`. -/
abbrev kiPtrT : go.GoType := go.GoType.PointerType keyIndex.ty

/-- The model of an item: the pointer and its key. -/
abbrev KiItem := Loc × GoString

/-- `p` is the item `(p, k)`: a `*keyIndex` with key `k`. -/
def kiItemIs (p : Loc) (v : KiItem) : IProp GF := iprop(⌜p = v.1⌝ ∗ kiKey p v.2)

instance kiItemIs_persistent (p : Loc) (v : KiItem) : Persistent (kiItemIs (GF := GF) p v) := by
  unfold kiItemIs; infer_instance

theorem kiItemLess_swo : StrictWeakOrder kiItemLess where
  irrefl a := goStringLt_irrefl a.2
  trans _ _ _ h1 h2 := goStringLt_trans h1 h2
  incomp_trans a b c h1 h2 h3 h4 := by
    have e1 := goStringLt_eq_of_not_lt h1 h2
    have e2 := goStringLt_eq_of_not_lt h3 h4
    unfold kiItemLess
    rw [e1, e2]
    exact ⟨goStringLt_irrefl _, goStringLt_irrefl _⟩

theorem kiKey_agree (p : Loc) (k1 k2 : GoString) :
    ⊢ kiKey (GF := GF) p k1 -∗ kiKey p k2 -∗ ⌜k1 = k2⌝ := by
  unfold kiKey
  iintro ⟨%ks1, #H1, #Hs1⟩ ⟨%ks2, #H2, #Hs2⟩
  icombine H1 H2 gives %Heq
  subst Heq
  ihave %Hv := ownSlice_agree ks1 _ _ _ _ $$ Hs1 Hs2
  ipureintro; exact Hv

/-- A pointer determines its item. -/
theorem kiItemIs_fun (p : Loc) (v1 v2 : KiItem) :
    ⊢ kiItemIs (GF := GF) p v1 -∗ kiItemIs p v2 -∗ ⌜v1 = v2⌝ := by
  unfold kiItemIs
  iintro ⟨%H1, #Hk1⟩ ⟨%H2, #Hk2⟩
  ihave %Hk := kiKey_agree p v1.2 v2.2 $$ Hk1 Hk2
  ipureintro
  exact Prod.ext (H1.symm.trans H2) Hk

/-! ### The tree's fractions: `ownBTree` split, `ownKi` split and combine -/

theorem ownBTree_split' {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) (dq1 dq2 : DFrac) :
    ownBTree T t isItem less items (dq1 • dq2) ⊢
      ownBTree T t isItem less items dq1 ∗ ownBTree T t isItem less items dq2 := by
  unfold ownBTree
  iintro ⟨%h, %zs, Ht, %Hz, #Hall⟩
  icases btree.ownBTree_split _ t dq1 dq2 _ $$ Ht with ⟨Ht1, Ht2⟩
  isplitl [Ht1]
  · iexists h, zs; iframe Ht1; isplitl []; · ipureintro; exact Hz
    iexact Hall
  · iexists h, zs; iframe Ht2; isplitl []; · ipureintro; exact Hz
    iexact Hall

theorem revVal_inj {a b : Rev} (h : revVal a = revVal b) : a = b := by
  have := congrArg revOf h
  simpa using this

theorem map_revVal_inj : ∀ (l1 l2 : List Rev), l1.map revVal = l2.map revVal → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [revVal_inj h.1, map_revVal_inj l1 l2 h.2]

theorem ownGen_split (gv : generation) (gm : Gen) (dq1 dq2 : DFrac) :
    ownGen (GF := GF) gv gm (dq1 • dq2) ⊢ ownGen gv gm dq1 ∗ ownGen gv gm dq2 := by
  unfold ownGen
  iintro ⟨%Hp, Hr, Hc⟩
  icases btree.slice_split dq1 dq2 _ _ $$ Hr with ⟨Hr1, Hr2⟩
  icases btree.cap_split Revision dq1 dq2 _ $$ Hc with ⟨Hc1, Hc2⟩
  isplitl [Hr1 Hc1]
  · iframe; ipureintro; exact Hp
  · iframe; ipureintro; exact Hp

theorem ownGen_combine (gv : generation) (gm1 gm2 : Gen) (dq1 dq2 : DFrac) :
    ⊢ ownGen (GF := GF) gv gm1 dq1 -∗ ownGen gv gm2 dq2 -∗ ⌜gm1 = gm2⌝ ∗ ownGen gv gm1 (dq1 • dq2) := by
  unfold ownGen
  iintro ⟨%Hp1, Hr1, Hc1⟩ ⟨%Hp2, Hr2, Hc2⟩
  ihave %Hrevs := ownSlice_agree _ _ _ _ _ $$ Hr1 Hr2
  have hgm : gm1 = gm2 := by
    cases gm1; cases gm2
    simp only at Hp1 Hp2 Hrevs
    obtain ⟨h1, h2⟩ := Hp1
    obtain ⟨h1', h2'⟩ := Hp2
    have hrevs := map_revVal_inj _ _ Hrevs
    simp only [Gen.mk.injEq]
    exact ⟨h1.symm.trans h1', revVal_inj (h2.symm.trans h2'), hrevs⟩
  subst hgm
  isplitl []
  · ipureintro; rfl
  isplitl []
  · ipureintro; exact Hp1
  isplitl [Hr1 Hr2]
  · iapply btree.slice_combine dq1 dq2 _ _; iframe
  iapply btree.cap_combine Revision dq1 dq2 _; iframe

theorem ownGensL_split (dq1 dq2 : DFrac) : ∀ (gvs : List generation) (gens : List Gen),
    ownGensL (GF := GF) (dq1 • dq2) gvs gens ⊢ ownGensL dq1 gvs gens ∗ ownGensL dq2 gvs gens
  | [], [] => by simp only [ownGensL]; iintro _; isplitl [] <;> itrivial
  | gv :: gvs, gm :: gens => by
    simp only [ownGensL]
    iintro ⟨H, Hs⟩
    icases ownGen_split gv gm dq1 dq2 $$ H with ⟨H1, H2⟩
    icases ownGensL_split dq1 dq2 gvs gens $$ Hs with ⟨Hs1, Hs2⟩
    isplitl [H1 Hs1] <;> iframe
  | [], _ :: _ => by simp only [ownGensL]; iintro %h; exact h.elim
  | _ :: _, [] => by simp only [ownGensL]; iintro %h; exact h.elim

theorem ownGensL_combine (dq1 dq2 : DFrac) : ∀ (gvs : List generation) (gens1 gens2 : List Gen),
    ⊢ ownGensL (GF := GF) dq1 gvs gens1 -∗ ownGensL dq2 gvs gens2 -∗
      ⌜gens1 = gens2⌝ ∗ ownGensL (dq1 • dq2) gvs gens1
  | [], [], [] => by simp only [ownGensL]; iintro _ _; isplitl [] <;> itrivial
  | gv :: gvs, gm1 :: gens1, gm2 :: gens2 => by
    simp only [ownGensL]
    iintro ⟨H1, Hs1⟩ ⟨H2, Hs2⟩
    icases ownGen_combine gv gm1 gm2 dq1 dq2 $$ H1 H2 with ⟨%Hg, H⟩
    icases ownGensL_combine dq1 dq2 gvs gens1 gens2 $$ Hs1 Hs2 with ⟨%Hgs, Hs⟩
    subst Hg Hgs
    isplitl []
    · ipureintro; rfl
    iframe
  | [], _ :: _, _ => by simp only [ownGensL]; iintro %h _; exact h.elim
  | [], [], _ :: _ => by simp only [ownGensL]; iintro _ %h; exact h.elim
  | _ :: _, [], _ => by simp only [ownGensL]; iintro %h _; exact h.elim
  | _ :: _, _ :: _, [] => by simp only [ownGensL]; iintro _ %h; exact h.elim

theorem ownGens_split (gs : GoSlice) (gens : List Gen) (dq1 dq2 : DFrac) :
    ownGens (GF := GF) gs gens (dq1 • dq2) ⊢ ownGens gs gens dq1 ∗ ownGens gs gens dq2 := by
  unfold ownGens
  iintro ⟨%gvs, Hs, Hc, Hl⟩
  icases btree.slice_split dq1 dq2 _ _ $$ Hs with ⟨Hs1, Hs2⟩
  icases btree.cap_split generation dq1 dq2 _ $$ Hc with ⟨Hc1, Hc2⟩
  icases ownGensL_split dq1 dq2 gvs gens $$ Hl with ⟨Hl1, Hl2⟩
  isplitl [Hs1 Hc1 Hl1]
  · iexists gvs; iframe
  · iexists gvs; iframe

theorem ownGens_combine (gs : GoSlice) (gens1 gens2 : List Gen) (dq1 dq2 : DFrac) :
    ⊢ ownGens (GF := GF) gs gens1 dq1 -∗ ownGens gs gens2 dq2 -∗
      ⌜gens1 = gens2⌝ ∗ ownGens gs gens1 (dq1 • dq2) := by
  unfold ownGens
  iintro ⟨%gvs1, Hs1, Hc1, Hl1⟩ ⟨%gvs2, Hs2, Hc2, Hl2⟩
  ihave %Hgvs := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
  subst Hgvs
  icases ownGensL_combine dq1 dq2 gvs1 gens1 gens2 $$ Hl1 Hl2 with ⟨%Hg, Hl⟩
  subst Hg
  isplitl []
  · ipureintro; rfl
  iexists gvs1
  iframe Hl
  isplitl [Hs1 Hs2]
  · iapply btree.slice_combine dq1 dq2 _ _; iframe
  iapply btree.cap_combine generation dq1 dq2 _; iframe

theorem ownKi_split (p : Loc) (gs : GoSlice) (ki : KeyIndex) (dq1 dq2 : DFrac) :
    ownKi (GF := GF) p gs ki (dq1 • dq2) ⊢ ownKi p gs ki dq1 ∗ ownKi p gs ki dq2 := by
  unfold ownKi
  iintro ⟨Hm, Hg, Hgs⟩
  icases btree.tp_split dq1 dq2 _ _ $$ Hm with ⟨Hm1, Hm2⟩
  icases btree.tp_split dq1 dq2 _ _ $$ Hg with ⟨Hg1, Hg2⟩
  icases ownGens_split gs ki.gens dq1 dq2 $$ Hgs with ⟨Hgs1, Hgs2⟩
  isplitl [Hm1 Hg1 Hgs1] <;> iframe

/-- Two fractions of a key index agree on its generations slice and its model. -/
theorem ownKi_combine (p : Loc) (gs1 gs2 : GoSlice) (ki1 ki2 : KeyIndex) (dq1 dq2 : DFrac) :
    ⊢ ownKi (GF := GF) p gs1 ki1 dq1 -∗ ownKi p gs2 ki2 dq2 -∗
      ⌜gs1 = gs2 ∧ ki1 = ki2⌝ ∗ ownKi p gs1 ki1 (dq1 • dq2) := by
  unfold ownKi
  iintro ⟨Hm1, Hg1, Hgs1⟩ ⟨Hm2, Hg2, Hgs2⟩
  icombine Hm1 Hm2 gives %Hm
  icombine Hg1 Hg2 gives %Hg
  subst Hg
  icases ownGens_combine gs1 ki1.gens ki2.gens dq1 dq2 $$ Hgs1 Hgs2 with ⟨%Hgens, Hgs⟩
  have hki : ki1 = ki2 := by
    cases ki1; cases ki2
    simp only at Hm Hgens
    simp only [KeyIndex.mk.injEq]
    exact ⟨revVal_inj Hm, Hgens⟩
  subst hki
  isplitl []
  · ipureintro; exact ⟨rfl, rfl⟩
  iframe Hgs
  isplitl [Hm1 Hm2]
  · iapply btree.tp_combine dq1 dq2 _ _; iframe
  iapply btree.tp_combine dq1 dq2 _ _; iframe

theorem ownKi_split_own (p : Loc) (gs : GoSlice) (ki : KeyIndex) (q1 q2 : Qp) :
    ownKi (GF := GF) p gs ki (DFrac.own (q1 + q2)) ⊢
      ownKi p gs ki (DFrac.own q1) ∗ ownKi p gs ki (DFrac.own q2) :=
  ownKi_split p gs ki (DFrac.own q1) (DFrac.own q2)

theorem ownBTree_split_own {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (T : go.GoType) [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) (items : List V) (q1 q2 : Qp) :
    ownBTree T t isItem less items (DFrac.own (q1 + q2)) ⊢
      ownBTree T t isItem less items (DFrac.own q1) ∗ ownBTree T t isItem less items (DFrac.own q2) :=
  ownBTree_split' T t isItem less items (DFrac.own q1) (DFrac.own q2)

/-! ### The tree with its key indexes -/

/-- An entry's key index: its pointer (not `nil`) and its mutable part, at fraction `q`. -/
def ownEntry (z : IdxEntry) (q : Qp) : IProp GF :=
  iprop(⌜z.1 ≠ null⌝ ∗ ∃ gs : GoSlice, ownKi z.1 gs z.2.2 (DFrac.own q))

/-- The tree at `t` and its key indexes hold the entries `L` (keys strictly increasing), at
fraction `q`. -/
def ownTree (t : Loc) (L : List IdxEntry) (q : Qp) : IProp GF :=
  iprop(⌜(itemsOfEntries L).Pairwise kiItemLess⌝ ∗
    ownBTree kiPtrT t kiItemIs kiItemLess (itemsOfEntries L) (DFrac.own q) ∗
    [∗list] z ∈ L, ownEntry z q)

theorem bigSepL_ownKi_split (L : List IdxEntry) (q1 q2 : Qp) :
    ([∗list] z ∈ L, ownEntry (GF := GF) z (q1 + q2)) ⊢
      ([∗list] z ∈ L, ownEntry z q1) ∗ ([∗list] z ∈ L, ownEntry z q2) := by
  induction L with
  | nil => iintro _; isplitl [] <;> (iapply BigSepL.bigSepL_nil_intro; iempintro)
  | cons z L ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hz, Hs⟩
    iunfold ownEntry at Hz
    icases Hz with ⟨%Hn, %gs, H⟩
    icases ownKi_split_own _ _ _ _ _ $$ H with ⟨H1, H2⟩
    icases ih $$ Hs with ⟨Hs1, Hs2⟩
    isplitl [H1 Hs1]
    · iapply BigSepL.bigSepL_cons.2; iframe Hs1; iunfold ownEntry; isplitl []
      · ipureintro; exact Hn
      iexists gs; iexact H1
    · iapply BigSepL.bigSepL_cons.2; iframe Hs2; iunfold ownEntry; isplitl []
      · ipureintro; exact Hn
      iexists gs; iexact H2

theorem bigSepL_ownKi_combine (L1 : List IdxEntry) (q1 q2 : Qp) :
    ∀ (L2 : List IdxEntry), itemsOfEntries L1 = itemsOfEntries L2 →
    ⊢ ([∗list] z ∈ L1, ownEntry (GF := GF) z q1) -∗ ([∗list] z ∈ L2, ownEntry z q2) -∗
      ⌜L1 = L2⌝ ∗ [∗list] z ∈ L1, ownEntry z (q1 + q2) := by
  induction L1 with
  | nil =>
    intro L2 h
    cases L2 with
    | nil => iintro _ _; isplitl []; · ipureintro; rfl
             iapply BigSepL.bigSepL_nil_intro; iempintro
    | cons _ _ => simp [itemsOfEntries] at h
  | cons z L ih =>
    intro L2 h
    cases L2 with
    | nil => simp [itemsOfEntries] at h
    | cons z' L' =>
      obtain ⟨z1, z2, z3⟩ := z
      obtain ⟨z1', z2', z3'⟩ := z'
      simp only [itemsOfEntries, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, h⟩ := h
      iintro H1 H2
      icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨Hz1, Hs1⟩
      icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hz2, Hs2⟩
      iunfold ownEntry at Hz1
      iunfold ownEntry at Hz2
      icases Hz1 with ⟨%Hn, %gs1, H1⟩
      icases Hz2 with ⟨-, %gs2, H2⟩
      icases ownKi_combine _ _ _ _ _ _ _ $$ H1 H2 with ⟨%Hp, H⟩
      icases ih L' (by unfold itemsOfEntries; exact h) $$ Hs1 Hs2 with ⟨%HL, Hs⟩
      isplitl []
      · ipureintro
        simp only at Hp
        rw [HL, Hp.2]
      iapply BigSepL.bigSepL_cons.2
      iframe Hs
      iunfold ownEntry
      isplitl []
      · ipureintro; exact Hn
      iexists gs1
      rw [show DFrac.own (q1 + q2) = DFrac.own q1 • DFrac.own q2 from rfl]
      iexact H

/-- Inserting an entry (by key) into the entries' resources. -/
theorem bigSepL_ownEntry_insert (z0 : IdxEntry) (q : Qp) : ∀ (L : List IdxEntry),
    ownEntry (GF := GF) z0 q ∗ ([∗list] z ∈ L, ownEntry z q) ⊢
      [∗list] z ∈ btInsert entryLess z0 L, ownEntry z q
  | [] => by
    iintro ⟨H0, -⟩
    simp only [btInsert]
    iapply BigSepL.bigSepL_cons.2
    iframe H0
    iapply BigSepL.bigSepL_nil_intro; iempintro
  | w :: ws => by
    iintro ⟨H0, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hw, Hs⟩
    unfold btInsert
    split
    · iapply BigSepL.bigSepL_cons.2
      iframe Hw
      iapply bigSepL_ownEntry_insert z0 q ws
      iframe
    · split
      · iapply BigSepL.bigSepL_cons.2
        iframe H0
        iapply BigSepL.bigSepL_cons.2
        iframe
      · iapply BigSepL.bigSepL_cons.2
        iframe H0 Hs

/-- Two fractions of the tree hold the same entries (the key indexes' models agree). -/
theorem ownTree_combine (t : Loc) (L1 L2 : List IdxEntry) (q1 q2 : Qp) :
    ⊢ ownTree (GF := GF) t L1 q1 -∗ ownTree t L2 q2 -∗ ⌜L1 = L2⌝ ∗ ownTree t L1 (q1 + q2) := by
  unfold ownTree
  iintro ⟨%Hs1, Ht1, Hk1⟩ ⟨-, Ht2, Hk2⟩
  ihave Hc := ownBTree_combine kiPtrT t kiItemIs kiItemLess (itemsOfEntries L1) (itemsOfEntries L2)
    (DFrac.own q1) (DFrac.own q2) kiItemIs_fun $$ [Ht1 Ht2]
  · iframe
  icases Hc with ⟨%Hitems, Ht⟩
  icases bigSepL_ownKi_combine L1 q1 q2 L2 Hitems $$ Hk1 Hk2 with ⟨%HL, Hk⟩
  subst HL
  isplitl []
  · ipureintro; rfl
  isplitl []
  · ipureintro; exact Hs1
  iframe Hk
  rw [show DFrac.own (q1 + q2) = DFrac.own q1 • DFrac.own q2 from rfl]
  iexact Ht

instance ownTree_fractional (t : Loc) (L : List IdxEntry) :
    Fractional (fun q => ownTree (GF := GF) t L q) where
  fractional q1 q2 := by
    refine ⟨?_, ?_⟩
    · unfold ownTree
      iintro ⟨%Hs, Ht, Hk⟩
      icases ownBTree_split_own kiPtrT t kiItemIs kiItemLess _ q1 q2 $$ Ht with ⟨Ht1, Ht2⟩
      icases bigSepL_ownKi_split L q1 q2 $$ Hk with ⟨Hk1, Hk2⟩
      isplitl [Ht1 Hk1]
      · iframe Ht1 Hk1; ipureintro; exact Hs
      · iframe Ht2 Hk2; ipureintro; exact Hs
    · iintro ⟨H1, H2⟩
      icases ownTree_combine t L L q1 q2 $$ H1 H2 with ⟨-, H⟩
      iexact H

/-! ### The lock invariant, the writer and the certificate -/

/-- The ghost names of a tree index: its history and its number of events. -/
structure IdxNames where
  hist : GName
  nev : GName

/-- The writer's log, well formed and bounded: `ilog` committed, `pend` pending. -/
def IdxWf (ilog : Log) (pend : List Change) : Prop :=
  LogWf' (ilog ++ [pend]) ∧ ilog.length + 1 < 2 ^ 63 ∧ pend.length < 2 ^ 63 ∧
    ∀ cs ∈ ilog, cs.length < 2 ^ 63

/-- The `RWMutex`'s resource at fraction `q` (see the module docstring). -/
def idxLockInv (t : Loc) (γ : IdxNames) (q : Qp) : IProp GF :=
  iprop(∃ (ilog : Log) (pend : List Change) (L : List IdxEntry),
    "#Hhist" ∷ monoListLbOwn γ.hist (histShape ilog pend) ∗
    "Hnev" ∷ monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length ∗
    "Htree" ∷ ownTree t L q ∗
    "%HL" ∷ ⌜idxOfEntries L = indexOf (evsOf (ilog ++ [pend]))⌝ ∗
    "%Hwf" ∷ ⌜IdxWf ilog pend⌝)

instance idxLockInv_fractional (t : Loc) (γ : IdxNames) :
    Fractional (idxLockInv (GF := GF) t γ) where
  fractional q1 q2 := by
    have hnat := fun n => (monoNatAuthOwn_fractional (GF := GF) γ.nev n).fractional q1 q2
    refine ⟨?_, ?_⟩
    · iintro H
      unfold idxLockInv
      iNamed H
      icases (hnat _).1 $$ Hnev with ⟨Hn1, Hn2⟩
      icases (ownTree_fractional t L).fractional q1 q2 |>.1 $$ Htree with ⟨Ht1, Ht2⟩
      isplitl [Hn1 Ht1]
      · iexists ilog, pend, L; simp only [named]; iframe Hn1 Ht1; iframe #; ipureintro; exact ⟨HL, Hwf⟩
      · iexists ilog, pend, L; simp only [named]; iframe Hn2 Ht2; iframe #; ipureintro; exact ⟨HL, Hwf⟩
    · iintro ⟨H1, H2⟩
      unfold idxLockInv
      icases H1 with ⟨%ilog1, %pend1, %L1, H1⟩
      icases H2 with ⟨%ilog2, %pend2, %L2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      generalize hn1 : (evsOf (ilog1 ++ [pend1])).length = n1 at *
      generalize hn2 : (evsOf (ilog2 ++ [pend2])).length = n2 at *
      icases monoNatAuthOwn_agree γ.nev q1 q2 n1 n2 $$ Hnev1 Hnev2 with %Hn
      obtain ⟨-, Hn⟩ := Hn
      subst Hn
      icases ownTree_combine t L1 L2 q1 q2 $$ Htree1 Htree2 with ⟨%HL, Htree⟩
      subst HL
      iexists ilog1, pend1, L1
      simp only [named]
      iframe Htree
      isplitl []
      · iexact Hhist1
      isplitl [Hnev1 Hnev2]
      · rw [hn1]; iapply (hnat n1).2; iframe
      ipureintro; exact ⟨HL1, Hwf1⟩

end reprs


section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of the embedded `RWMutex`. -/
abbrev idxMuAddr (ti : Loc) : Loc := structFieldRef treeIndex go!"RWMutex" ti

end addrs

section reprs2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A tree index (persistent): its tree and logger, and the lock's guard (writers lock through
it). -/
def isTreeIndex (ti : Loc) (γ : IdxNames) : IProp GF :=
  iprop(∃ (t lg : Loc),
    "#Htree" ∷ ti.[treeIndex, go!"tree"] ↦□ t ∗
    "#Hlg" ∷ ti.[treeIndex, go!"lg"] ↦□ lg ∗
    "#Hmu" ∷ sync.isRWMutexGuard (idxMuAddr ti) (idxLockInv t γ))

instance isTreeIndex_persistent (ti : Loc) (γ : IdxNames) : Persistent (isTreeIndex (GF := GF) ti γ) := by
  unfold isTreeIndex; infer_instance

/-- A reader's token: one of the `RWMutex`'s bounded reader slots (`RLock` needs one). -/
def idxReader (ti : Loc) (γ : IdxNames) : IProp GF :=
  iprop(∃ t : Loc, ti.[treeIndex, go!"tree"] ↦□ t ∗ sync.ownRWMutex (idxMuAddr ti) (idxLockInv t γ))

/-- The writer's handle: the history's authority (`ilog` committed, `pend` put so far) and a
lower bound of the event count at its last write. -/
def idxWriter (γ : IdxNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (histShape ilog pend) ∗
    monoNatLbOwn γ.nev (evsOf (ilog ++ [pend])).length ∗ ⌜IdxWf ilog pend⌝)

theorem idxWriter_wf (γ : IdxNames) (ilog : Log) (pend : List Change) :
    idxWriter (GF := GF) γ ilog pend ⊢ ⌜IdxWf ilog pend⌝ := by
  unfold idxWriter; iintro ⟨-, -, %H⟩; ipureintro; exact H

/-- The certificate of a committed log `log`: its history is a prefix of the index's, and the
index had all its events. -/
def idxCert (γ : IdxNames) (log : Log) : IProp GF :=
  iprop(monoListLbOwn γ.hist (histOf log) ∗ monoNatLbOwn γ.nev (evsOf log).length ∗
    ⌜LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝)

instance idxCert_persistent (γ : IdxNames) (log : Log) : Persistent (idxCert (GF := GF) γ log) := by
  unfold idxCert; infer_instance

theorem LogWf'.append_nil {log : Log} (h : LogWf' log) (hne : log ≠ []) : LogWf' (log ++ [[]]) := by
  refine ⟨fun _ => ?_, fun r cs i k hr hi => ?_⟩
  · rw [List.getElem?_append_left (List.length_pos_iff.2 hne)]; exact h.1 hne
  · by_cases hlt : r < log.length
    · rw [List.getElem?_append_left hlt] at hr
      have := h.2 r cs i k hr hi
      rw [stateAt_append_lt _ _ (by omega)]
      exact this
    · rw [List.getElem?_append_right (by omega)] at hr
      have : r - log.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hr).1
        simp at this; omega
      rw [this] at hr
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      simp at hi

/-- **Commit** (a ghost step, outside the index lock): the pending revision is closed, and the
committed log is certified. -/
theorem idxWriter_commit (γ : IdxNames) (ilog : Log) (pend : List Change)
    (hlen : ilog.length + 2 < 2 ^ 63) (hne : ilog ≠ []) :
    ⊢ idxWriter (GF := GF) γ ilog pend ==∗ idxWriter γ (ilog ++ [pend]) [] ∗ idxCert γ (ilog ++ [pend]) := by
  unfold idxWriter idxCert
  iintro ⟨Hauth, #Hnev, %Hwf⟩
  obtain ⟨hwf, hl, hp, hcs⟩ := Hwf
  imod monoListAuthOwn_update_app [HistItem.commit] $$ Hauth with ⟨Hauth, #Hlb⟩
  imodintro
  have hwf' : LogWf' (ilog ++ [pend] ++ [[]]) := hwf.append_nil (by simp)
  have hcs' : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63 := by
    intro cs hcs'
    rcases List.mem_append.1 hcs' with h | h
    · exact hcs cs h
    · rw [List.mem_singleton] at h; rw [h]; exact hp
  have hhist : histShape (ilog ++ [pend]) [] = histShape ilog pend ++ [HistItem.commit] :=
    (histShape_commit ilog pend).symm
  have hhist2 : histOf (ilog ++ [pend]) = histShape ilog pend ++ [HistItem.commit] := by
    rw [histShape_commit]; simp [histShape, evsOfRev]
  have hevs : evsOf (ilog ++ [pend] ++ [[]]) = evsOf (ilog ++ [pend]) := by
    rw [evsOf_append (ilog ++ [pend]) []]; simp [evsOfRev]
  rw [hhist, hhist2, hevs]
  isplitl [Hauth]
  · iframe Hauth
    isplitl []
    · iexact Hnev
    ipureintro
    refine ⟨hwf', by simp; omega, by simp, hcs'⟩
  · isplitl []
    · iexact Hlb
    isplitl []
    · iexact Hnev
    ipureintro
    exact ⟨hwf, by simp; omega, hcs'⟩


/-! ### What a reader of the index knows -/

/-- What a reader of the index knows of its contents: the certificate of a committed log, or
the writer's own handle (its committed log with its pending revision). -/
inductive IdxKnow where
  | cert (log : Log)
  | writer (ilog : Log) (pend : List Change)

/-- The log the knowledge is of: the index's answers at revisions below its length are its
(`idxKnows_facts`, then `reader_answer`/`reader_range`). -/
def IdxKnow.log : IdxKnow → Log
  | .cert log => log
  | .writer ilog pend => ilog ++ [pend]

@[simp] theorem IdxKnow.log_cert (log : Log) : (IdxKnow.cert log).log = log := rfl
@[simp] theorem IdxKnow.log_writer (ilog : Log) (pend : List Change) :
    (IdxKnow.writer ilog pend).log = ilog ++ [pend] := rfl

/-- The resource of the knowledge: the certificate, or the writer's handle (which the index's
readers give back as is). -/
def idxKnows (γ : IdxNames) : IdxKnow → IProp GF
  | .cert log => idxCert γ log
  | .writer ilog pend => idxWriter γ ilog pend

theorem idxKnows_cert (γ : IdxNames) (log : Log) :
    idxKnows (GF := GF) γ (.cert log) = idxCert γ log := rfl
theorem idxKnows_writer (γ : IdxNames) (ilog : Log) (pend : List Change) :
    idxKnows (GF := GF) γ (.writer ilog pend) = idxWriter γ ilog pend := rfl

/-- The lock's events are the writer's. -/
theorem writer_events (ilog ilog' : Log) (pend pend' : List Change)
    (hpre : histShape ilog' pend' <+: histShape ilog pend)
    (hcnt : (evsOf (ilog ++ [pend])).length ≤ (evsOf (ilog' ++ [pend'])).length) :
    evsOf (ilog' ++ [pend']) = evsOf (ilog ++ [pend]) := by
  have := evsOfHist_prefix_eq _ _ hpre
    (by rw [evsOfHist_histShape, evsOfHist_histShape]; exact hcnt)
  rw [evsOfHist_histShape, evsOfHist_histShape] at this
  exact this

/-- Under the index's lock (its history's lower bound and its event count: `idxLockInv`), what
the reader knows gives the reader lemmas' premises: its log's history is comparable with the
lock's and its events are among the lock's, and the log is well formed and bounded. -/
theorem idxKnows_facts (γ : IdxNames) (kn : IdxKnow) (log : Log) (hlog : kn.log = log)
    (ilog : Log) (pend : List Change) (q : Qp) :
    ⊢ idxKnows (GF := GF) γ kn -∗ monoListLbOwn γ.hist (histShape ilog pend) -∗
      monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length -∗
      ⌜(histOf log <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log) ∧
        (evsOf log).length ≤ (evsOf (ilog ++ [pend])).length ∧ LogWf' log ∧
        log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝ ∗
      idxKnows γ kn ∗ monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length := by
  cases kn with
  | cert log' =>
    simp only [IdxKnow.log] at hlog
    subst hlog
    rw [idxKnows_cert]
    iintro #Hkn #Hlb Hnev
    ihave #Hcert0 : idxCert γ log' $$ []
    · iexact Hkn
    iunfold idxCert at Hkn
    icases Hkn with ⟨#Hclb, #Hcnt, %Hcwf⟩
    ihave %Hcmp := mono_list_lb_valid γ.hist _ _ $$ Hclb Hlb
    ihave %Hcnt' := monoNatLbOwn_valid γ.nev q _ _ $$ Hnev Hcnt
    iframe Hnev
    isplitl []
    · ipureintro; exact ⟨Hcmp, Hcnt'.2, Hcwf.1, Hcwf.2.1, Hcwf.2.2⟩
    iexact Hcert0
  | writer ilog' pend' =>
    simp only [IdxKnow.log] at hlog
    subst hlog
    rw [idxKnows_writer]
    iintro Hkn #Hlb Hnev
    iunfold idxWriter at Hkn
    icases Hkn with ⟨Hauth, #Hwlb, %Hwwf⟩
    ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth Hlb
    ihave %Hcnt := monoNatLbOwn_valid γ.nev q _ _ $$ Hnev Hwlb
    iframe Hnev
    isplitl []
    · ipureintro
      obtain ⟨hwf, hlen, hpend, hcs⟩ := Hwwf
      refine ⟨Or.inr ?_, Hcnt.2, hwf, by simp; omega, ?_⟩
      · have h2 : histOf (ilog' ++ [pend']) = histShape ilog' pend' ++ [HistItem.commit] := by
          rw [histShape_commit]; simp [histShape, evsOfRev]
        rw [h2]
        exact Hpre.2.trans (List.prefix_append _ _)
      · intro cs hcs'
        rcases List.mem_append.1 hcs' with h | h
        · exact hcs cs h
        · rw [List.mem_singleton] at h; rw [h]; exact hpend
    iunfold idxWriter
    iframe Hauth
    iframe #
    ipureintro; exact Hwwf

end reprs2

end mvcc
end EtcdGrove
end Perennial
