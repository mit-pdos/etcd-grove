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
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostVar
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx

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

def Change.enc : Change → Bool × GoString × GoString × w64
  | .put k v l => (false, k, v, l)
  | .del k => (true, k, [], W64 0)

theorem Change.enc_inj : Function.Injective Change.enc := by
  intro x y h
  cases x <;> cases y <;> simp only [Change.enc, Prod.mk.injEq] at h
  · obtain ⟨-, rfl, rfl, rfl⟩ := h; rfl
  · exact Bool.noConfusion h.1
  · exact Bool.noConfusion h.1
  · obtain ⟨-, rfl, -, -⟩ := h; rfl

instance Change.countable : Pos.Countable Change :=
  .ofInjective (fun c => Pos.Countable.encode c.enc) (fun _ _ h => Change.enc_inj (Pos.encode_inj h))

def Ev.enc (e : Ev) : Rev × (Bool × GoString × GoString × w64) := (e.rev, e.change.enc)

theorem Ev.enc_inj : Function.Injective Ev.enc := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Ev.enc, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [Change.enc_inj h]

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

/-- The tree's items are sorted by key. -/
theorem ownTree_sorted (t : Loc) (L : List IdxEntry) (q : Qp) :
    ownTree (GF := GF) t L q ⊢ ownTree t L q ∗ ⌜(itemsOfEntries L).Pairwise kiItemLess⌝ := by
  unfold ownTree
  iintro ⟨%Hs, Ht, Hk⟩
  iframe Ht Hk
  isplitl [] <;> (ipureintro; exact Hs)

/-- An entry of the tree: its pointer is not `nil`, and is a key index of the entry's key, for
good. -/
theorem ownTree_entry (t : Loc) (L : List IdxEntry) (q : Qp) (z : IdxEntry) (hz : z ∈ L) :
    ownTree (GF := GF) t L q ⊢ ownTree t L q ∗ ⌜z.1 ≠ null⌝ ∗ kiKey z.1 z.2.1 := by
  unfold ownTree
  iintro ⟨%Hs, Ht, Hk⟩
  icases BigSepL.bigSepL_mem_acc (Φ := fun z => ownEntry (GF := GF) z q) hz $$ Hk with ⟨Hz, Hback⟩
  iunfold ownEntry at Hz
  icases Hz with ⟨%Hn, Hz⟩
  ihave Hk := Hback $$ [Hz]
  · iunfold ownEntry; iframe Hz; ipureintro; exact Hn
  iunfold ownBTree at Ht
  icases Ht with ⟨%h, %zs, Hbt, %Hzs, #Hall⟩
  have hmem : (z.1, z.2.1) ∈ zs.map Prod.snd := by
    rw [Hzs]; unfold itemsOfEntries; exact List.mem_map_of_mem hz
  obtain ⟨y, hy, hyv⟩ := List.mem_map.1 hmem
  ihave #Hy : kiItemIs y.1 (z.1, z.2.1) $$ []
  · rw [← hyv]; iapply Hall; ipureintro; exact hy
  iunfold kiItemIs at Hy
  icases Hy with ⟨%Hyp, #Hkey⟩
  isplitl [Hbt Hk]
  · iframe Hk
    isplitl []
    · ipureintro; exact Hs
    iunfold ownBTree
    iexists h, zs
    iframe Hbt
    iframe #
    ipureintro; exact Hzs
  isplitl []
  · ipureintro; exact Hn
  simp only at Hyp
  rw [← Hyp]
  iexact Hkey

/-- Deleting (by key) the item of the entry at `j` is erasing the entry, on sorted entries. -/
theorem btDelete_items_eraseIdx : ∀ (L : List IdxEntry), L.Pairwise entryLess → ∀ (j : Nat)
    (z : IdxEntry) (q : Loc), L[j]? = some z →
    btDelete kiItemLess (q, z.2.1) (itemsOfEntries L) = itemsOfEntries (L.eraseIdx j)
  | [], _, j, _, _, h => by simp at h
  | w :: ws, hs, 0, z, q, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [itemsOfEntries, List.map_cons, List.eraseIdx_cons_zero]
    unfold btDelete
    have h1 : ¬ kiItemLess (w.1, w.2.1) (q, w.2.1) := goStringLt_irrefl _
    have h2 : ¬ kiItemLess (q, w.2.1) (w.1, w.2.1) := goStringLt_irrefl _
    rw [ite_eq_right h1, ite_eq_right h2]
  | w :: ws, hs, j + 1, z, q, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.pairwise_cons] at hs
    have hz : z ∈ ws := List.mem_of_getElem? h
    have hw : entryLess w z := hs.1 z hz
    simp only [itemsOfEntries, List.map_cons, List.eraseIdx_cons_succ]
    unfold btDelete
    have h1 : kiItemLess (w.1, w.2.1) (q, z.2.1) := hw
    rw [ite_eq_left h1]
    have := btDelete_items_eraseIdx ws hs.2 j z q h
    unfold itemsOfEntries at this
    rw [this]

theorem idxOfEntries_eraseIdx (L : List IdxEntry) (j : Nat) :
    idxOfEntries (L.eraseIdx j) = (idxOfEntries L).eraseIdx j := by
  unfold idxOfEntries
  induction L generalizing j with
  | nil => simp
  | cons w ws ih => cases j with
    | zero => simp
    | succ j => simp only [List.eraseIdx_cons_succ, List.map_cons, ih]

/-- The entry at `j` taken out of the entries' resources. -/
theorem bigSepL_ownEntry_eraseIdx (q : Qp) : ∀ (L : List IdxEntry) (j : Nat) (z : IdxEntry),
    L[j]? = some z →
    ([∗list] y ∈ L, ownEntry (GF := GF) y q) ⊢ ownEntry z q ∗ [∗list] y ∈ L.eraseIdx j, ownEntry y q
  | [], _, _, h => by simp at h
  | w :: ws, 0, z, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [List.eraseIdx_cons_zero]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hw, Hs⟩
    iframe Hw Hs
  | w :: ws, j + 1, z, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.eraseIdx_cons_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hw, Hs⟩
    icases bigSepL_ownEntry_eraseIdx q ws j z h $$ Hs with ⟨Hz, Hs⟩
    iframe Hz
    iapply BigSepL.bigSepL_cons.2
    iframe Hw Hs

/-- Every entry's pointer is a key index of the entry's key, for good. -/
theorem ownTree_keys (t : Loc) (L : List IdxEntry) (q : Qp) :
    ownTree (GF := GF) t L q ⊢ ownTree t L q ∗ □ (∀ z, ⌜z ∈ L⌝ -∗ kiKey z.1 z.2.1) := by
  unfold ownTree
  iintro ⟨%Hs, Ht, Hk⟩
  iunfold ownBTree at Ht
  icases Ht with ⟨%h, %zs, Hbt, %Hzs, #Hall⟩
  isplitl [Hbt Hk]
  · iframe Hk
    isplitl []
    · ipureintro; exact Hs
    iunfold ownBTree
    iexists h, zs
    iframe Hbt
    iframe #
    ipureintro; exact Hzs
  imodintro
  iintro %z %hz
  have hmem : (z.1, z.2.1) ∈ zs.map Prod.snd := by
    rw [Hzs]; unfold itemsOfEntries; exact List.mem_map_of_mem hz
  obtain ⟨y, hy, hyv⟩ := List.mem_map.1 hmem
  ihave #Hy : kiItemIs y.1 (z.1, z.2.1) $$ []
  · rw [← hyv]; iapply Hall; ipureintro; exact hy
  iunfold kiItemIs at Hy
  icases Hy with ⟨%Hyp, #Hkey⟩
  simp only at Hyp
  rw [← Hyp]
  iexact Hkey

/-- Entries sorted by key, each pointer a key index of its key: the pointers are distinct. -/
theorem kiKeys_nodup (L : List IdxEntry) (hs : L.Pairwise entryLess) :
    (□ ∀ z, ⌜z ∈ L⌝ -∗ kiKey (GF := GF) z.1 z.2.1) ⊢ ⌜(L.map Prod.fst).Nodup⌝ := by
  iintro #H
  ihave %Hk : ⌜∀ (a b : IdxEntry), a ∈ L → b ∈ L → a.1 = b.1 → a.2.1 = b.2.1⌝ $$ []
  · iapply pure_forall.2; iintro %a
    iapply pure_forall.2; iintro %b
    iapply pure_forall.2; iintro %ha
    iapply pure_forall.2; iintro %hb
    iapply pure_forall.2; iintro %hab
    ihave #Ha := H $$ %a %ha
    ihave #Hb := H $$ %b %hb
    rw [hab]
    iapply kiKey_agree $$ Ha Hb
  ipureintro
  unfold List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hlt heq => ?_) hs
  have := Hk a b ha hb heq
  unfold entryLess at hlt
  rw [this] at hlt
  exact goStringLt_irrefl _ hlt

/-! ### The lock invariant, the writer and the certificate -/

/-- The ghost names of a tree index: its history, its number of events, and the committed log
(a monotone list of the revisions' changes: the history records the events, not the values, so
the certificate carries the log itself through this one); and the store's compaction revision
(`crev`, a monotone counter of `crevN c`: its authority is split between the store's two locks
and the compaction right, `InvStore.lean`; the index's lock keeps a lower bound of every key's
compaction level, `idxLockInv`). -/
structure IdxNames where
  hist : GName
  nev : GName
  log : GName
  crev : GName
  /-- the compactor's state (`ghostVar (Int × List Loc)`: the revision of the last compaction and
  the key indexes a compaction in progress has yet to visit), half in the lock's resource
  (`idxCmpOwn`), half the compactor's (`idxCompactor`) -/
  cmp : GName

/-- The writer's log, well formed and bounded: `ilog` committed, `pend` pending. -/
def IdxWf (ilog : Log) (pend : List Change) : Prop :=
  LogWf' (ilog ++ [pend]) ∧ ilog.length + 1 < 2 ^ 63 ∧ pend.length < 2 ^ 63 ∧
    ∀ cs ∈ ilog, cs.length < 2 ^ 63

/-- Part `q` of the compaction revision's authority, at `c` (`-1`: none): whoever holds a part
knows the compaction revision is `c` (the store's locks and the compaction right hold the
parts). -/
def crevUB (γ : IdxNames) (q : Qp) (c : Int) : IProp GF := monoNatAuthOwn γ.crev q (crevN c)

/-- A lower bound `c` of the compaction revision (persistent). -/
def crevLb (γ : IdxNames) (c : Int) : IProp GF := monoNatLbOwn γ.crev (crevN c)

instance crevLb_persistent (γ : IdxNames) (c : Int) : Persistent (crevLb (GF := GF) γ c) := by
  unfold crevLb; infer_instance

/-- A part of the authority bounds every lower bound. -/
theorem crevUB_lb (γ : IdxNames) (q : Qp) (c c' : Int) (hc : -1 ≤ c) (hc' : -1 ≤ c') :
    ⊢ crevUB (GF := GF) γ q c -∗ crevLb γ c' -∗ ⌜c' ≤ c⌝ := by
  unfold crevUB crevLb
  iintro Ha Hl
  ihave %h := monoNatLbOwn_valid γ.crev q _ _ $$ Ha Hl
  ipureintro; exact crevN_le hc' hc h.2

/-- **The compactor's state in the lock's resource** (at the lock's fraction `q`, half of it):
the revision `cc` of the last compaction, at or above every key's level (`cmax`), and the key
indexes `P` a compaction in progress has yet to visit, all in the tree (no one but the compactor
removes them: replacing a key index, `Insert`, needs no compaction, `cmax < 0`). -/
def idxCmpOwn (γ : IdxNames) (q : Qp) (L : List IdxEntry) (cmax : Int) : IProp GF :=
  iprop(∃ (cc : Int) (P : List Loc), ghostVar γ.cmp q.half (cc, P) ∗
    ⌜cmax ≤ cc ∧ (∀ p ∈ P, p ∈ L.map Prod.fst) ∧ (P ≠ [] → 0 ≤ cmax)⌝)

/-- **The compactor's token** (exclusive: one compaction at a time; the store's compaction job
runs on the FIFO scheduler): the revision of the last compaction, `-1` if none. -/
def idxCompactor (γ : IdxNames) (c : Int) : IProp GF := ghostVar γ.cmp (1 : Qp).half (c, ([] : List Loc))

theorem Qp.half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half :=
  Subtype.ext (by simp only [Qp.val_half, Qp.val_add]; grind)

/-- The writers keep every key index in the tree (they add some). -/
theorem idxCmpOwn_mono (γ : IdxNames) (q : Qp) (L L' : List IdxEntry) (cmax : Int)
    (h : ∀ p ∈ L.map Prod.fst, p ∈ L'.map Prod.fst) :
    idxCmpOwn (GF := GF) γ q L cmax ⊢ idxCmpOwn γ q L' cmax := by
  unfold idxCmpOwn
  iintro ⟨%cc, %P, H, %Hp⟩
  iexists cc, P
  iframe H
  ipureintro
  exact ⟨Hp.1, fun p hp => h p (Hp.2.1 p hp), Hp.2.2⟩

/-- With no compaction (`cmax < 0`), no compaction is in progress: any tree. -/
theorem idxCmpOwn_neg (γ : IdxNames) (q : Qp) (L L' : List IdxEntry) (cmax : Int) (h : cmax < 0) :
    idxCmpOwn (GF := GF) γ q L cmax ⊢ idxCmpOwn γ q L' cmax := by
  unfold idxCmpOwn
  iintro ⟨%cc, %P, H, %Hp⟩
  iexists cc, P
  iframe H
  ipureintro
  refine ⟨Hp.1, fun p hp => ?_, Hp.2.2⟩
  exfalso
  have := Hp.2.2 (List.ne_nil_of_mem hp)
  omega

/-- Changing an entry in place keeps the pointers. -/
theorem ptrs_set (L : List IdxEntry) (i : Nat) (z z' : IdxEntry) (hi : L[i]? = some z)
    (h : z'.1 = z.1) : (L.set i z').map Prod.fst = L.map Prod.fst := by
  have hlt : i < L.length := (List.getElem?_eq_some_iff.1 hi).1
  have hz : L[i] = z := (List.getElem?_eq_some_iff.1 hi).2
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_set]
  split
  · rename_i hj; subst hj; rw [hz, h]
  · rfl

/-- Inserting an entry of a new key keeps the pointers. -/
theorem ptrs_btInsert_new : ∀ (L : List IdxEntry) (z : IdxEntry), (∀ w ∈ L, w.2.1 ≠ z.2.1) →
    ∀ p ∈ L.map Prod.fst, p ∈ (btInsert entryLess z L).map Prod.fst
  | [], _, _, p, hp => by simp at hp
  | w :: ws, z, hn, p, hp => by
    unfold btInsert
    split
    · rcases List.mem_cons.1 hp with rfl | hp
      · simp
      · simp only [List.map_cons, List.mem_cons]
        exact Or.inr (ptrs_btInsert_new ws z (fun w' hw' => hn w' (List.mem_cons_of_mem _ hw')) p hp)
    · split
      · simp only [List.map_cons, List.mem_cons] at hp ⊢; exact Or.inr hp
      · rename_i h1 h2
        exact absurd (goStringLt_eq_of_not_lt h1 h2) (hn w List.mem_cons_self)

theorem idxCmpOwn_split (γ : IdxNames) (L : List IdxEntry) (cmax : Int) (q1 q2 : Qp) :
    idxCmpOwn (GF := GF) γ (q1 + q2) L cmax ⊢ idxCmpOwn γ q1 L cmax ∗ idxCmpOwn γ q2 L cmax := by
  unfold idxCmpOwn
  iintro ⟨%cc, %P, H, %Hp⟩
  rw [Qp.half_add]
  icases (ghostVar_fractional (GF := GF) γ.cmp (cc, P)).fractional q1.half q2.half |>.1 $$ H
    with ⟨H1, H2⟩
  isplitl [H1]
  · iexists cc, P; iframe H1; ipureintro; exact Hp
  · iexists cc, P; iframe H2; ipureintro; exact Hp

theorem idxCmpOwn_combine (γ : IdxNames) (L : List IdxEntry) (c1 c2 : Int) (q1 q2 : Qp) :
    idxCmpOwn (GF := GF) γ q1 L c1 ∗ idxCmpOwn γ q2 L c2 ⊢ idxCmpOwn γ (q1 + q2) L c1 := by
  unfold idxCmpOwn
  iintro ⟨⟨%cc1, %P1, H1, %Hp1⟩, ⟨%cc2, %P2, H2, -⟩⟩
  ihave %Ha := ghostVar_agree γ.cmp _ _ _ _ $$ H1 H2
  cases Ha
  iexists cc1, P1
  rw [Qp.half_add]
  isplitl [H1 H2]
  · iapply (ghostVar_fractional (GF := GF) γ.cmp (cc1, P1)).fractional q1.half q2.half |>.2
    iframe H1 H2
  ipureintro; exact Hp1

/-- A key's index of any events is well formed (its fold from `kiEmpty`). -/
theorem kiOfKey_KiWf_inv (evs : List Ev) (k : GoString) : KiWf (kiOfKey evs k) := by
  unfold kiOfKey
  generalize evs.filter (fun ev => decide (ev.key = k)) = es
  suffices h : ∀ (es : List Ev) (ki : KeyIndex), KiWf ki → KiWf (es.foldl kiApply ki) from
    h es kiEmpty KiWf.kiEmpty
  intro es
  induction es with
  | nil => intro ki h; exact h
  | cons e es ih => intro ki h; exact ih _ (kiApply_wf h e)

/-- A compacted key index has a generation if it had one. -/
theorem kiCompact_gens_ne (c : w64) (ki : KeyIndex) (h : ki.gens ≠ []) :
    (kiCompact c ki).gens ≠ [] := by
  have hlt := compactGenIdx_lt c ki.gens h
  unfold kiCompact
  simp only
  intro he
  have := congrArg List.length he
  rw [List.length_drop, List.length_set] at this
  simp at this
  omega

/-- The writer's log is bounded. -/
theorem IdxWf.logB {ilog : Log} {pend : List Change} (h : IdxWf ilog pend) : LogB (ilog ++ [pend]) := by
  obtain ⟨-, hlen, hp, hcs⟩ := h
  refine ⟨by simp; omega, fun cs hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact hcs cs hc
  · rw [List.mem_singleton] at hc; rw [hc]; exact hp

/-- A key's index of the events is `isEmpty` exactly when it is the empty one. -/
theorem kiOfKey_isEmpty_iff (evs : List Ev) (k : GoString) :
    kiIsEmpty (kiOfKey evs k) = true ↔ kiOfKey evs k = kiEmpty := by
  constructor
  · intro h
    rcases KiHead.kiOfKey evs k with he | he
    · exact he
    · rw [(kiIsEmpty_false_of_head he).1] at h; cases h
  · intro h; rw [h]; rfl

/-- With no compaction (every level `-1`), the index is the uncompacted one, key by key. -/
theorem IdxCRep.get_neg (log : Log) (hb : LogB log) {idx : IndexM}
    (h : IdxCRep (-1) (evsOf log) idx) (k : GoString) :
    idxGet idx k = idxGet (indexOf (evsOf log)) k := by
  obtain ⟨c, h0, h1, h2⟩ := h.2 k
  have hc : c = -1 := by omega
  subst hc
  rw [h2]
  unfold kiCompactO
  rw [kiCompact_neg log hb k]
  by_cases he : kiIsEmpty (kiOfKey (evsOf log) k) = true
  · simp only [he, ↓reduceIte]
    exact ((idxGet_indexOf_eq_none_iff _ k).2 ((kiOfKey_isEmpty_iff _ k).1 he)).symm
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    have hne : kiOfKey (evsOf log) k ≠ kiEmpty := fun e => he ((kiOfKey_isEmpty_iff _ k).2 e)
    cases hg : idxGet (indexOf (evsOf log)) k with
    | none => exact absurd ((idxGet_indexOf_eq_none_iff _ k).1 hg) hne
    | some ki =>
      have := (indexOf_rep (evsOf log)).2 k
      rw [hg] at this
      simp only [Option.getD_some] at this
      rw [this]

/-- **A reader's answer under compaction** (pure): `reader_answer` through the lock's compacted
index, at a revision at or above every level. -/
theorem reader_answerC (log₀ ilog : Log) (pend : List Change) (L : List IdxEntry) (cmax : Int)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length)
    (hwf0 : IdxWf ilog pend) (hwf : LogWf' log₀) (hcs : ∀ cs ∈ log₀, cs.length < 2 ^ 63)
    (HLL : IdxCRep cmax (evsOf (ilog ++ [pend])) (idxOfEntries L))
    (k : GoString) (r : Nat) (hr : r < log₀.length) (hlen0 : log₀.length < 2 ^ 63) (hc : cmax ≤ r) :
    kiGet ((idxGet (idxOfEntries L) k).getD kiEmpty) (W64 r) =
      kiGet (kiOfKey (evsOf log₀) k) (W64 r) := by
  have hz : cmax ≤ sint.Z (W64 r) := by
    have : sint.Z (W64 r) = r := by word
    omega
  have := IdxCRep.kiAt (ilog ++ [pend]) hwf0.logB HLL (W64 r) hz k
  unfold kiAt at this
  rw [this]
  exact reader_answer log₀ ilog pend hcmp hcount (by have := hwf0.2.1; omega) hwf hcs k r hr

/-- **A reader's range answers under compaction** (pure): `rangeAnswers_entries` through the
lock's compacted index, at a revision at or above every level. -/
theorem rangeAnswers_entriesC (log₀ ilog : Log) (pend : List Change) (L : List IdxEntry) (cmax : Int)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length)
    (hwf0 : IdxWf ilog pend) (hwf : LogWf' log₀) (hcs : ∀ cs ∈ log₀, cs.length < 2 ^ 63)
    (HLL : IdxCRep cmax (evsOf (ilog ++ [pend])) (idxOfEntries L))
    (k e : GoString) (r : Nat) (hr : r < log₀.length) (hlen0 : log₀.length < 2 ^ 63) (hc : cmax ≤ r) :
    rangeAnswers log₀ false k e (W64 r) = entryAnswers (rangeEntries L k e) (W64 r) := by
  have hz : cmax ≤ sint.Z (W64 r) := by
    have : sint.Z (W64 r) = r := by word
    omega
  unfold rangeAnswers
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← reader_range log₀ ilog pend hcmp hcount (by have := hwf0.2.1; omega) hwf hcs k e r hr,
    ← IdxCRep.rangeAt (ilog ++ [pend]) hwf0.logB HLL (W64 r) hz, rangeAt_entries]

/-- The `RWMutex`'s resource at fraction `q` (see the module docstring): the tree holds the
events of `ilog ++ [pend]`, each key's index compacted at a level of its own, at most `cmax`, a
lower bound of the compaction revision (`IdxCRep`, `Compact.lean`; the compaction job compacts
key by key under the lock), below the length of a lower bound of the committed log (so below
every writer's next revision). -/
def idxLockInv (t : Loc) (γ : IdxNames) (q : Qp) : IProp GF :=
  iprop(∃ (ilog : Log) (pend : List Change) (L : List IdxEntry) (cmax : Int),
    "#Hhist" ∷ monoListLbOwn γ.hist (histShape ilog pend) ∗
    "Hnev" ∷ monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length ∗
    "Htree" ∷ ownTree t L q ∗
    "#Hcrev" ∷ crevLb γ cmax ∗
    "#Hcl" ∷ (∃ log₀ : Log, monoListLbOwn γ.log log₀ ∗ ⌜cmax < log₀.length⌝) ∗
    "%HL" ∷ ⌜IdxCRep cmax (evsOf (ilog ++ [pend])) (idxOfEntries L) ∧ -1 ≤ cmax⌝ ∗
    "%Hwf" ∷ ⌜IdxWf ilog pend⌝ ∗
    "Hcmp" ∷ idxCmpOwn γ q L cmax)

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
      icases idxCmpOwn_split γ L cmax q1 q2 $$ Hcmp with ⟨Hc1, Hc2⟩
      isplitl [Hn1 Ht1 Hc1]
      · iexists ilog, pend, L, cmax; simp only [named]; iframe Hn1 Ht1 Hc1; iframe #; ipureintro
        exact ⟨HL, Hwf⟩
      · iexists ilog, pend, L, cmax; simp only [named]; iframe Hn2 Ht2 Hc2; iframe #; ipureintro
        exact ⟨HL, Hwf⟩
    · iintro ⟨H1, H2⟩
      unfold idxLockInv
      icases H1 with ⟨%ilog1, %pend1, %L1, %cmax1, H1⟩
      icases H2 with ⟨%ilog2, %pend2, %L2, %cmax2, H2⟩
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      generalize hn1 : (evsOf (ilog1 ++ [pend1])).length = n1 at *
      generalize hn2 : (evsOf (ilog2 ++ [pend2])).length = n2 at *
      icases monoNatAuthOwn_agree γ.nev q1 q2 n1 n2 $$ Hnev1 Hnev2 with %Hn
      obtain ⟨-, Hn⟩ := Hn
      subst Hn
      icases ownTree_combine t L1 L2 q1 q2 $$ Htree1 Htree2 with ⟨%HL, Htree⟩
      subst HL
      iexists ilog1, pend1, L1, cmax1
      simp only [named]
      iframe Htree
      ihave Hcmp := idxCmpOwn_combine γ L1 cmax1 cmax2 q1 q2 $$ [Hcmp1 Hcmp2]
      · iframe Hcmp1 Hcmp2
      iframe Hcmp
      isplitl []
      · iexact Hhist1
      isplitl [Hnev1 Hnev2]
      · rw [hn1]; iapply (hnat n1).2; iframe
      isplitl []
      · iexact Hcrev1
      isplitl []
      · iexact Hcl1
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A tree index (persistent): its tree and logger, and the lock's guard (writers lock through
it). -/
def isTreeIndex (ti : Loc) (γ : IdxNames) : IProp GF :=
  iprop(∃ (t lg : Loc),
    "#Htree" ∷ ti.[treeIndex, go!"tree"] ↦□ t ∗
    "#Hlg" ∷ ti.[treeIndex, go!"lg"] ↦□ lg ∗
    "%Hlgnn" ∷ ⌜lg ≠ null⌝ ∗
    "#Hmu" ∷ sync.isRWMutexGuard (idxMuAddr ti) (idxLockInv t γ))

instance isTreeIndex_persistent (ti : Loc) (γ : IdxNames) : Persistent (isTreeIndex (GF := GF) ti γ) := by
  unfold isTreeIndex; infer_instance

/-- A reader's token: one of the `RWMutex`'s bounded reader slots (`RLock` needs one). -/
def idxReader (ti : Loc) (γ : IdxNames) : IProp GF :=
  iprop(∃ t : Loc, ti.[treeIndex, go!"tree"] ↦□ t ∗ sync.ownRWMutex (idxMuAddr ti) (idxLockInv t γ))

/-- The committed log's authority at fraction `q`: half is the writer's (`idxWriter`), half
is kept elsewhere (the store's `s.revMu`), so that a reader of the committed log there finds
every certificate below it (`idxLogAuth_cert_prefix`). -/
abbrev idxLogAuth (γ : IdxNames) (q : Qp) (log : Log) : IProp GF := monoListAuthOwn γ.log q log

/-- The writer's handle: the history's authority (`ilog` committed, `pend` put so far), a
lower bound of the event count at its last write, and half the committed log's authority. -/
def idxWriter (γ : IdxNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (histShape ilog pend) ∗
    monoNatLbOwn γ.nev (evsOf (ilog ++ [pend])).length ∗ ⌜IdxWf ilog pend⌝ ∗
    idxLogAuth γ (1 : Qp).half ilog)

theorem idxWriter_wf (γ : IdxNames) (ilog : Log) (pend : List Change) :
    idxWriter (GF := GF) γ ilog pend ⊢ ⌜IdxWf ilog pend⌝ := by
  unfold idxWriter; iintro ⟨-, -, %H, -⟩; ipureintro; exact H

/-- The writer's handle once **sealed**: the pending revision `pend` (not empty) is final, its
commit marker already in the history (so the history's lower bound `histOf (ilog ++ [pend])`
is persistent before the commit, which needs `s.revMu`'s half of the committed log); the
committed log's authority is still at `ilog` until the commit (`idxWriterSealed_commit`). The
watchable store seals before it notifies the watchers of the revision. -/
def idxWriterSealed (γ : IdxNames) (ilog : Log) (pend : List Change) : IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 (histOf (ilog ++ [pend])) ∗
    monoNatLbOwn γ.nev (evsOf (ilog ++ [pend])).length ∗ ⌜IdxWf ilog pend ∧ pend ≠ []⌝ ∗
    idxLogAuth γ (1 : Qp).half ilog)

/-- The writer's handle, sealed or not. -/
def idxWriterB (γ : IdxNames) (ilog : Log) (pend : List Change) (sealed : Bool) : IProp GF :=
  if sealed then idxWriterSealed γ ilog pend else idxWriter γ ilog pend

@[simp] theorem idxWriterB_false (γ : IdxNames) (ilog : Log) (pend : List Change) :
    idxWriterB (GF := GF) γ ilog pend false = idxWriter γ ilog pend := rfl

@[simp] theorem idxWriterB_true (γ : IdxNames) (ilog : Log) (pend : List Change) :
    idxWriterB (GF := GF) γ ilog pend true = idxWriterSealed γ ilog pend := rfl

/-- **Seal** (a ghost step of the writer alone): the pending revision's commit marker, and the
persistent lower bound of the history with the revision committed. -/
theorem idxWriter_seal (γ : IdxNames) (ilog : Log) (pend : List Change) (hne : pend ≠ []) :
    idxWriter (GF := GF) γ ilog pend ==∗
      idxWriterSealed γ ilog pend ∗ monoListLbOwn γ.hist (histOf (ilog ++ [pend])) := by
  unfold idxWriter idxWriterSealed
  iintro ⟨Hauth, #Hnev, %Hwf, Hlauth⟩
  imod monoListAuthOwn_update_app [HistItem.commit] $$ Hauth with ⟨Hauth, #Hlb⟩
  imodintro
  rw [histShape_seal]
  iframe Hauth Hlauth Hlb Hnev
  ipureintro; exact ⟨Hwf, hne⟩

/-- A sealed writer's pending revision is not empty. -/
theorem idxWriterB_ne (γ : IdxNames) (ilog : Log) (pend : List Change) (b : Bool) :
    idxWriterB (GF := GF) γ ilog pend b ⊢ idxWriterB γ ilog pend b ∗ ⌜b = true → pend ≠ []⌝ := by
  cases b
  · iintro H; iframe H; ipureintro; intro h; cases h
  · simp only [idxWriterB_true]
    unfold idxWriterSealed
    iintro ⟨Ha, Hn, %Hw, Hl⟩
    iframe Ha Hn Hl
    ipureintro; exact ⟨Hw, fun _ => Hw.2⟩

/-- An empty pending revision is never sealed. -/
theorem idxWriterB_nil (γ : IdxNames) (ilog : Log) (b : Bool) :
    idxWriterB (GF := GF) γ ilog [] b ⊢ idxWriter γ ilog [] := by
  cases b
  · exact .rfl
  · simp only [idxWriterB_true]
    unfold idxWriterSealed
    iintro ⟨-, -, %Hw, -⟩
    exact absurd rfl Hw.2

theorem idxWriterB_wf (γ : IdxNames) (ilog : Log) (pend : List Change) (b : Bool) :
    idxWriterB (GF := GF) γ ilog pend b ⊢ ⌜IdxWf ilog pend⌝ := by
  cases b
  · exact idxWriter_wf γ ilog pend
  · simp only [idxWriterB_true]
    unfold idxWriterSealed
    iintro ⟨-, -, %Hw, -⟩
    ipureintro; exact Hw.1

/-- The certificate of a committed log `log`: its history is a prefix of the index's, the
index had all its events, and `log` is a prefix of the committed log (so two certificates
are of logs in prefix order: `idxCert_prefix`). -/
def idxCert (γ : IdxNames) (log : Log) : IProp GF :=
  iprop(monoListLbOwn γ.hist (histOf log) ∗ monoNatLbOwn γ.nev (evsOf log).length ∗
    ⌜LogWf' log ∧ log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63⌝ ∗
    monoListLbOwn γ.log log)

instance idxCert_persistent (γ : IdxNames) (log : Log) : Persistent (idxCert (GF := GF) γ log) := by
  unfold idxCert; infer_instance

/-- **Two certificates are of logs in prefix order.** -/
theorem idxCert_prefix (γ : IdxNames) (log log' : Log) :
    idxCert (GF := GF) γ log ∗ idxCert γ log' ⊢ ⌜log <+: log' ∨ log' <+: log⌝ := by
  unfold idxCert
  iintro ⟨⟨-, -, -, Hl⟩, ⟨-, -, -, Hl'⟩⟩
  iapply mono_list_lb_valid γ.log log log' $$ Hl Hl'

/-- **Two certificates of logs of one length are of one log.** -/
theorem idxCert_agree_len (γ : IdxNames) (log log' : Log) :
    idxCert (GF := GF) γ log ∗ idxCert γ log' ⊢ ⌜log.length = log'.length → log = log'⌝ := by
  refine (idxCert_prefix γ log log').trans (pure_mono fun h hlen => ?_)
  rcases h with h | h
  · exact h.eq_of_length hlen
  · exact (h.eq_of_length hlen.symm).symm

/-- The committed log (any part of its authority) extends every certificate's. -/
theorem idxLogAuth_cert_prefix (γ : IdxNames) (q : Qp) (ilog log : Log) :
    idxLogAuth (GF := GF) γ q ilog ∗ idxCert γ log ⊢ ⌜log <+: ilog⌝ := by
  unfold idxCert
  iintro ⟨Ha, ⟨-, -, -, Hl⟩⟩
  ihave %h := mono_list_auth_lb_valid γ.log q ilog log $$ Ha Hl
  ipureintro; exact h.2

/-- The writer's committed log extends every certificate's. -/
theorem idxWriter_cert_prefix (γ : IdxNames) (ilog : Log) (pend : List Change) (log : Log) :
    idxWriter (GF := GF) γ ilog pend ∗ idxCert γ log ⊢ ⌜log <+: ilog⌝ := by
  unfold idxWriter
  iintro ⟨⟨-, -, -, Ha⟩, Hc⟩
  iapply idxLogAuth_cert_prefix γ _ ilog log $$ [$Ha $Hc]

/-- The certificate of the empty log (nothing committed). -/
theorem idxCert_nil (γ : IdxNames) : ⊢ |==> idxCert (GF := GF) γ [] := by
  unfold idxCert
  imod monoListLbOwn_nil (GF := GF) (A := HistItem) γ.hist with #H1
  imod monoNatLbOwn_0 (GF := GF) γ.nev with #H2
  imod monoListLbOwn_nil (GF := GF) (A := List Change) γ.log with #H3
  imodintro
  have h1 : histOf [] = ([] : List HistItem) := rfl
  have h2 : (evsOf []).length = 0 := rfl
  rw [h1, h2]
  iframe H1 H2 H3
  ipureintro
  exact ⟨⟨fun h => absurd rfl h, fun r cs i k hr _ => by simp at hr⟩, by simp, by simp⟩

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
    (hlen : ilog.length + 2 < 2 ^ 63) :
    ⊢ idxWriter (GF := GF) γ ilog pend -∗ idxLogAuth γ (1 : Qp).half ilog ==∗
      idxWriter γ (ilog ++ [pend]) [] ∗ idxLogAuth γ (1 : Qp).half (ilog ++ [pend]) ∗
        idxCert γ (ilog ++ [pend]) := by
  have hhalves := fun (l : Log) =>
    (monoListAuthOwn_fractional (GF := GF) γ.log l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hhalves
  unfold idxWriter idxCert idxLogAuth
  iintro ⟨Hauth, #Hnev, %Hwf, Hlauth⟩ Hlother
  obtain ⟨hwf, hl, hp, hcs⟩ := Hwf
  ihave Hlauth : monoListAuthOwn γ.log 1 ilog $$ [Hlauth Hlother]
  · iapply (hhalves ilog).2; iframe Hlauth Hlother
  imod monoListAuthOwn_update_app [HistItem.commit] $$ Hauth with ⟨Hauth, #Hlb⟩
  imod monoListAuthOwn_update_app [pend] $$ Hlauth with ⟨Hlauth, #Hllb⟩
  icases (hhalves (ilog ++ [pend])).1 $$ Hlauth with ⟨Hlauth, Hlother⟩
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
  isplitl [Hauth Hlauth]
  · iframe Hauth Hlauth
    isplitl []
    · iexact Hnev
    ipureintro
    refine ⟨hwf', by simp; omega, by simp, hcs'⟩
  iframe Hlother
  · isplitl []
    · iexact Hlb
    isplitl []
    · iexact Hnev
    iframe Hllb
    ipureintro
    exact ⟨hwf, by simp; omega, hcs'⟩

/-- **Commit** of a sealed writer: the committed log's authority catches up with the history. -/
theorem idxWriterSealed_commit (γ : IdxNames) (ilog : Log) (pend : List Change)
    (hlen : ilog.length + 2 < 2 ^ 63) :
    ⊢ idxWriterSealed (GF := GF) γ ilog pend -∗ idxLogAuth γ (1 : Qp).half ilog ==∗
      idxWriter γ (ilog ++ [pend]) [] ∗ idxLogAuth γ (1 : Qp).half (ilog ++ [pend]) ∗
        idxCert γ (ilog ++ [pend]) := by
  have hhalves := fun (l : Log) =>
    (monoListAuthOwn_fractional (GF := GF) γ.log l).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hhalves
  unfold idxWriterSealed idxWriter idxCert idxLogAuth
  iintro ⟨Hauth, #Hnev, %Hwf, Hlauth⟩ Hlother
  obtain ⟨⟨hwf, hl, hp, hcs⟩, -⟩ := Hwf
  ihave Hlauth : monoListAuthOwn γ.log 1 ilog $$ [Hlauth Hlother]
  · iapply (hhalves ilog).2; iframe Hlauth Hlother
  ihave #Hlb := monoListLbOwn_get γ.hist 1 _ $$ Hauth
  imod monoListAuthOwn_update_app [pend] $$ Hlauth with ⟨Hlauth, #Hllb⟩
  icases (hhalves (ilog ++ [pend])).1 $$ Hlauth with ⟨Hlauth, Hlother⟩
  imodintro
  have hwf' : LogWf' (ilog ++ [pend] ++ [[]]) := hwf.append_nil (by simp)
  have hcs' : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63 := by
    intro cs hcs'
    rcases List.mem_append.1 hcs' with h | h
    · exact hcs cs h
    · rw [List.mem_singleton] at h; rw [h]; exact hp
  have hhist : histShape (ilog ++ [pend]) [] = histOf (ilog ++ [pend]) := by
    rw [← histShape_seal, histShape_commit]
  have hevs : evsOf (ilog ++ [pend] ++ [[]]) = evsOf (ilog ++ [pend]) := by
    rw [evsOf_append (ilog ++ [pend]) []]; simp [evsOfRev]
  rw [hhist, hevs]
  isplitl [Hauth Hlauth]
  · iframe Hauth Hlauth
    isplitl []
    · iexact Hnev
    ipureintro
    refine ⟨hwf', by simp; omega, by simp, hcs'⟩
  iframe Hlother
  · isplitl []
    · iexact Hlb
    isplitl []
    · iexact Hnev
    iframe Hllb
    ipureintro
    exact ⟨hwf, by simp; omega, hcs'⟩

/-- **Commit** of a writer, sealed or not. -/
theorem idxWriterB_commit (γ : IdxNames) (ilog : Log) (pend : List Change) (b : Bool)
    (hlen : ilog.length + 2 < 2 ^ 63) :
    ⊢ idxWriterB (GF := GF) γ ilog pend b -∗ idxLogAuth γ (1 : Qp).half ilog ==∗
      idxWriter γ (ilog ++ [pend]) [] ∗ idxLogAuth γ (1 : Qp).half (ilog ++ [pend]) ∗
        idxCert γ (ilog ++ [pend]) := by
  cases b
  · exact idxWriter_commit γ ilog pend hlen
  · exact idxWriterSealed_commit γ ilog pend hlen


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
    icases Hkn with ⟨#Hclb, #Hcnt, %Hcwf, -⟩
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
    icases Hkn with ⟨Hauth, #Hwlb, %Hwwf, Hlauth⟩
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
    iframe Hauth Hlauth
    iframe #
    ipureintro; exact Hwwf

/-- With the writer's handle, the lock's events are the writer's (`writer_events`). -/
theorem idxKnows_writer_events (γ : IdxNames) (kn : IdxKnow) (ilog : Log) (pend : List Change)
    (q : Qp) :
    ⊢ idxKnows (GF := GF) γ kn -∗ monoListLbOwn γ.hist (histShape ilog pend) -∗
      monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length -∗
      ⌜∀ ilog' pend', kn = .writer ilog' pend' →
        evsOf (ilog ++ [pend]) = evsOf (ilog' ++ [pend'])⌝ ∗
      idxKnows γ kn ∗ monoNatAuthOwn γ.nev q (evsOf (ilog ++ [pend])).length := by
  cases kn with
  | cert log =>
    iintro Hkn _ Hnev
    iframe Hkn Hnev
    ipureintro; intro _ _ h; cases h
  | writer ilog' pend' =>
    rw [idxKnows_writer]
    iintro Hkn #Hlb Hnev
    iunfold idxWriter at Hkn
    icases Hkn with ⟨Hauth, #Hwlb, %Hwwf, Hlauth⟩
    ihave %Hpre := mono_list_auth_lb_valid γ.hist 1 _ _ $$ Hauth Hlb
    ihave %Hcnt := monoNatLbOwn_valid γ.nev q _ _ $$ Hnev Hwlb
    iframe Hnev
    isplitl []
    · ipureintro
      intro a b h
      injection h with h1 h2
      subst h1 h2
      exact writer_events ilog' ilog pend' pend Hpre.2 Hcnt.2
    iunfold idxWriter
    iframe Hauth Hlauth
    iframe #
    ipureintro; exact Hwwf

end reprs2

end mvcc
end EtcdGrove
end Perennial
