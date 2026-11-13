/-
The public reader cursor triples' (U6h, `notes/bbolt-proof-plan.md`) frame: a reader's
`boltTx`/`boltCur` opened into the internal specs' resources (`rdTxK`, the cursor's bucket `rBktP`,
its stack, `rCurPos`) with the bucket's facts (`rBktOK`, its entries the cursor's `es`, plain), and
closed at a new position (`rdCur_open`); a reader's key/value result as the public `curAt`
(`rKV_curAt`, `rCurKV_curAt`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Pub
public import Proof.go_etcd_io.bbolt.Read.GetFacts
public import Proof.go_etcd_io.bbolt.Read.CurPos
public import Spec.go_etcd_io.bbolt.Api
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pubR
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance rBktP_discard_persistent_pubR (v : View) (tx b : Loc) (bv : List w8) (ibp pp : Loc) :
    Persistent (rBktP (GF := GF) v tx b DFrac.discard bv ibp pp) := by
  unfold rBktP locOwn; infer_instance

/-- **The facts of a reader cursor's bucket**: well-formed (`rBktOK`), its entries the cursor's
`es`, plain (a top-level bucket holds no nested bucket). -/
def rdCurFacts (v : View) (bv : List w8) (es : List BoltEnt) : Prop :=
  viewWF v ∧ rBktOK v bv ∧ es = bktEntries v.pages bv ∧
    ∀ pg ∈ bktLeaves v.pages bv, ∀ i < pageCount pg, leafFlags pg i % 2 = 0

/-- **A reader's transaction and cursor, opened** (the public reader cursor triples' frame): the
reader's `rdTxK`, the cursor's bucket and stack at `rCurPos … pos`, the registration and view
(for `curAt`); closed at any new position of the same bucket. -/
theorem rdCur_open (B : BNs) (N : Namespace) (tx c : Loc) (q : Qp) (T : TxView)
    (es : List BoltEnt) (pos : Option Nat) (hro : T.rw = false) :
    boltTxDef (GF := GF) B N tx q T ∗ boltCurDef B tx c T es pos ⊢
    ∃ (K : BC) (v : View) (r : TxReg) (b : Loc) (stk : GoSlice) (els : List elemRef)
      (bv : List w8) (ibp pp : Loc),
      rdTxK K tx .loan q T v ∗ rBktP v tx b DFrac.discard bv ibp pp ∗ c ↦ Cursor.mk b stk ∗
      stk ↦* els ∗ ownSliceCap elemRef stk (DFrac.own 1) ∗ reg tx B r ∗ viewOf r v ∗
      ⌜r.rw = false ∧ rdCurFacts v bv es ∧ rCurPos v bv pp els pos⌝ ∗
      (∀ (stk' : GoSlice) (els' : List elemRef) (pos' : Option Nat),
        rdTxK K tx .loan q T v -∗ c ↦ Cursor.mk b stk' -∗ stk' ↦* els' -∗
        ownSliceCap elemRef stk' (DFrac.own 1) -∗ ⌜rCurPos v bv pp els' pos'⌝ -∗
        boltTxDef B N tx q T ∗ boltCurDef B tx c T es pos') := by
  iintro ⟨Ht, Hc⟩
  ihave Ht := (boltTx_rdTx B N tx q T hro).1 $$ Ht
  icases Ht with ⟨%db, Hr, #Hdb⟩
  ihave Hr := (rdTx_rdTxK B N tx .loan q T).1 $$ Hr
  icases Hr with ⟨%K, %v, %HK, Hk⟩
  unfold boltCurDef
  icases Hc with ⟨%r, %b, %n, %g, %stk, %els, %v', #Hreg, Hh, Hc, Hs, Hcap, #Hvo', %Hes, Hbr⟩
  icases (persistent_entails_left (rdTxK_view _ tx .loan q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  icases rdTxK_cur_acc _ tx .loan q T v $$ Hk with ⟨%r0, -, #Hreg0, #Hvo, %Hro, Hst, Hkb⟩
  ihave Hk := Hkb $$ Hst
  obtain ⟨hKB, hKN⟩ := HK
  rw [hKB]
  iunfold reg at Hreg Hreg0
  icombine Hreg Hreg0 gives %hr
  obtain ⟨-, rfl⟩ := hr
  simp only [Hro, Bool.false_eq_true, ite_false]
  iunfold handleFrag at Hh
  isimp only [Hro, Bool.false_eq_true, ↓reduceIte] at Hh
  icases Hh with %Hg
  icases Hbr with ⟨%bv, %ibp, %pp, #Hrb, %Hbe, %Hpos⟩
  ihave %Hvv := viewOfRdAgree_holds r v v' Hro $$ [Hvo Hvo']
  · iframe #
  subst Hvv
  obtain ⟨hT, hvwf⟩ := Hvw
  obtain ⟨m, hm⟩ : ∃ m, v.data !! n = some m := by
    cases h : v.data !! n with
    | none => exact absurd h (rd_root_lookup_some v hvwf n bv Hbe)
    | some m => exact ⟨m, rfl⟩
  obtain ⟨hn, -, -⟩ := rd_bkt_data v hvwf n bv m Hbe hm
  have hes : es = bktEntries v.pages bv := by
    rw [Hes.1, hT, ← rd_bktEnts v hvwf n bv m Hbe hm]
    show bktEnts ((v.data !! n).getD ∅) = bktEnts m
    rw [hm]; rfl
  iexists K, v, r, b, stk, els, bv, ibp, pp
  unfold reg
  iframe; iframe #
  isplitr
  · ipureintro
    exact ⟨Hro, ⟨hvwf, rBktOK_of v hvwf bv (Or.inr ⟨n, hn⟩), hes,
      fun pg hpg i hi => rd_top_plain v hvwf n bv hn pg hpg i hi⟩, Hpos⟩
  iintro %stk' %els' %pos' Hk Hc Hs Hcap %Hpos'
  isplitl [Hk]
  · iapply (boltTx_rdTx B N tx q T hro).2
    iexists db; iframe #
    iapply (rdTx_rdTxK B N tx .loan q T).2
    iexists K, v; iframe
    ipureintro; exact ⟨hKB, hKN⟩
  iexists r, b, n, g, stk', els', v
  unfold handleFrag
  simp only [Hro, Bool.false_eq_true, ite_false]
  iframe; iframe #
  isplitr
  · ipureintro; exact Hg
  isplitr
  · ipureintro; exact Hes
  ipureintro; exact ⟨Hbe, Hpos'⟩

/-- **A reader's entry as the public `curAt`**: the entry at a cursor position `i` (the leaf
element `(pg, idx)` of `rEnts`), read by `keyValue`, is the bucket's entry `i` (its key non-nil,
key and value live while `tx` is). -/
theorem rKV_curAt (γ : BoltName) (tx : Loc) (r : TxReg) (v : View) (bv : List w8)
    (es : List BoltEnt) (i : Nat) (pg : List w8) (idx : Nat) (k vl : GoSlice) (fl : w32)
    (hes : es = bktEntries v.pages bv) (hget : (rEnts v bv)[i]? = some (pg, idx)) :
    reg tx (bnsOf γ.gs) r ∗ viewOf r v ∗ rKV (GF := GF) v pg idx k vl fl ⊢
      curAt tx γ es i k vl ∗ ⌜fl = (leafElem pg idx).flags'⌝ := by
  have hidx : idx < pageCount pg := by
    unfold rEnts at hget
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
    have hm : (pg, idx) ∈ (bktLeaves v.pages bv).flatMap lEnts := heq ▸ List.getElem_mem hlt
    obtain ⟨pg', -, hm'⟩ := List.mem_flatMap.mp hm
    unfold lEnts at hm'
    obtain ⟨j, hj, hje⟩ := List.mem_map.mp hm'
    simp only [Prod.mk.injEq] at hje
    obtain ⟨rfl, rfl⟩ := hje
    exact List.mem_range.mp hj
  have hes' : es[i]? = some (leafKey pg idx, leafValue pg idx) := by
    rw [hes]; exact rEnts_get v bv i pg idx hget
  unfold curAt txBytes txBytesDef rKV
  rw [hes']; simp only [hidx, ite_true]
  iintro ⟨#Hreg, #Hvo, ⟨%ks, %vs, ⟨%hk, %hks, %hvs, %hfl⟩, #Hks, #Hvs⟩⟩
  isplitl
  · isplitr
    · ipureintro; exact hk
    isplitr
    · cases ks with
      | stale => exact absurd rfl hks
      | own d => unfold srcOwn; ileft; iexact Hks
      | view =>
        unfold srcOwn
        icases Hks with %Hin
        iright; iexists r, v; iframe #; ipureintro; exact Hin
    · cases vs with
      | stale => exact absurd rfl hvs
      | own d => unfold srcOwn; ileft; iexact Hvs
      | view =>
        unfold srcOwn
        icases Hvs with %Hin
        iright; iexists r, v; iframe #; ipureintro; exact Hin
  · ipureintro; exact hfl

/-- An entry of `rEnts` is an entry of one of the bucket's leaves. -/
theorem rEnts_mem (v : View) (bv : List w8) (i : Nat) (pg : List w8) (idx : Nat)
    (hget : (rEnts v bv)[i]? = some (pg, idx)) :
    pg ∈ bktLeaves v.pages bv ∧ idx < pageCount pg := by
  unfold rEnts at hget
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
  have hm : (pg, idx) ∈ (bktLeaves v.pages bv).flatMap lEnts := heq ▸ List.getElem_mem hlt
  obtain ⟨pg', hpg', hm'⟩ := List.mem_flatMap.mp hm
  unfold lEnts at hm'
  obtain ⟨j, hj, hje⟩ := List.mem_map.mp hm'
  simp only [Prod.mk.injEq] at hje
  obtain ⟨rfl, rfl⟩ := hje
  exact ⟨hpg', List.mem_range.mp hj⟩

/-- `fl &&& 1 = 0` is the flags' low bit clear. -/
theorem w32_and_one (f : w32) : f &&& W32 1 = W32 0 ↔ f.toNat % 2 = 0 := by
  rw [BitVec.toNat_eq]; simp [BitVec.toNat_and, Nat.and_one_is_mod]

/-- **A reader cursor's move result as the public `curAt`** (`rCurKV` at `s`): the entry `s` of
the cursor's `es` (nil, nil past the end), plain flags, and where the stack is. -/
theorem rCurKV_pub (γ : BoltName) (tx : Loc) (r : TxReg) (v : View) (bv : List w8) (pp : Loc)
    (els : List elemRef) (s : Nat) (k vl : GoSlice) (fl : w32) (es : List BoltEnt)
    (hf : rdCurFacts v bv es) :
    reg tx (bnsOf γ.gs) r ∗ viewOf r v ∗ rCurKV (GF := GF) v bv pp els s k vl fl ⊢
      curAt tx γ es s k vl ∗ ⌜fl &&& W32 1 = W32 0 ∧ (rPosAt v bv pp els s (s + 1) ∨
        (s = (rEnts v bv).length ∧ ∃ i, rPosAt v bv pp els i s))⌝ := by
  obtain ⟨-, -, hes, hplain⟩ := hf
  unfold rCurKV
  iintro ⟨#Hreg, #Hvo, (⟨%pg, %idx, ⟨%Hp, -, %Hget⟩, Hkv⟩ | %H)⟩
  · icases rKV_curAt γ tx r v bv es s pg idx k vl fl hes Hget $$ [Hkv] with ⟨Hc, %Hfl⟩
    · iframe #; iexact Hkv
    iframe
    ipureintro
    obtain ⟨hpg, hidx⟩ := rEnts_mem v bv s pg idx Hget
    refine ⟨(w32_and_one fl).2 ?_, Or.inl Hp⟩
    have := hplain pg hpg idx hidx
    unfold leafFlags at this; rw [Hfl]; exact this
  · obtain ⟨hs, rfl, rfl, rfl, i, hi⟩ := H
    have hnone : es[s]? = none := by
      rw [hes, List.getElem?_eq_none_iff, rEnts_length, hs]; exact Nat.le_refl _
    unfold curAt
    rw [hnone]
    ipureintro
    exact ⟨⟨rfl, rfl⟩, by decide, Or.inr ⟨hs, i, hi⟩⟩

/-- Past the end, `curAt` is nil, nil at every position. -/
theorem curAt_past (γ : BoltName) (tx : Loc) (es : List BoltEnt) (i j : Nat) (k vl : GoSlice)
    (hi : es.length ≤ i) (hj : es.length ≤ j) :
    curAt (GF := GF) tx γ es i k vl ⊢ curAt tx γ es j k vl := by
  unfold curAt
  rw [List.getElem?_eq_none hi, List.getElem?_eq_none hj]

end pubR

end bbolt
end EtcdGrove
end Perennial
