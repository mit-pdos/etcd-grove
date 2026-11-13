/-
The public writer cursor triples' (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a fraction")
frame: a writer's `boltTx`/`boltCur` at a fraction `q` opened into the internal writer cursor specs'
resources (`wtxWQ`, the cursor's stack with its persistent part, `wCurAt`) with the bucket's facts
(`wCurCtx`, its entries the cursor's `es`), and closed at a new position (`wrCur_open`); a move's
result as the public `curAt` (`wEntKV_curAt`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCur
public import Proof.go_etcd_io.bbolt.Read.PubWBkt
public import Proof.go_etcd_io.bbolt.Read.TxBytes
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

section pubWCur
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The writer's heap facts (`heapOK`), out of `wtxWQ`. -/
theorem wtxWQ_heapOK (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ ⌜heapOK (GF := GF) tx X⌝ := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hrest⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own q) X $$ Hh
  isplitl
  · iframe; ipureintro; exact Hr
  · ipureintro; exact Hok

/-- **The writer's `tx.db` field** (non-nil: the database's) out of `wtxWQ`, and back. -/
theorem wtxWQ_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} K.db ∗ ⌜K.db ≠ null⌝ ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} K.db -∗ wtxWQ K tx r m q X) := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨#Hpkg, #Hcore, %Hc, #Hreg, Hheap, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hvc, Hmap⟩
  have hdb : r.db = K.db := Hc.1
  rw [hdb]
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, %Ht0, -⟩
  iframe Hdb
  isplitr
  · ipureintro; exact Ht0.2.1
  iintro Hdb
  rw [← hdb]
  iframe; iframe #
  ipureintro; exact ⟨rfl, Hc.2⟩

/-- **A writer's transaction and cursor at `q`, opened** (the public writer cursor triples' frame):
the writer's `wtxWQ`, the cursor's stack at `wCurAt … pos` with its persistent part, the bucket's
facts, the registration and view (for `curAt`); closed at any new position of the same bucket. `hD1`
is `gensOK`'s third clause (maintainer 14); the cursor's facts are `wtxFrac`'s (`wrCurFacts`). -/
theorem wrCur_open (B : BNs) (N : Namespace) (tx c : Loc) (q : Qp) (T : TxView)
    (es : List BoltEnt) (pos : Option Nat) (hrw : T.rw = true)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b)
 :
    boltTxDef (GF := GF) B N tx q T ∗ boltCurDef B tx c T es pos ⊢
    ∃ (K : BC) (r : TxReg) (X : WX) (n : GoString) (b : Loc) (stk : GoSlice)
      (els : List elemRef) (nl : Loc → Option (Loc × Nat)) (ipg : List w8),
      wtxWQ K tx r true q X ∗ c ↦ Cursor.mk b stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ wStkOwn r nl X.v (wRoot X.v T n) ipg els ∗
      reg tx B r ∗ viewOf r X.v ∗
      ⌜wCurCtx X n b (wRoot X.v T n) ∧ es = wEs X n ∧ b ≠ X.rl ∧
        wCurAt nl X.v es b (wRoot X.v T n) ipg els pos⌝ ∗
      (∀ (stk' : GoSlice) (els' : List elemRef) (nl' : Loc → Option (Loc × Nat))
          (ipg' : List w8) (pos' : Option Nat),
        wtxWQ K tx r true q X -∗ c ↦ Cursor.mk b stk' -∗ stk' ↦* els' -∗
        ownSliceCap elemRef stk' (DFrac.own 1) -∗
        wStkOwn r nl' X.v (wRoot X.v T n) ipg' els' -∗
        ⌜wCurAt nl' X.v es b (wRoot X.v T n) ipg' els' pos'⌝ -∗
        boltTxDef B N tx q T ∗ boltCurDef B tx c T es pos') := by
  iintro ⟨Ht, Hc⟩
  ihave Ht := (boltTxDef_wtxWQ B N tx q T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %cv, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur, hbase, hgens, hwr, hwc⟩ := Hf
  unfold boltCurDef
  have hfp : ∀ (r' : TxReg) (b : Loc) (n : GoString) (g : Nat),
      Persistent (handleFrag (GF := GF) r' b n g) := fun r' b n g => by
    unfold handleFrag; split <;> infer_instance
  have hnp : ∀ (r' : TxReg) (nl : Loc → Option (Loc × Nat)) (e : elemRef),
      Persistent (nodeLoc (GF := GF) r' nl e) := fun r' nl e => by
    unfold nodeLoc; split <;> infer_instance
  icases Hc with ⟨%r', %b, %n, %g, %stk, %els, %v', #Hreg', #Hh, Hc, Hs, Hcap, #Hvo', %Hes, Hbr⟩
  obtain ⟨hes, hg⟩ := Hes
  subst hg
  ihave #Hreg'' : reg (GF := GF) tx K.B r' $$ []
  · rw [hKB]; iexact Hreg'
  icases wtxWQ_handle K tx r r' true q X b n (T.gen n) $$ [Hw] with ⟨Hw, %Hhd⟩
  · iframe; iframe #
  obtain ⟨hrr, hhd⟩ := Hhd
  subst hrr
  icases wtxWQ_reg_rw K tx r' true q X $$ Hw with ⟨Hw, -, %Hrw⟩
  ihave %Hvv := viewOf_agree r' X.v v' $$ [Hvo Hvo']
  · iframe #
  subst Hvv
  isimp only [Hrw, ↓reduceIte] at Hbr
  icases Hbr with ⟨%nl, %ipg, #Hnl, #Hinl, %Hpos⟩
  have hbl := hD1 X hgens b n hhd
  have hnlc := hwc.1
  have hroot := hwc.2.1
  have hbr : b ≠ X.rl := by
    intro e
    unfold bktLoc at hbl
    cases hR : X.t.bs !! X.rl with
    | none => rw [hR] at hbl; cases hbl
    | some R =>
      rw [hR] at hbl
      simp only [Option.bind_some] at hbl
      exact hwr.2.2 R hR n b hbl e
  have hesX : es = wEs X n := by rw [hes, hcur]; rfl
  iexists K, r', X, n, b, stk, els, nl, ipg
  iframe Hw Hc Hs Hcap
  isplitr
  · unfold wStkOwn; iframe #
  rw [← hKB]
  iframe #
  isplitr
  · ipureintro
    exact ⟨⟨hok, hbl, hnlc, hroot n b hbl, hbr⟩, hesX, hbr, Hpos⟩
  iintro %stk' %els' %nl' %ipg' %pos' Hw Hc Hs Hcap #Hown %Hpos'
  isplitl [Hw Hv Hst]
  · iapply (boltTxDef_wtxWQ K.B N tx q T hrw).2
    iexists K, r', cv, X
    iframe; iframe #
    ipureintro; exact ⟨⟨rfl, hKN, hTc⟩, hok, hcur, hbase, hgens, hwr, hwc⟩
  iexists r', b, n, (T.gen n), stk', els', X.v
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨hes, rfl⟩
  isimp only [Hrw, ↓reduceIte]
  iexists nl', ipg'
  iunfold wStkOwn at Hown
  icases Hown with ⟨#H1, #H2⟩
  iframe #
  ipureintro; exact Hpos'

/-- **A writer cursor move's result as the public `curAt`**: the entry at `i` with its bytes'
sources (persistent bytes, or the writer's view) is `curAt`'s. -/
theorem wEntKV_curAt (γ : BoltName) (tx : Loc) (r : TxReg) (X : WX) (es : List BoltEnt) (i : Nat)
    (k vl : GoSlice) (fl : w32) :
    reg tx (bnsOf γ.gs) r ∗ viewOf r X.v ∗ wEntKV (GF := GF) X.v es i k vl fl ⊢
      curAt tx γ es i k vl ∗ ⌜¬ isBktFlag fl⌝ := by
  unfold curAt wEntKV txBytes txBytesDef
  cases he : es[i]? with
  | some e =>
    simp only
    iintro ⟨#Hreg, #Hvo, ⟨%Hk, #Hks, #Hvs⟩⟩
    isplitl
    · isplitr
      · ipureintro; exact Hk.1
      isplitl
      · icases Hks with (#H | %H)
        · ileft; iexact H
        · iright; iexists r, X.v; iframe #; ipureintro; exact H
      · icases Hvs with (#H | %H)
        · ileft; iexact H
        · iright; iexists r, X.v; iframe #; ipureintro; exact H
    · ipureintro; exact Hk.2
  | none =>
    simp only
    iintro ⟨-, -, %Hn⟩
    obtain ⟨h1, h2, h3⟩ := Hn
    isplitl
    · ipureintro; exact ⟨h1, h2⟩
    · ipureintro; rw [h3]; unfold isBktFlag; decide

end pubWCur

end bbolt
end EtcdGrove
end Perennial
