/-
The public read triples' (U6g, `notes/bbolt-proof-plan.md`) accessors: what a public read takes out
of a reader's `rdTxK` (its statistics token, view and registration), and the full database's
persistence.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pub
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isBoltP_persistent_pub (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

/-- **The reader's statistics token and view**, with its core and registration, out of `rdTxK`
and back (`Bucket.Cursor`'s public triple: the token for `Bucket.Cursor_i`, the view and the
registration for the cursor). -/
theorem rdTxK_cur_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ r : TxReg, K.core ∗ reg tx K.B r ∗ viewOf r v ∗
      ⌜r.rw = false⌝ ∗ statsTok r true q ∗ (statsTok r true q -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  iexists r
  iframe Hcore Hreg Hvo
  isplitr
  · ipureintro; exact Hc.2.2.1
  unfold statsTok
  simp only [ite_true]
  iframe Hex
  iintro Hex
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact Hf

/-- **A reader's views agree** (U6g): two `viewOf`s of a reader's registration are one view.
What a public reader triple needs to use a handle's view (`boltBktDef`'s, `boltCurDef`'s,
`txBytesDef`'s) with its `rdTxK`'s. A reader's view is at the fixed key `null` (maintainer R's
U6g item 2), so the two fragments agree. -/
def ViewOfRdAgree : Prop :=
  ∀ (r : TxReg) (v v' : View), r.rw = false → viewOf (GF := GF) r v ∗ viewOf r v' ⊢ ⌜v = v'⌝

theorem viewOfRdAgree_holds : ViewOfRdAgree (GF := GF) := by
  intro r v v' hrw
  unfold viewOf
  simp only [hrw, Bool.false_eq_true, ↓reduceIte]
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.2

/-- **A reader's new handle registered** (U6g): what `Tx.Bucket`'s reader post needs of the handle
`b` it opened (`boltBktDef`'s `handleFrag r b n 0`): a reader's `handleFrag` is `⌜g = 0⌝`
(maintainer R's U6g item 3; its bucket is in `boltBktDef`'s reader branch). -/
def RdHandleMint : Prop :=
  ∀ (B : BNs) (N : Namespace) (db tx b : Loc) (r : TxReg) (n : GoString), r.rw = false →
    isBoltDef (GF := GF) B N db ∗ reg tx B r ⊢ handleFrag r b n 0

theorem rdHandleMint_holds : RdHandleMint (GF := GF) := by
  intro B N db tx b r n hrw
  unfold handleFrag
  simp only [hrw, Bool.false_eq_true, ↓reduceIte]
  iintro -
  ipureintro; trivial

instance bytesPointsto_discard_persistent_pub (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l DFrac.discard bs) :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional_persistent

instance ite_persistent_pub {c : Prop} [Decidable c] (P Q : IProp GF) [Persistent P]
    [Persistent Q] : Persistent (if c then P else Q) := by
  split <;> infer_instance

instance rBkt_discard_persistent_pub (v : View) (tx b : Loc) (bv : List w8) :
    Persistent (rBkt (GF := GF) v tx b DFrac.discard bv) := by
  unfold rBkt locOwn; infer_instance

end pub

section pubKey
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A key and a live slice's bytes, read together** out of `rdTxK` (the key caller-owned or
the view's), and back (`bytes.Equal(key, k)` after a search). -/
theorem rd_keyR_src_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (key : GoSlice) (kr : KeyR) (kb : List w8) (s : GoSlice) (sr : Src) (bs : List w8)
    (hs : sr ≠ Src.stale) :
    rdTxK (GF := GF) K tx src q T v ∗ keyR v key kr kb ∗ srcOwn v s sr bs ⊢
      ∃ d1 d2 : DFrac, key ↦*{d1} kb ∗ s ↦*{d2} bs ∗
        (key ↦*{d1} kb -∗ s ↦*{d2} bs -∗ rdTxK K tx src q T v ∗ keyR v key kr kb) := by
  cases kr with
  | view =>
    simp only [keyR]
    iintro ⟨Hk, %Hin, #Hs⟩
    icases rdTxK_src2_acc K tx src q T v key s Src.view sr kb bs (by intro h; cases h) hs
      $$ [Hk Hs] with ⟨%d1, %d2, H1, H2, Hb⟩
    · iframe; iframe #; unfold srcOwn; ipureintro; exact Hin
    iexists d1, d2
    iframe
    iintro H1 H2
    ihave Hk := Hb $$ H1 H2
    iframe; ipureintro; exact Hin
  | heap dk =>
    simp only [keyR]
    iintro ⟨Hk, Hkey, #Hs⟩
    ihave %Hbase := rdTxK_base_pos K tx src q T v $$ Hk
    icases rdTxK_cells_acc K tx src q T v $$ Hk with ⟨%qc, Hc, Hkb⟩
    icases viewCells_src_acc qc v Hbase s sr bs hs $$ [Hc] with ⟨%d2, H2, Hcb⟩
    · iframe; iframe #
    iexists dk, d2
    iframe
    iintro Hkey H2
    ihave Hc := Hcb $$ H2
    ihave Hk := Hkb $$ Hc
    iframe

/-- **A key's bytes** out of `rdTxK` and back (`bytes.Equal(key, nil)`). -/
theorem rd_keyR_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (key : GoSlice) (kr : KeyR) (kb : List w8) :
    rdTxK (GF := GF) K tx src q T v ∗ keyR v key kr kb ⊢
      ∃ d1 : DFrac, key ↦*{d1} kb ∗ (key ↦*{d1} kb -∗ rdTxK K tx src q T v ∗ keyR v key kr kb) := by
  cases kr with
  | view =>
    simp only [keyR]
    iintro ⟨Hk, %Hin⟩
    ihave %Hbase := rdTxK_base_pos K tx src q T v $$ Hk
    icases rdTxK_cells_acc K tx src q T v $$ Hk with ⟨%qc, Hc, Hkb⟩
    icases viewCells_src_acc qc v Hbase key Src.view kb (by intro h; cases h) $$ [Hc]
      with ⟨%d1, H1, Hcb⟩
    · iframe; unfold srcOwn; ipureintro; exact Hin
    iexists d1
    iframe
    iintro H1
    ihave Hc := Hcb $$ H1
    ihave Hk := Hkb $$ Hc
    iframe; ipureintro; exact Hin
  | heap dk =>
    simp only [keyR]
    iintro ⟨Hk, Hkey⟩
    iexists dk
    iframe
    iintro Hkey
    iframe

end pubKey

end bbolt
end EtcdGrove
end Perennial
