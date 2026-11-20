/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__ForEach.lean` (auth-schema-srv port, 2026-11-19): the
transaction's `db` field is not nil (a writer's `isBoltP`, a reader's `rdTxK`), then the public
`Bucket.Cursor`, `Cursor.First` and `Cursor.Next` over the bucket's entries, the visitor on each.
The loop holds `I i`, the cursor at the `i`-th entry while there is one, and `curAt` of the `i`-th.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__ForEach
public import Spec.go_etcd_io.bbolt.Bucket__Cursor
public import Spec.go_etcd_io.bbolt.Cursor__First
public import Spec.go_etcd_io.bbolt.Cursor__Next
public import Proof.go_etcd_io.bbolt.Read.Iter
public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Read.Pub
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The transaction's `db` field, not nil (either kind), out of `boltTx` and back. -/
private theorem boltTx_db_nn [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc)
    (γ : BoltName) (q : Qp) (T : TxView) :
    boltTx (GF := GF) tx γ q T ⊢ ∃ (d : Loc) (dq : DFrac), tx.[Tx, go!"db"] ↦{dq} d ∗ ⌜d ≠ null⌝ ∗
      (tx.[Tx, go!"db"] ↦{dq} d -∗ boltTx tx γ q T) := by
  unfold boltTx boltTxDef
  split
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    ihave #Hcore : BC.core (GF := GF) ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ $$ []
    · unfold BC.core; unfold isBoltP; icases Hb with ⟨$, -⟩
    ihave %Hnn := BC.core_db_nonnull _ $$ Hcore
    unfold wtxFrac
    icases Hw with ⟨Hh, Hf, Hvc, Hst, Hbk, Hnl, Hdb, Hm, #Hvo, %Hok⟩
    iexists r.db, _
    iframe Hdb
    isplitr
    · ipureintro; rw [Hc.2.1]; exact Hnn
    iintro Hdb
    iexists db, p, sp, t0, r, c, X
    iframe Hreg Hb Hv Hex
    isplitr
    · ipureintro; exact Hc
    iframe Hh Hf Hvc Hst Hbk Hnl Hdb Hm Hvo
    ipureintro; exact Hok
  · iintro ⟨%db', Hr, #Hb'⟩
    ihave Hr := (rdTx_rdTxK _ _ tx .loan q T).1 $$ Hr
    icases Hr with ⟨%K, %v, %HK, Hk⟩
    icases rdTxK_db_acc K tx .loan q T v $$ Hk with ⟨%dd, Hdb, %Hnn, Hcl⟩
    iexists K.db, dd
    iframe Hdb
    isplitr
    · ipureintro; exact Hnn
    iintro Hdb
    ihave Hk := Hcl $$ Hdb
    iexists db'
    iframe Hb'
    iapply (rdTx_rdTxK _ _ tx .loan q T).2
    iexists K, v
    iframe
    ipureintro; exact HK

/-- `curAt` past the entries: the key is nil. -/
private theorem curAt_end [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName)
    (es : List BoltEnt) (i : Nat) (k v : GoSlice) (hk : k ≠ slice.nil) :
    curAt (GF := GF) tx γ es i k v ⊢ ⌜i < es.length⌝ := by
  unfold curAt
  split
  · rename_i e he
    iintro -; ipureintro
    exact (List.getElem?_eq_some_iff.mp he).1
  · iintro %H; exact absurd H.1 hk

/-- `curAt` with a nil key: past the entries. -/
private theorem curAt_nil [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName)
    (es : List BoltEnt) (i : Nat) (v : GoSlice) :
    curAt (GF := GF) tx γ es i slice.nil v ⊢ ⌜es.length ≤ i⌝ := by
  unfold curAt
  split
  · iintro ⟨%H, -⟩; exact absurd rfl H
  · rename_i he
    iintro -; ipureintro
    exact List.getElem?_eq_none_iff.mp he

theorem Bucket.ForEach.wp_proof
    (hcur : Bucket.Cursor.spec (GF := GF) (hG := hG))
    (hfst : Cursor.First.spec (GF := GF) (hG := hG))
    (hnx : Cursor.Next.spec (GF := GF) (hG := hG)) :
    Bucket.ForEach.spec (GF := GF) (hG := hG) := by
  intro _ _ _ tx γ q T b n m fn I E
  wp_start as ⟨Ht, #Hb, %Hm, HI, #Hfn⟩
  ihave #Hbtx : b.[Bucket, go!"tx"] ↦□ tx $$ []
  · unfold boltBkt boltBktDef; icases Hb with ⟨%r, -, #H, -⟩; iexact H
  icases boltTx_db_nn tx γ q T $$ Ht with ⟨%d, %dq, Hdb, %Hnn, Hcl⟩
  wp_auto
  simp only [decide_eq_false Hnn]
  wp_auto
  ihave Ht := Hcl $$ Hdb
  wp_apply hcur tx γ q T b n m $$ [Ht] as %c ⟨Ht, Hc⟩
  · iframe; iframe #; ipureintro; exact Hm
  try wp_auto
  wp_apply hfst tx c γ q T (bktEnts m) none $$ [Ht Hc] as %k0 %v0 ⟨Ht, Hc, #Hcur⟩
  · iframe
  try wp_auto
  ihave IH : (∃ (i : Nat) (p : Nat) (k vl : GoSlice),
      "k" ∷ k_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vl ∗ "Ht" ∷ boltTx tx γ q T ∗
      "Hc" ∷ boltCur tx γ c T (bktEnts m) (some p) ∗ "HI" ∷ I i ∗
      "#Hcur" ∷ curAt tx γ (bktEnts m) i k vl ∗
      "%Hp" ∷ ⌜i ≤ (bktEnts m).length ∧ (i < (bktEnts m).length → p = i)⌝ : IProp GF)
    $$ [k v Ht Hc HI]
  · iexists 0, 0, k0, v0
    simp only [named]
    iframe; iframe #
    ipureintro; exact ⟨Nat.zero_le _, fun _ => trivial⟩
  wp_for IH
  cleanup_bool_decide
  by_cases hkn : k = slice.nil
  · simp only [hkn, _root_.decide_true, Bool.not_true, intoVal_eq_iff, Bool.false_eq_true,
      _root_.decide_false, ↓reduceIte]
    wp_auto
    ihave %Hle := curAt_nil tx γ (bktEnts m) i vl $$ Hcur
    have hi : i = (bktEnts m).length := Nat.le_antisymm Hp.1 Hle
    iapply HΦ
    iframe
    ileft
    rw [← hi]
    iframe
    ipureintro; rfl
  · simp only [hkn, _root_.decide_false, Bool.not_false, _root_.decide_true, ↓reduceIte]
    ihave %Hlt := curAt_end tx γ (bktEnts m) i k vl hkn $$ Hcur
    have hp := Hp.2 Hlt
    subst hp
    wp_auto
    wp_apply Hfn $$ %p %k %vl [Ht HI] as %err ⟨Ht, HIE⟩
    · iframe; iframe #; ipureintro; exact Hlt
    try wp_auto
    cases err with
    | ok ie =>
      icases HIE with (⟨%He, -⟩ | ⟨%He, HE⟩)
      · cases He
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iright
      iexists p
      iframe
      ipureintro; exact ⟨He, Hlt⟩
    | nil =>
      icases HIE with (⟨-, HI⟩ | ⟨%He, -⟩)
      rotate_left
      · exact absurd rfl He
      wp_auto
      wp_for_post
      wp_apply hnx tx c γ q T (bktEnts m) (some p) $$ [Ht Hc] as %k' %v' ⟨Ht, Hc, #Hcur'⟩
      · iframe
      try wp_auto
      iframe
      iexists p + 1, (if p + 1 < (bktEnts m).length then p + 1 else p), k', v'
      simp only [named]
      iframe; iframe #
      ipureintro
      refine ⟨Hlt, fun h => ?_⟩
      simp [h]

end proof

end bbolt
end EtcdGrove
end Perennial
