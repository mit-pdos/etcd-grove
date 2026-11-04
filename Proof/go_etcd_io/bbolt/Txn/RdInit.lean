/-
A new reader's `rdTxK` (U5 of `notes/bbolt-proof-plan.md`): what `beginTx` assembles once
`Tx.init` ran, the reader is registered (`store_register`, `txs_register`) and its `mmaplock`
share is deposited.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Txn.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The root bucket's header a reader's root bucket stands for. -/
theorem inBucketOf_rootVal (v : View) :
    inBucketOf (rootVal v) = (⟨W64 (v.root : Int), W64 0⟩ : InBucket) := by
  unfold inBucketOf rootVal bytesAt
  rw [List.drop_zero, List.take_of_length_le (by rw [ByteEncoding.encode_length]; exact Nat.le_refl _),
    ByteEncoding.decode_encode]

omit [GooseExts] [GooseSemantics] [GooseInterp] in
/-- A `TxViewC` of a read-only view. -/
theorem ofC_ro (D : Data) : TxView.ofC ((false, D, D, ∅) : TxViewC) = TxView.ro D := by
  unfold TxView.ofC TxView.ro
  simp

private instance BC_core_persistent_ri (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

private theorem QpMul_one_r (q : Qp) : QpMul 1 q = q := Subtype.ext (by simp [QpMul])

omit package_sem in
/-- **A new reader's `rdTxK`** (design §3.11, "Reader begin"), from `Tx.init`'s fields, the meta
copy and the root bucket, the registration, the view's cells and `mmaplock`'s share. -/
theorem rdTxK_intro (K : BC) (tx : Loc) (src : PairSrc) (n : TxNames) (C : CommitSt) (b : Loc)
    (l k : Nat) (m ibp : Loc) (hok : C.metaOk) (htree : treeOK C) (htx : tx ≠ null)
    (hpgb : ∀ id pg, C.pages !! id = some pg → (id + 1) * 4096 ≤ l) :
    reg tx K.B ⟨K.db, n, false, src⟩ ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      K.core ∗
      ghostVar n.v (1 : Qp).half (((false, (View.ofC b C).data, (View.ofC b C).data, ∅) : TxViewC),
        TxX.rd (View.ofC b C) (metaOf (C.slot C.txid)) k) ∗
      ghostVar n.ex 1 () ∗
      tx.[Tx, go!"writable"] ↦ false ∗ tx.[Tx, go!"managed"] ↦ false ∗ tx.[Tx, go!"meta"] ↦ m ∗
      tx.[Tx, go!"root"] ↦ initRoot tx null null ibp ∗ tx.[Tx, go!"pages"] ↦ null ∗
      (∃ ch : GoSlice, tx.[Tx, go!"commitHandlers"] ↦ ch) ∗ (∃ wf : w64, tx.[Tx, go!"WriteFlag"] ↦ wf) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own ((1 : Qp).half + (1 : Qp).half.half)} K.db ∗
      m ↦ metaOf (C.slot C.txid) ∗ ibp ↦ (metaOf (C.slot C.txid)).root' ∗
      viewCells rq (View.ofC b C) ∗
      ghostVar K.B.map sync.rfrac.half.half (some (b, l) : MapSt) ∗
      mapFields K.db (DFrac.own sync.rfrac.half) (some (b, l) : MapSt) ∗
      ((View.ofC b C).base ↪[n.vw]□ View.ofC b C) ∗
      (if src = .loan then threadPool.isThreadPool (poolN K.N) K.B.pool (rdPair K.B K.db K.sp)
       else emp) ⊢
    |==> rdTxK K tx src 1 (TxView.ro (View.ofC b C).data) (View.ofC b C) := by
  iintro ⟨#Hreg, #Hpkg, #Hcore, Hv, Hex, Hw, Hmg, Hme, Hrt, Hpg, ⟨%ch, Hch⟩, ⟨%wf, Hwf⟩, Hdb,
    Hmv, Hib, Hvc, Hmap, Hmf, #Hvw, Hpool⟩
  have hroot2 : 2 ≤ C.root := by
    obtain ⟨⟨hwf, -⟩, -⟩ := htree
    cases hwf with
    | page _ _ h2 _ _ _ _ _ => exact h2
  have hroot64 : C.root < 2 ^ 64 := by
    obtain ⟨-, -, -, -, -, -, ⟨-, hr, -⟩, -⟩ := hok
    rw [← hr]; exact BitVec.isLt _
  have hrt : (metaOf (C.slot C.txid)).root'.root' = W64 (C.root : Int) := by
    obtain ⟨-, -, -, -, -, -, ⟨-, hr, -⟩, -⟩ := hok
    apply BitVec.eq_of_toNat_eq; rw [hr]; simp; omega
  ipersist Hib
  icases typedPointsto_not_null_dup _ _ _ $$ Hrt with ⟨Hrt, %Hrtn⟩
  unfold initRoot newBucketV
  iStructNamed Hrt
  imodintro
  unfold rdTxK
  iexists ⟨K.db, n, false, src⟩, ((false, (View.ofC b C).data, (View.ofC b C).data, ∅) : TxViewC),
    metaOf (C.slot C.txid), k
  isplitr
  · ipureintro; exact ⟨(ofC_ro _).symm, rfl, rfl, rfl⟩
  iframe Hreg Hpkg Hcore Hv Hex Hpool
  unfold rtxFrac
  simp only [QpMul_one_r]
  iexists ⟨false, false, null, m, initRoot tx null null ibp, null, zeroValDef, ch, wf⟩
  iframe Hw Hmg Hme Hpg Hch Hwf Hmv Hvc
  isplitl [InBucket tx buckets page rootNode nodes]
  · unfold rBkt
    iexists ibp, null
    iframe
    isplitl []
    · ileft
      iexists (metaOf (C.slot C.txid)).root'
      iframe Hib
      ipureintro
      rw [inBucketOf_rootVal, hrt]; rfl
    have h0 : inBucketRoot (rootVal (View.ofC b C)) ≠ 0 := by
      unfold inBucketRoot; rw [inBucketOf_rootVal]
      simp only [View.ofC]
      rw [toNat_W64_of_lt C.root hroot64]; omega
    simp only [h0, ↓reduceIte]
    ipureintro; trivial
  isplitl [FillPercent]
  · unfold txRoot; iexists _; iexact FillPercent
  isplitl [Hdb]
  · unfold txDbQ; simp only [QpMul_one_r]; iexact Hdb
  isplitl [Hmap Hmf]
  · iexists l; iframe; ipureintro; exact hpgb
  isplitl []
  · unfold viewOf; iexact Hvw
  ipureintro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | trivial | rfl | exact ⟨C, htree, rfl⟩ | exact hok.2.2.2.2.2.2.1.1 | exact htx |
      exact Hrtn

omit package_sem in
/-- **What `Rollback` reads of a reader** (`managed`, `db`, `writable`), and back. -/
theorem rdTxK_flags_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢
      tx.[Tx, go!"managed"] ↦{DFrac.own q} false ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} K.db ∗ tx.[Tx, go!"writable"] ↦{DFrac.own q} false ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ⌜K.db ≠ null⌝ ∗
      (tx.[Tx, go!"managed"] ↦{DFrac.own q} false -∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} K.db -∗ tx.[Tx, go!"writable"] ↦{DFrac.own q} false -∗
        rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpkg, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hmg, Hrest⟩, Hpool⟩
  icases Hrest with ⟨Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hrest⟩
  icases Hrest with ⟨Hmv, Hvc, Hmap, Hvo, %Hf⟩
  have hdb : r.db = K.db := Hc.2.1
  have hm : t.managed' = false := Hf.2.2.2.2.2.1
  ihave %hdbn : ⌜K.db ≠ null⌝ $$ []
  · unfold BC.core isBoltCoreP
    icases Hcore with ⟨-, -, %Ht, -⟩
    ipureintro; exact Ht.2.1
  rw [hm, hdb]
  iframe Hmg Hdb Hw Hpkg
  isplitr
  · ipureintro; exact hdbn
  iintro Hmg Hdb Hw
  iexists r, c, mv, k
  isplitr
  · ipureintro; exact Hc
  iframe Hreg Hcore Hv Hex Hpool
  iexists t
  rw [← hm] at *
  rw [← hdb]
  iframe
  ipureintro; exact ⟨Hf.1, Hf.2.1, Hf.2.2.1, Hf.2.2.2.1, Hf.2.2.2.2.1, rfl, Hf.2.2.2.2.2.2⟩

end rd

end bbolt
end EtcdGrove
end Perennial
