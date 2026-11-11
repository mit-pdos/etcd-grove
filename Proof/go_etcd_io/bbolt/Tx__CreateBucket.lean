/-
The proof of `Spec/go_etcd_io/bbolt/Tx__CreateBucket.lean` (U7l, `notes/bbolt-proof-plan.md`): over
`wtxW` (`boltTxDef_wtxW`), `tx.root.CreateBucket(name)` by `Write.Bucket.CreateBucket.wp_root`
(`Write/CreateBktWp`); an error leaves the records as they are, a new bucket closes the new records
back with the view `T.setBkt n ∅` (`boltTxDef_wclose`, from `createOK`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__CreateBucket
public import Proof.go_etcd_io.bbolt.Write.CreateBktWp
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

theorem Tx.CreateBucket.wp_proof
    (hBw : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hNode : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Cursor.node.spec (GF := GF) (hG := hG))
    (hPut : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], node.put.spec (GF := GF) (hG := hG))
    (hWrite : Bucket.write.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Tx.CreateBucket.spec (GF := GF) (hG := hG) := by
  intro _ tx γ T name n dq
  wp_start as ⟨Ht, Hname, %Hpre⟩
  obtain ⟨hrw, hkm⟩ := Hpre
  unfold boltTx boltBkt at *
  ihave Ht := (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur', hbase, hgens, hwr, hwc⟩ := Hf
  icases wtxW_heapOK' K tx r true X $$ Hw with ⟨Hw, %Hhok⟩
  have hrl : X.rl = txRoot (GF := GF) tx := Hhok.1
  wp_auto
  rw [show tx.[Tx, go!"root"] = txRoot (GF := GF) tx from rfl, ← hrl]
  iapply wp_fupd
  wp_apply Write.Bucket.CreateBucket.wp_root hBw hCur hSeek hNode hPut hWrite hClone hEq K tx r X T
    name n dq hok hcur' hgens hwr hwc hkm $$ [Hw Hname] as %b %err ⟨Hname, Hres⟩
  · iframe
  by_cases hn0 : n.length = 0
  · rw [if_pos hn0] at *
    icases Hres with ⟨%he, Hw⟩
    imodintro
    iapply HΦ
    rw [if_pos (Or.inl hn0), if_pos hn0]
    iframe Hname
    isplitl
    · iapply (boltTxDef_wtxW _ _ tx T hrw).2
      iexists K, r, c, X
      iframe; iframe #
      ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr, hwc⟩
    ipureintro; exact he
  by_cases hex : T.cur.lookup n ≠ none
  · simp only [hn0, hex, ↓reduceIte, ne_eq, not_false_eq_true] at *
    icases Hres with ⟨#He, Hw⟩
    imodintro
    iapply HΦ
    simp only [↓reduceIte, false_or]
    iframe Hname; iframe #
    iapply (boltTxDef_wtxW _ _ tx T hrw).2
    iexists K, r, c, X
    iframe; iframe #
    ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr, hwc⟩
  have hnew : T.cur !! n = none := by simpa using hex
  have hne : ¬ (T.cur !! n ≠ none) := fun h => h hnew
  have hor : ¬ (n.length = 0 ∨ T.cur !! n ≠ none) := by
    rintro (h | h); exact hn0 h; exact h hnew
  rw [if_neg hn0, if_neg hne, if_neg hor]
  icases Hres with ⟨%he, %X', Hw, #Hbkt, %Hc⟩
  obtain ⟨hokX', hdX', hgX', hwrX', hk, hsh, hwcX'⟩ := Hc
  let c' : TxViewC := (c.1, c.2.1, c.2.2.1.insert n ∅, c.2.2.2)
  have hTc' : T.setBkt n ∅ = TxView.ofC c' := by rw [hTc]; rfl
  imod boltTxDef_wclose K tx r c c' X X' (T.setBkt n ∅) ⊤ (by simp) hTc' hk hsh
    ⟨hokX', hrw, by rw [hdX']; rfl, by rw [hk.v]; exact hbase, hgX', hwrX', hwcX'⟩ $$
    [Hv Hw Hst] with Ht
  · rw [hk.v, hKB, show (T.setBkt n ∅).base = T.base from rfl]; iframe; iframe #
  imodintro
  iapply HΦ
  rw [← hKB, ← hKN]
  iframe Ht Hname
  rw [if_neg hn0, if_neg hne]
  iframe Hbkt
  ipureintro; exact he

end proof

end bbolt
end EtcdGrove
end Perennial
