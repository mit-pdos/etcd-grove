/-
The proof of `Spec/go_etcd_io/bbolt/Tx__CreateBucketIfNotExists.lean` (U7l,
`notes/bbolt-proof-plan.md`): over `wtxW` (`boltTxDef_wtxW`), `tx.root.CreateBucketIfNotExists(name)`
by `Write.Bucket.CreateBucketIfNotExists.wp_root` (`Write/CreateBktIfWp`); an empty name leaves the
records as they are, a new bucket closes the new records back with the view `T.setBkt n ∅`
(`createOK`), an existing one with `T` (`openOK`), both by `boltTxDef_wclose`.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists
public import Proof.go_etcd_io.bbolt.Write.CreateBktIfWp
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.CreateBucketIfNotExists.wp_proof
    (hBw : ∀ [HasExt osFsExt], Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : ∀ [HasExt osFsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : ∀ [HasExt osFsExt], Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hNode : ∀ [HasExt osFsExt], Cursor.node.spec (GF := GF) (hG := hG))
    (hPut : ∀ [HasExt osFsExt], node.put.spec (GF := GF) (hG := hG))
    (hWrite : Bucket.write.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (hopen : ∀ [HasExt osFsExt], Bucket.openBucket_w.spec (GF := GF) (hG := hG)) :
    Tx.CreateBucketIfNotExists.spec (GF := GF) (hG := hG) := by
  intro _ tx γ T name n dq
  wp_start as ⟨Ht, Hname, %Hpre⟩
  obtain ⟨hrw, hkm⟩ := Hpre
  unfold boltTx boltBkt at *
  ihave Ht := (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur', hbase, hgens, hwr⟩ := Hf
  icases wtxW_heapOK' K tx r true X $$ Hw with ⟨Hw, %Hhok⟩
  have hrl : X.rl = txRoot (GF := GF) tx := Hhok.1
  wp_auto
  rw [show tx.[Tx, go!"root"] = txRoot (GF := GF) tx from rfl, ← hrl]
  iapply wp_fupd
  wp_apply Write.Bucket.CreateBucketIfNotExists.wp_root hBw hCur hSeek hNode hPut hWrite hClone hEq
    hopen K tx r X T name n dq hok hcur' hgens hwr hkm $$ [Hw Hname] as %b %err ⟨Hname, Hres⟩
  · iframe
  by_cases hn0 : n.length = 0
  · rw [if_pos hn0]
    icases Hres with ⟨%he, Hw⟩
    imodintro
    iapply HΦ
    rw [if_pos hn0]
    iframe Hname
    isplitr
    · ipureintro; exact he
    iapply (boltTxDef_wtxW _ _ tx T hrw).2
    iexists K, r, c, X
    iframe; iframe #
    ipureintro; exact ⟨⟨hKB, hKN, hTc⟩, hok, hcur', hbase, hgens, hwr⟩
  rw [if_neg hn0]
  icases Hres with ⟨%he, %X', Hw, #Hbkt, %Hc⟩
  by_cases hnew : T.cur !! n = none
  · rw [if_pos hnew] at Hc
    obtain ⟨hokX', hdX', hgX', hwrX', hk, hsh⟩ := Hc
    let c' : TxViewC := (c.1, c.2.1, c.2.2.1.insert n ∅, c.2.2.2)
    have hTc' : T.setBkt n ∅ = TxView.ofC c' := by rw [hTc]; rfl
    imod boltTxDef_wclose K tx r c c' X X' (T.setBkt n ∅) ⊤ (by simp) hTc' hk hsh
      ⟨hokX', hrw, by rw [hdX']; rfl, by rw [hk.v]; exact hbase, hgX', hwrX'⟩ $$
      [Hv Hw Hst] with Ht
    · rw [hk.v, hKB, show (T.setBkt n ∅).base = T.base from rfl]; iframe; iframe #
    imodintro
    iapply HΦ
    rw [← hKB, ← hKN, if_neg hn0, if_pos hnew]
    iframe Ht Hname Hbkt
    ipureintro; exact he
  · rw [if_neg hnew] at Hc
    obtain ⟨hokX', hdX', hgX', hwrX', hk, hsh⟩ := Hc
    imod boltTxDef_wclose K tx r c c X X' T ⊤ (by simp) hTc hk hsh
      ⟨hokX', hrw, by rw [hdX']; exact hcur', by rw [hk.v]; exact hbase, hgX', hwrX'⟩ $$
      [Hv Hw Hst] with Ht
    · rw [hk.v, hKB]; iframe; iframe #
    imodintro
    iapply HΦ
    rw [← hKB, ← hKN, if_neg hn0, if_neg hnew]
    iframe Ht Hname Hbkt
    ipureintro; exact he

end proof

end bbolt
end EtcdGrove
end Perennial
