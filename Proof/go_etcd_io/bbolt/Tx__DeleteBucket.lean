/-
The proof of `Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean` (U7m, `notes/bbolt-proof-plan.md`): over
`wtxW` (`boltTxDef_wtxW`) with the exclusive part taken out (`Write/DelBktXcl.dbk_open`: mode
`false`, the database side `wdbW` for `child.free()`), `tx.root.DeleteBucket(name)` by
`Write.Bucket.DeleteBucket.wp_root` (`Write/DelBktWp`); the exclusive part put back and `boltTx`
closed at `T` (an absent name) or `T.dropBkt n` (`dbk_close`, from `deleteOK`).

The empty name in an empty root bucket returns `ErrIncompatibleValue` (U7m's finding; the triple's
middle case since D-M). `wrCurFacts T X` is `boltTx`'s writer facts' (maintainer 16); `deleteOK`'s
`wrCurFacts (T.dropBkt n) X'` is what closes with.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__DeleteBucket
public import Proof.go_etcd_io.bbolt.Write.DelBktWp
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

/-- The view with `n` deleted, encoded. -/
def dropC (c : TxViewC) (n : GoString) : TxViewC :=
  (c.1, c.2.1, c.2.2.1.delete n, c.2.2.2.insert n ((c.2.2.2 !! n).getD 0 + 1))

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx package_sem in
theorem dropBkt_ofC (c : TxViewC) (n : GoString) :
    (TxView.ofC c).dropBkt n = TxView.ofC (dropC c n) := by
  unfold TxView.dropBkt TxView.ofC dropC
  simp only [TxView.mk.injEq, true_and]
  funext x
  by_cases h : x = n
  · subst h; simp
  · simp [h, Ne.symm h]

theorem Tx.DeleteBucket.wp_proof
    (hBw : ∀ [HasExt osFsExt], Bucket.Bucket_w.spec (GF := GF) (hG := hG))
    (hCur : ∀ [HasExt osFsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hSeek : ∀ [HasExt osFsExt], Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hFeb : ∀ [HasExt osFsExt], Bucket.ForEachBucket_w.spec (GF := GF) (hG := hG))
    (hNode : ∀ [HasExt osFsExt], Cursor.node.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hFree : ∀ [HasExt osFsExt], Bucket.free_dead.spec (GF := GF) (hG := hG))
    (hClone : cloneBytes.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Tx.DeleteBucket.spec (GF := GF) (hG := hG) := by
  intro _ tx γ T name n dq
  wp_start as ⟨Ht, Hname, %hrw⟩
  unfold boltTx at *
  ihave Ht := (boltTxDef_wtxW _ _ tx T hrw).1 $$ Ht
  icases Ht with ⟨%K, %r, %c, %X, %HK, #Hfull, #Hvo, Hv, Hw, Hst, %Hf⟩
  obtain ⟨hKB, hKN, hTc⟩ := HK
  obtain ⟨hok, hcur', hbase, hgens, hwr, hwc⟩ := Hf
  icases wtxW_heapOK' K tx r true X $$ Hw with ⟨Hw, %Hhok⟩
  have hrl : X.rl = txRoot (GF := GF) tx := Hhok.1
  imod Write.dbk_open K tx r X c $$ [Hw Hv] with Hx
  · iframe
  wp_auto
  icases Hx with ⟨Hw, Hv, Hxcl⟩
  unfold Write.dbkXcl
  icases Hxcl with ⟨Hrwl, Hcls, %w, %extra, Hwdb, Hshape, %Hxf⟩
  rw [show tx.[Tx, go!"root"] = txRoot (GF := GF) tx from rfl, ← hrl]
  iapply wp_fupd
  wp_apply Write.Bucket.DeleteBucket.wp_root hBw hCur hSeek hFeb hNode hDel hFree hClone hEq K tx r
    X w T name n dq hok hcur' hgens hwr
    hwc Hxf.1 $$ [Hw Hwdb Hname] as %err ⟨Hname, Hres⟩
  · iframe
  rw [← hKB, ← hKN]
  by_cases hex : T.cur.lookup n = none
  · rw [if_pos hex]
    icases Hres with ⟨Hw, Hwdb, Herr⟩
    icases Herr with (#He | ⟨%hn, #He⟩)
    · imod Write.dbk_close K tx r c c X X w extra T hTc ⟨hok, hrw, hcur', hbase, hgens, hwr, hwc⟩ Hxf
        $$ [Hv Hw Hrwl Hcls Hwdb Hshape Hst] with Ht
      · iframe; iframe #
      imodintro
      iapply HΦ
      iframe Hname
      ileft
      iframe Ht; iframe #
      ipureintro; exact hex
    · -- the empty name in an empty root bucket: `ErrIncompatibleValue` (D-M)
      imod Write.dbk_close K tx r c c X X w extra T hTc ⟨hok, hrw, hcur', hbase, hgens, hwr, hwc⟩ Hxf
        $$ [Hv Hw Hrwl Hcls Hwdb Hshape Hst] with Ht
      · iframe; iframe #
      imodintro
      iapply HΦ
      iframe Hname
      iright; ileft
      iframe Ht; iframe #
      ipureintro; exact ⟨hn, hex⟩
  rw [if_neg hex]
  icases Hres with ⟨%he, %X', %w', Hw, Hwdb, %Hd⟩
  obtain ⟨hok', hd', hg', hwr', hv', hmv', hC', hfl', hsh', hwc'⟩ := Hd
  have hT' : T.dropBkt n = TxView.ofC (dropC c n) := by rw [hTc]; exact dropBkt_ofC c n
  ihave Hshape := hsh' extra $$ Hshape
  rw [show X.v = X'.v from hv'.symm]
  imod Write.dbk_close K tx r c (dropC c n) X X' w' extra (T.dropBkt n) hT'
      ⟨hok', hrw, hd'.symm, by rw [hv']; exact hbase, hg', hwr', hwc'⟩
      ⟨hfl', by rw [hmv', hC']; exact Hxf.2.1, by rw [hC']; exact Hxf.2.2⟩
    $$ [Hv Hw Hrwl Hcls Hwdb Hshape Hst] with Ht
  · iframe; iframe #
  imodintro
  iapply HΦ
  iframe Hname
  iright; iright
  iframe Ht
  ipureintro; exact ⟨hex, he⟩

end proof

end bbolt
end EtcdGrove
end Perennial
