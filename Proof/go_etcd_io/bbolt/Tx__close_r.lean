/-
The proof of `Spec/go_etcd_io/bbolt/Tx__close_r.lean` (U5, `notes/bbolt-proof-plan.md`; design
§3.11 "Reader end"): the exclusive part taken out (`txExcl_take`), `removeTx` (`Txn/RemoveTx`), then
the fields cleared with all of `tx.db` (the invariant's quarter came out at `txs_close`) and the
pair's source given back.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__close_r
public import Proof.go_etcd_io.bbolt.Txn.RemoveTx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos in
private theorem QpMul_one_c (q : Qp) : QpMul 1 q = q := Subtype.ext (by simp [QpMul])

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos in
private theorem txDbQ_one_quarter : (1 : Qp).half.half + txDbQ 1 = 1 :=
  Subtype.ext (by simp only [txDbQ, QpMul, Qp.val_add, Qp.val_half, Qp.val_one]; grind)

private instance BC_core_persistent_cr (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

theorem Tx.close_r.wp_proof (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_RemoveRO : internal.freelist.Interface.RemoveReadonlyTXID.spec (GF := GF) (hG := hG)) :
    Tx.close_r.spec (GF := GF) (hG := hG) := by
  intro K tx src T v
  wp_start as Hrd
  iunfold rdTxK at Hrd
  icases Hrd with ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpkg, #Hcore, Hv, Hex, Hrt, Hpool⟩
  obtain ⟨hT, hdb, hrw, hsrc⟩ := Hc
  iunfold rtxFrac at Hrt
  icases Hrt with ⟨%t, Hw, Hmg, Hme, Hrb, ⟨%f, Hfp⟩, Hpg, Hch, Hwf, Hdb, Hmv, Hvc,
    ⟨%l, Hmap, Hmf, %Hl⟩, Hvo, %Hf⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  imod txExcl_take K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hti Hreg Hex] with Hx
  · iframe; iframe #
  wp_auto
  rw [hdb, decide_eq_false Ht0.2.1]
  wp_auto
  iunfold txExcl at Hx
  icases Hx with ⟨%c', %x, Hv', Hd, Hx⟩
  icombine Hv Hv' gives %hv
  obtain ⟨-, hv⟩ := hv
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
  icases Hx with ⟨Hrl, Hloan, Hstok, Hrds⟩
  simp only [QpMul_one_c]
  rw [hdb]
  -- batch 41: the spare reader's half of `B.spr`, for `removeTx`
  ihave ⟨Hpool, Hsp⟩ : (if src = .loan then
      threadPool.isThreadPool (poolN K.N) K.B.pool (rdPair K.B K.db K.sp) else emp) ∗
      (if r.src = .loan then emp else ghostVar K.B.spr (1 : Qp).half (some k)) $$ [Hpool]
  · cases src
    · simp only [hsrc, ↓reduceIte]; iframe
    · simp only [hsrc, reduceCtorEq, ↓reduceIte]; iframe
  wp_apply wp_removeTx wp_Txid wp_RemoveRO K tx r v mv k t.meta' l hdb Hf.2.2.1
    $$ [Hrl Hmap Hmf Hrds Hvc Hstok Hd Hme Hmv Hsp] as ⟨Hmtok, Hstok, Hme, Hmv, Hdb4, Hd, #Hdone, Htok⟩
  · iframe; iframe #
  -- the pair's source back
  ihave Hback : |={⊤}=> pairBack K src $$ [Hloan Hpool Hmtok Hstok Htok]
  · cases src
    · simp only [hsrc, ↓reduceIte, pairBack]
      iapply threadPool.giveBack (poolN K.N) K.B.pool (rdPair K.B K.db K.sp) ⊤ CoPset.subseteq_top
      iframe Hpool Hloan
      iunfold rdPair; iframe
    · simp only [hsrc, reduceCtorEq, ↓reduceIte, pairBack, sparePair, rdPair]
      imodintro; iframe
  imod Hback with Hback
  -- the fields cleared: all of `tx.db`, the root bucket whole
  rw [hdb] at *
  ihave Hdb := (typedPointsto_frac_add _ _ _ _).2 $$ [Hdb Hdb4]
  · iframe
  rw [txDbQ_one_quarter]
  iunfold rBkt at Hrb
  icases Hrb with ⟨%ibp, %pp, Hib, Htx, Hbk, Hpp, Hrn, Hnd, -, -⟩
  ihave Hroot : (txRoot tx) ↦ (⟨ibp, tx, null, pp, null, null, f⟩ : go_etcd_io.bbolt.Bucket) $$
    [Hib Htx Hbk Hpp Hrn Hnd Hfp]
  · iapply typedPointsto_combine _ _ _ Hf.2.2.2.2.2.2.1
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  unfold txRoot
  wp_auto
  iapply HΦ
  iframe
  iexact Hdone

end proof

end bbolt
end EtcdGrove
end Perennial
