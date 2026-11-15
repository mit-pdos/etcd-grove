/-
The proof of `Spec/go_etcd_io/bbolt/DB__Info.lean` (U5, `notes/bbolt-proof-plan.md`): a live
transaction holds a share of `mmaplock`'s mapping fields (a reader's `rtxFrac`, a writer's
`wtxFrac`), mapped, so `db.data` is the mapping's positive base; the page size is `dbFixed`'s.
-/
module

public import Spec.go_etcd_io.bbolt.DB__Info
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Inv.Tx
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

private instance isBoltP_persistent_i [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (db : Loc)
    (p : BFile) (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance reg_persistent_i [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance viewOf_persistent_i [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

/-- What `DB.Info` reads through a live transaction: its database's core and the `data` field at
some fraction (the mapping's base, positive), and back. -/
private theorem boltTxDef_data_acc [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (tx : Loc) (q : Qp)
    (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ∃ (db b : Loc) (dq : DFrac),
      isBoltCore B N db ∗ db.[DB, go!"data"] ↦{dq} b ∗ ⌜0 < b.addr⌝ ∗
      (db.[DB, go!"data"] ↦{dq} b -∗ boltTxDef B N tx q T) := by
  unfold boltTxDef
  split
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    unfold wtxFrac
    icases Hw with ⟨Hh, Hf, Hvc, Hst, Hbk, Hnl, Hdb, ⟨%l, Hmf, %Hl⟩, #Hvo, %Hok⟩
    iunfold mapFields at Hmf
    icases Hmf with ⟨Hdr, Hd, Hm0, Hm1, %Hb⟩
    obtain ⟨hT, rfl, hrw⟩ := Hc
    iexists r.db, X.v.base, DFrac.own (QpMul q (1 : Qp).half.half)
    iframe Hd
    isplitl []
    · unfold isBoltCore isBoltP; icases Hb with ⟨Hc, -⟩; iexists p, sp, t0; iexact Hc
    isplitl []
    · ipureintro; exact Hb.2.1
    iintro Hd
    iexists r.db, p, sp, t0, r, c, X
    iframe Hreg Hb Hv Hex
    isplitr
    · ipureintro; exact ⟨hT, rfl, hrw⟩
    ihave Hmf : mapFields r.db (DFrac.own (QpMul q (1 : Qp).half.half)) (some (X.v.base, l) : MapSt)
      $$ [Hdr Hd Hm0 Hm1]
    · simp only [mapFields]; iframe; ipureintro; exact Hb
    iframe Hh Hf Hvc Hst Hbk Hnl Hdb Hvo
    isplitl [Hmf]
    · iexists l; iframe; ipureintro; exact Hl
    ipureintro; exact Hok
  · iintro ⟨%db', Hr, #Hb'⟩
    unfold rdTx rtxFrac
    icases Hr with ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore, Hv, Hex,
      ⟨%t, Hw, Hmg, Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hmv, Hvc, ⟨%l, Hmap, Hmf, %Hl⟩, #Hvo, %Hf⟩,
      Hpool⟩
    iunfold mapFields at Hmf
    icases Hmf with ⟨Hdr, Hd, Hm0, Hm1, %Hb⟩
    obtain ⟨hT, rfl, hrw, hsrc⟩ := Hc
    iexists r.db, v.base, DFrac.own (QpMul q sync.rfrac).half
    iframe Hd
    isplitl []
    · unfold isBoltCore; iexists p, sp, t0; iexact Hcore
    isplitl []
    · ipureintro; exact Hb.2.1
    iintro Hd
    iexists db'
    iframe Hb'
    iexists r.db, p, sp, t0, r, c, v, mv, k
    iframe Hreg Hcore Hv Hex Hpool
    isplitr
    · ipureintro; exact ⟨hT, rfl, hrw, hsrc⟩
    ihave Hmf : mapFields r.db (DFrac.own (QpMul q sync.rfrac).half) (some (v.base, l) : MapSt)
      $$ [Hdr Hd Hm0 Hm1]
    · simp only [mapFields]; iframe; ipureintro; exact Hb
    iexists t
    iframe Hw Hmg Hme Hrb Hfp Hpg Hch Hwf Hdb Hmv Hvc Hvo
    isplitl [Hmap Hmf]
    · iexists l; iframe; ipureintro; exact Hl
    ipureintro; exact Hf

theorem DB.Info.wp_proof (wp_Assert : internal.common.Assert.spec (GF := GF) (hG := hG)) :
    DB.Info.spec (GF := GF) (hG := hG) := by
  intro _ _ _ db tx γ q T
  wp_start as ⟨#Hdb, -, Ht⟩
  unfold boltTx
  icases boltTxDef_data_acc _ _ tx q T $$ Ht with ⟨%db', %b, %dq, #Hc, Hd, %Hb, Hcl⟩
  ihave %he := isBolt_db_agree _ _ db db' $$ [Hdb Hc]
  · unfold isBolt; iframe #
  subst he
  ihave #Hps : db.[DB, go!"pageSize"] ↦□ W64 4096 $$ []
  · unfold isBoltCore isBoltCoreP dbFixed
    icases Hc with ⟨%p, %sp, %t0, -, -, -, -, -, ⟨$, -⟩, -⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
  · unfold isBoltCore isBoltCoreP
    icases Hc with ⟨%p, %sp, %t0, -, -, -, $, -⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  have hbn : b ≠ null := fun e => by subst e; exact absurd Hb (Int.lt_irrefl 0)
  wp_auto
  rw [decide_eq_false hbn]
  wp_auto
  wp_apply wp_Assert
  wp_apply wp_ArbitraryInt as %x -
  iapply HΦ
  ihave Ht := Hcl $$ Hd
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
