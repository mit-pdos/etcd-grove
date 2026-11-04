/-
The proof of `Spec/go_etcd_io/bbolt/Tx__DB.lean` (U5, `notes/bbolt-proof-plan.md`): a live
transaction holds a share of its `db` field, the registered database (`reg`), which `txDB`'s
registration names.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__DB
public import Proof.go_etcd_io.bbolt.Inv.Tx
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

private instance reg_persistent_d (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance isBoltP_persistent_d [HasExt osFsExt] (B : BNs) (N : Namespace) (db : Loc)
    (p : GoString) (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance viewOf_persistent_d (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

/-- A live transaction's `db` field, at its share, with its registration, and back. -/
private theorem boltTxDef_db_acc [HasExt osFsExt] (B : BNs) (N : Namespace) (tx : Loc) (q : Qp)
    (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ∃ r : TxReg,
      reg tx B r ∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} r.db ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} r.db -∗ boltTxDef B N tx q T) := by
  unfold boltTxDef
  split
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    unfold wtxFrac
    icases Hw with ⟨Hh, Hf, Hvc, Hst, Hbk, Hnl, Hdb, Hm, #Hvo, %Hok⟩
    iexists r
    iframe Hreg Hdb
    iintro Hdb
    iexists db, p, sp, t0, r, c, X
    iframe Hreg Hb Hv Hex
    isplitr
    · ipureintro; exact Hc
    iframe Hh Hf Hvc Hst Hbk Hnl Hdb Hm Hvo
    ipureintro; exact Hok
  · iintro ⟨%db', Hr, #Hb'⟩
    unfold rdTx rtxFrac
    icases Hr with ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore, Hv, Hex,
      ⟨%t, Hw, Hmg, Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hmv, Hvc, Hm, #Hvo, %Hf⟩, Hpool⟩
    iexists r
    iframe Hreg Hdb
    iintro Hdb
    iexists db'
    iframe Hb'
    iexists db, p, sp, t0, r, c, v, mv, k
    iframe Hreg Hcore Hv Hex Hpool
    isplitr
    · ipureintro; exact Hc
    iexists t
    iframe Hw Hmg Hme Hrb Hfp Hpg Hch Hwf Hdb Hmv Hvc Hm Hvo
    ipureintro; exact Hf

theorem Tx.DB.wp_proof : Tx.DB.spec (GF := GF) (hG := hG) := by
  intro _ tx db γ q T
  wp_start as ⟨Ht, #Hd⟩
  unfold boltTx
  unfold txDB txDBDef
  icases Hd with ⟨%r', -, #Hr', %Hdb⟩
  icases boltTxDef_db_acc _ _ tx q T $$ Ht with ⟨%r, #Hr, Hf, Hcl⟩
  unfold reg
  icombine Hr Hr' gives %hr
  obtain ⟨-, rfl⟩ := hr
  subst Hdb
  wp_auto
  iapply HΦ
  iapply Hcl
  iexact Hf

end proof

end bbolt
end EtcdGrove
end Perennial
