/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Size.lean` (U5, `notes/bbolt-proof-plan.md`): the meta
copy's `pgid` (a reader's `rtxFrac`, a writer's `txFields`) times the page size (`dbFixed`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Size
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
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

private instance isBoltP_persistent_sz [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (db : Loc)
    (p : BFile) (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance isBoltCoreP_persistent_sz [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (db : Loc)
    (p : BFile) (sp : Loc) (t0 : Nat) : Persistent (isBoltCoreP (GF := GF) B N db p sp t0) := by
  unfold isBoltCoreP dblAt t0At dbFixed dbLogger; infer_instance

private instance reg_persistent_sz (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance viewOf_persistent_sz (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

/-- What `Tx.Size` reads of a transaction: its meta copy, its database and the page size. -/
theorem boltTxDef_size_acc [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (tx : Loc) (q : Qp)
    (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ∃ (m : Loc) (mv : internal.common.Meta) (db : Loc)
      (dq dq' : DFrac), tx.[Tx, go!"meta"] ↦{dq} m ∗ m ↦{dq} mv ∗ tx.[Tx, go!"db"] ↦{dq'} db ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      (tx.[Tx, go!"meta"] ↦{dq} m -∗ m ↦{dq} mv -∗ tx.[Tx, go!"db"] ↦{dq'} db -∗
        boltTxDef B N tx q T) := by
  unfold boltTxDef
  split
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    ihave #Hps : db.[DB, go!"pageSize"] ↦□ W64 4096 $$ []
    · unfold isBoltP isBoltCoreP dbFixed
      icases Hb with ⟨⟨-, -, -, -, -, ⟨$, -⟩, -⟩, -⟩
    ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
    · unfold isBoltP isBoltCoreP
      icases Hb with ⟨⟨-, -, -, $, -⟩, -⟩
    unfold wtxFrac wtxHeap txFields
    icases Hw with ⟨⟨%Hok, ⟨Hw1, Hw2, Hm, Hw4⟩, Hrest⟩, Hw'⟩
    icases Hw4 with ⟨Hw5, Hw6, Hw7, Hmv, Hw8⟩
    icases Hw' with ⟨Hf, Hvc, Hst, Hbk, Hnl, Hdb, Hrest'⟩
    iexists X.t.t.meta', X.t.mv, r.db, DFrac.own q, DFrac.own (txDbQ q)
    iframe Hm Hmv Hdb
    obtain ⟨hT, rfl, hrw⟩ := Hc
    iframe Hps Hpk
    iintro Hm Hmv Hdb
    iexists r.db, p, sp, t0, r, c, X
    iframe Hreg Hb Hv Hex
    isplitr
    · ipureintro; exact ⟨hT, rfl, hrw⟩
    iframe
    ipureintro; exact Hok
  · iintro ⟨%db', Hr, #Hb'⟩
    unfold rdTx rtxFrac
    icases Hr with ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore, Hv, Hex,
      ⟨%t, Hw, Hmg, Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hmv, Hvc, Hmap, #Hvo, %Hf⟩, Hpool⟩
    ihave #Hps : db.[DB, go!"pageSize"] ↦□ W64 4096 $$ []
    · unfold isBoltCoreP dbFixed
      icases Hcore with ⟨-, -, -, -, -, ⟨$, -⟩, -⟩
    ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
    · unfold isBoltCoreP
      icases Hcore with ⟨-, -, -, $, -⟩
    iexists t.meta', mv, r.db, DFrac.own q, DFrac.own (txDbQ q)
    iframe Hme Hmv Hdb
    obtain ⟨hT, rfl, hrw, hsrc⟩ := Hc
    iframe Hps Hpk
    iintro Hme Hmv Hdb
    iexists db'
    iframe Hb'
    iexists r.db, p, sp, t0, r, c, v, mv, k
    iframe Hreg Hcore Hv Hex Hpool
    isplitr
    · ipureintro; exact ⟨hT, rfl, hrw, hsrc⟩
    iexists t
    iframe
    iframe Hvo
    ipureintro; exact Hf

theorem Tx.Size.wp_proof (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG)) :
    Tx.Size.spec (GF := GF) (hG := hG) := by
  intro _ tx γ q T
  wp_start as Ht
  unfold boltTx
  icases boltTxDef_size_acc _ _ tx q T $$ Ht with ⟨%m, %mv, %db, %dq, %dq', Hm, Hmv, Hdb, #Hps, #Hpk, Hcl⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Pgid $$ [$Hpkg $Hmv] as Hmv
  iapply HΦ
  iapply Hcl $$ Hm Hmv Hdb

end proof

end bbolt
end EtcdGrove
end Perennial
