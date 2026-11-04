/-
The `statlock` reader token a `DB.Stats` caller pays with (`statSlot`, U5 of
`notes/bbolt-proof-plan.md`): a pool loan for its `threadTok`, or its whole read transaction's
own token (taken from the transaction's exclusive part in `txsInv`).
-/
module

public import Proof.go_etcd_io.bbolt.Txn.Txs
public import Proof.go_etcd_io.bbolt.Inv.Tx
public import Perennial.Proof.sync.Results
public import Spec.go_etcd_io.bbolt.Api
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

private instance reg_persistent_slot (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

instance isBoltP_persistent' (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

/-- **The caller's `statlock` reader token** (`DB.Stats`): with the database `db` of `γ` at its
statistics pointer `sp`, the token (after a step) and its way back. -/
theorem statSlot_tok (db : Loc) (γ : BoltName) (o : Option (Loc × Data)) (p : GoString) (sp : Loc)
    (t0 : Nat) :
    isBoltP (GF := GF) (bnsOf γ.gs) γ.ns db p sp t0 ∗ statSlot γ o ⊢
    |={⊤}=> ▷ (sync.ownRWMutex db.[DB, go!"statlock"] (Ps sp) ∗
      (sync.ownRWMutex db.[DB, go!"statlock"] (Ps sp) ={⊤}=∗ statSlot γ o)) := by
  iintro ⟨#Hb, Hslot⟩
  rcases o with _ | ⟨tx, D⟩
  · unfold statSlot
    unfold isBoltP
    icases Hb with ⟨-, -, #Hpool⟩
    imod threadPool.borrow (poolN γ.ns) _ _ ⊤ CoPset.subseteq_top $$ [Hpool Hslot] with ⟨Hpair, Hloan⟩
    · iframe Hpool Hslot
    imodintro
    inext
    unfold rdPair
    icases Hpair with ⟨Hm, Hs⟩
    iframe Hs
    iintro Hs
    iapply threadPool.giveBack (poolN γ.ns) _ _ ⊤ CoPset.subseteq_top
    iframe Hpool Hloan Hm Hs
  · unfold statSlot boltTx boltTxDef
    have hro : (TxView.ro D).rw = false := rfl
    simp only [hro, Bool.false_eq_true, ↓reduceIte]
    icases Hslot with ⟨%db', Hrd, #Hb'⟩
    unfold rdTx
    icases Hrd with ⟨%db1, %p1, %sp1, %t01, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore1, Hv, Hex, Hrt,
      Hpool1⟩
    ihave %hdb : ⌜db = db1⌝ $$ []
    · iapply isBolt_db_agree (bnsOf γ.gs) γ.ns db db1
      isplitl
      · unfold isBoltDef; iexists p, sp, t0; iexact Hb
      · unfold isBoltCore; iexists p1, sp1, t01; iexact Hcore1
    subst hdb
    ihave %hag := isBoltP_agree _ _ db p p1 sp sp1 t0 t01 $$ [Hb Hcore1]
    · iframe Hb Hcore1
    obtain ⟨rfl, rfl⟩ := hag
    obtain ⟨hT, hrdb, hrw, hsrc⟩ := Hc
    ihave #Hinv1 : inv (txsN γ.ns) (txsInv (GF := GF) (bnsOf γ.gs) p1 sp t0) $$ []
    · unfold isBoltCoreP
      icases Hcore1 with ⟨-, -, -, -, -, -, -, -, -, -, $⟩
    imod txExcl_take (bnsOf γ.gs) γ.ns p1 sp t0 ⊤ CoPset.subseteq_top tx r $$ [Hex] with Hx
    · iframe Hinv1 Hreg Hex
    imodintro
    inext
    unfold txExcl
    icases Hx with ⟨%c', %x, Hv', Hd, Hx⟩
    icombine Hv Hv' gives %hv
    obtain ⟨-, hv⟩ := hv
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
    icases Hx with ⟨Hmm, Hloan, Hst, Hk⟩
    subst hrdb
    iframe Hst
    iintro Hst
    imod txExcl_put' (bnsOf γ.gs) γ.ns p1 sp t0 ⊤ CoPset.subseteq_top tx r $$ [Hv' Hd Hmm Hloan Hst Hk]
      with Hex
    · iframe Hinv1 Hreg
      unfold txExcl
      iexists c, (TxX.rd v mv k)
      iframe Hv' Hd
      dsimp only
      iframe Hmm Hloan Hst Hk
    imodintro
    iexists db'
    iframe Hb'
    iexists r.db, p1, sp, t0, r, c, v, mv, k
    iframe Hreg Hcore1 Hv Hex Hrt Hpool1
    ipureintro; exact ⟨hT, rfl, hrw, hsrc⟩

end slot
end bbolt
end EtcdGrove
end Perennial
