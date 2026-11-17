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

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

private instance reg_persistent_slot (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

instance isBoltP_persistent' (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc)
    (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

/-- **The caller's `statlock` reader token** (`DB.Stats`): with the database `db` of `γ` at its
statistics pointer `sp`, the token (after a step) and its way back. -/
theorem statSlot_tok (db : Loc) (γ : BoltName) (o : Option (Loc × TxView)) (p : BFile) (sp : Loc)
    (t0 : Nat) :
    isBoltP (GF := GF) (bnsOf γ.gs) γ.ns db p sp t0 ∗ statSlot γ o ⊢
    |={⊤}=> ▷ (sync.ownRWMutex db.[DB, go!"statlock"] (Ps sp) ∗
      (sync.ownRWMutex db.[DB, go!"statlock"] (Ps sp) ={⊤}=∗ statSlot γ o)) := by
  iintro ⟨#Hb, Hslot⟩
  rcases o with _ | ⟨tx, T⟩
  · unfold statSlot
    unfold isBoltP
    icases Hb with ⟨-, -, #Hpool, -⟩
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
  · sorry -- S1a (branch `bbolt-api-adds`: `statSlot` of any transaction; until it lands)

end slot
end bbolt
end EtcdGrove
end Perennial
