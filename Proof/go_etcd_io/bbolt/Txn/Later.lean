/-
`boltTxDef_later` (U5 of `notes/bbolt-proof-plan.md`, D-A): a transaction's timeless parts survive
a later; its database's invariants and locks (not timeless) come from `isBoltDef`, whose location
agrees with the transaction's by `dblAt` (timeless).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section later
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

private instance ite_timeless_l {c : Prop} [Decidable c] (P Q : IProp GF) [Timeless P]
    [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance

private instance mapFields_timeless_l (db : Loc) (dq : DFrac) (ms : MapSt) :
    Timeless (mapFields (GF := GF) db dq ms) := by
  unfold mapFields; split <;> infer_instance

private instance viewCells_timeless_l (q : Qp) (v : View) : Timeless (viewCells (GF := GF) q v) := by
  unfold viewCells; infer_instance

private instance rBkt_timeless_l (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) :
    Timeless (rBkt (GF := GF) v tx b dq bv) := by
  unfold rBkt locOwn; infer_instance

private instance rtxFrac_timeless_l (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView)
    (v : View) (mv : Meta) : Timeless (rtxFrac (GF := GF) B tx r q T v mv) := by
  unfold rtxFrac viewOf; infer_instance

private instance reg_timeless_l (tx : Loc) (B : BNs) (r : TxReg) :
    Timeless (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance reg_persistent_l (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance isBoltP_persistent_l (B : BNs) (N : Namespace) (db : Loc) (p : GoString)
    (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance dblAt_timeless_l (B : BNs) (db : Loc) : Timeless (dblAt (GF := GF) B db) := by
  unfold dblAt; infer_instance

private instance dblAt_persistent_l (B : BNs) (db : Loc) : Persistent (dblAt (GF := GF) B db) := by
  unfold dblAt; infer_instance

private instance ownSliceCap_timeless_l (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (dq : DFrac) : Timeless (ownSliceCap (GF := GF) V s dq) := by
  rw [ownSliceCap_unseal]; unfold ownSliceCapDef; infer_instance

private instance srcOwn_timeless_l (v : View) (s : GoSlice) (src : Src) (bs : List w8) :
    Timeless (srcOwn (GF := GF) v s src bs) := by
  unfold srcOwn; split <;> infer_instance

private instance wOwn_timeless_l (v : View) (live : Bool) (it : Inode) (w : WEntry) :
    Timeless (wOwn (GF := GF) v live it w) := by
  unfold wOwn; infer_instance

private instance pageOwn_timeless_l (v : View) (B : BRec) : Timeless (pageOwn (GF := GF) v B) := by
  unfold pageOwn; split
  · infer_instance
  · split <;> infer_instance

private instance objOwn_timeless_l (v : View) (l : Loc) (dq : DFrac) (b : Bool) (o : WObj) :
    Timeless (objOwn (GF := GF) v l dq b o) := by
  cases b <;> cases o <;> unfold objOwn <;> infer_instance

private instance wtxHeap_timeless_l (tx : Loc) (dq : DFrac) (X : WX) :
    Timeless (wtxHeap (GF := GF) tx dq X) := by
  unfold wtxHeap txFields rootFill; infer_instance

private instance fills_timeless_l (H : GMap Loc (GoString × Nat)) (dq : DFrac) :
    Timeless (fills (GF := GF) H dq) := by
  unfold fills; infer_instance

private instance wtxFrac_timeless_l (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView)
    (X : WX) : Timeless (wtxFrac (GF := GF) B tx r q T X) := by
  unfold wtxFrac viewOf; infer_instance

theorem boltTxDef_later' (B : BNs) (N : Namespace) (db tx : Loc) (q : Qp) (T : TxView) :
    isBoltDef (GF := GF) B N db ⊢ ▷ boltTxDef B N tx q T -∗ ◇ boltTxDef B N tx q T := by
  iintro #Hdb Ht
  ihave #Hdb' := Hdb
  unfold isBoltDef
  icases Hdb' with ⟨%p, %sp, %t0, #HbP⟩
  unfold boltTxDef
  split
  · icases Ht with ⟨%db1, %p1, %sp1, %t01, %r, %c, Ht⟩
    imod (later_exists_except0 (PROP := IProp GF)) $$ Ht with ⟨%X, Ht⟩
    icases Ht with ⟨>%Hc, >#Hreg, Hb1, >Hv, >Hex, >Hw⟩
    ihave >#Hdbl1 : ▷ dblAt B db1 $$ [Hb1]
    · inext; unfold isBoltP isBoltCoreP; icases Hb1 with ⟨⟨$, -⟩, -⟩
    ihave #Hdbl : dblAt B db $$ []
    · unfold isBoltP isBoltCoreP; icases HbP with ⟨⟨$, -⟩, -⟩
    unfold dblAt
    icombine Hdbl Hdbl1 gives %hd
    obtain ⟨-, rfl⟩ := hd
    imodintro
    iexists db, p, sp, t0, r, c, X
    isplitr
    · ipureintro; exact Hc
    iframe Hreg HbP
    iframe
  · icases Ht with ⟨%db', Hr, -⟩
    unfold rdTx
    icases Hr with ⟨%db1, %p1, %sp1, %t01, %r, %c, %v, Hr⟩
    imod (later_exists_except0 (PROP := IProp GF)) $$ Hr with ⟨%mv, Hr⟩
    imod (later_exists_except0 (PROP := IProp GF)) $$ Hr with ⟨%k, Hr⟩
    icases Hr with ⟨>%Hc, >#Hreg, Hc1, >Hv, >Hex, >Hrt, -⟩
    ihave >#Hdbl1 : ▷ dblAt B db1 $$ [Hc1]
    · inext; unfold isBoltCoreP; icases Hc1 with ⟨$, -⟩
    ihave #Hdbl : dblAt B db $$ []
    · unfold isBoltP isBoltCoreP; icases HbP with ⟨⟨$, -⟩, -⟩
    unfold dblAt
    icombine Hdbl Hdbl1 gives %hd
    obtain ⟨-, rfl⟩ := hd
    imodintro
    iexists db
    isplitl [Hv Hex Hrt]
    rotate_left
    · unfold isBoltDef; iexists p, sp, t0; iexact HbP
    iexists db, p, sp, t0, r, c, v, mv, k
    iframe
    isplitr
    · ipureintro; exact Hc
    unfold isBoltP
    icases HbP with ⟨#Hcore, -, #Hpool⟩
    iframe Hcore
    simp only [↓reduceIte]
    iframe Hreg Hpool

end later

end bbolt
end EtcdGrove
end Perennial
