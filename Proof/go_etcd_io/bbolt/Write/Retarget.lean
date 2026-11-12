/-
**A writer's operation that changes its records `X` to `X'`, closed back into `boltTx`** (U7h, the
review's U1): the agreed state's two halves (one in `boltTx`, one in the exclusive part `txExcl`,
inside the transactions' invariant) both move to `(c', X')`, and the exclusive part's copy of the
records' facts (`txShape`, `flViewU`, the view and the meta copy) is re-established for `X'`.

- `txExcl_retarget`: the exclusive part, retargeted (an update, given the facts' preservation);
- `boltTxDef_wclose`: the inverse of `boltTxDef_wtxW` for new records `X'` and view `T'`, opening
  the transactions' invariant with the writer's whole `ex` token.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section retarget
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **What the exclusive part keeps of the records** from `X` to `X'`: the base view and the meta
copy unchanged, the freelist's agreement (`flViewU`) and the page tokens (`txShape`) kept. -/
structure XclKeep (X X' : WX) : Prop where
  v : X'.v = X.v
  mv : X'.t.mv = X.t.mv
  fl : ∀ fl, flViewU X fl → flViewU X' fl

/-- **The exclusive part, retargeted** to the records `X'` and the view `c'` (both halves of the
agreed state updated). -/
theorem txExcl_retarget (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (r : TxReg)
    (c c' : TxViewC) (X X' : WX) (E : CoPset) (hk : XclKeep X X')
    (hsh : ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra) :
    txExcl (GF := GF) B p sp t0 tx r ∗ ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ⊢
      |={E}=> txExcl B p sp t0 tx r ∗ ghostVar r.n.v (1 : Qp).half (c', TxX.wr X') := by
  iintro ⟨Hx, Hv⟩
  iunfold txExcl at Hx
  icases Hx with ⟨%c0, %x, Hv', Hd, Hx⟩
  icombine Hv' Hv gives % ⟨_, hx⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  icases Hx with ⟨Hrwl, Hcls, %w, %extra, Hlive, Hshape, %Hok⟩
  ihave Hu := ghostVar_update_halves (c', TxX.wr X') r.n.v _ _ $$ Hv' Hv
  imod Hu
  icases Hu with ⟨Hv', Hv⟩
  ihave Hshape := hsh extra $$ Hshape
  imodintro
  iframe Hv
  iunfold txExcl
  iexists c', TxX.wr X'
  dsimp only
  iframe Hv' Hd Hrwl Hcls
  iexists w, extra
  rw [hk.v, hk.mv]
  iframe Hlive Hshape
  ipureintro
  exact ⟨Hok.1, Hok.2.1, Hok.2.2.1, hk.fl _ (by rw [← hk.v] at Hok; exact Hok.2.2.2.1),
    Hok.2.2.2.2⟩

private instance txX_inhabited_rt : Inhabited TxX := ⟨TxX.rd default (zeroValDef) 0⟩

/-- The writer branch of `txExcl` (its body after the agreed state and the `done` half), kept from
`X` to `X'`. -/
theorem txExcl_wbody_keep (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc) (r : TxReg)
    (X X' : WX) (hk : XclKeep X X')
    (hsh : ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra) :
    iprop(sync.ownMutex r.db.[DB, go!"rwlock"] ∗ ghostVar B.cls (1 : Qp).half false ∗
        ∃ (w : WDb) (extra : GMap Nat Unit),
          wdbLive B r.db p sp t0 tx (wLive X.v w.C) w ∗ txShape (GF := GF) r.n.pg X extra ∗
          ⌜wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C ∧
            flViewU X w.fl ∧ metaCopyOK X.t.mv w.C ∧ treeOK w.C⌝) ⊢
      iprop(sync.ownMutex r.db.[DB, go!"rwlock"] ∗ ghostVar B.cls (1 : Qp).half false ∗
        ∃ (w : WDb) (extra : GMap Nat Unit),
          wdbLive B r.db p sp t0 tx (wLive X'.v w.C) w ∗ txShape r.n.pg X' extra ∗
          ⌜wdbOK w ∧ w.ms = some (X'.v.base, mapLen w.ms) ∧ X'.v = View.ofC X'.v.base w.C ∧
            flViewU X' w.fl ∧ metaCopyOK X'.t.mv w.C ∧ treeOK w.C⌝) := by
  iintro ⟨Hrwl, Hcls, %w, %extra, Hlive, Hshape, %Hok⟩
  ihave Hshape := hsh extra $$ Hshape
  iframe Hrwl Hcls
  iexists w, extra
  rw [hk.v, hk.mv]
  iframe Hlive Hshape
  ipureintro
  exact ⟨Hok.1, Hok.2.1, Hok.2.2.1, hk.fl _ (by rw [← hk.v] at Hok; exact Hok.2.2.2.1),
    Hok.2.2.2.2⟩

/-- **`txExcl_retarget` under the later** `txExcl_take` leaves the exclusive part at (it is not
timeless: `wdbLive`). -/
theorem txExcl_retarget_later (B : BNs) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc)
    (r : TxReg) (c c' : TxViewC) (X X' : WX) (E : CoPset) (hk : XclKeep X X')
    (hsh : ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra) :
    ▷ txExcl (GF := GF) B p sp t0 tx r ∗ ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ⊢
      |={E}=> ▷ txExcl B p sp t0 tx r ∗ ghostVar r.n.v (1 : Qp).half (c', TxX.wr X') := by
  iintro ⟨Hx, Hv⟩
  iunfold txExcl at Hx
  icases Hx with ⟨%c0, %x, >Hv', >Hd, Hx⟩
  icombine Hv' Hv gives % ⟨_, hx⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  ihave Hx := later_mono (txExcl_wbody_keep B p sp t0 tx r X X' hk hsh) $$ Hx
  ihave Hu := ghostVar_update_halves (c', TxX.wr X') r.n.v _ _ $$ Hv' Hv
  imod Hu
  icases Hu with ⟨Hv', Hv⟩
  imodintro
  iframe Hv
  inext
  iunfold txExcl
  iexists c', TxX.wr X'
  dsimp only
  iframe Hv' Hd Hx

/-- Open `txsInv` at a registered transaction's entry (`Inv/Txs`' private `txs_open_i`). -/
theorem txs_open_rt (B : BNs) (N : Namespace) (p : GoString) (sp : Loc) (t0 : Nat) (E : CoPset)
    (hE : ↑(txsN N) ⊆ E) (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ⊢
    |={E, E \ ↑(txsN N)}=> ▷ txEntry B p sp t0 tx r ∗
      (▷ txEntry B p sp t0 tx r ={E \ ↑(txsN N), E}=∗ True) := by
  iintro ⟨#Hinv, #Hreg⟩
  iinv Hinv with Hi Hclose
  unfold txsInv
  icases Hi with ⟨%M, >Hauth, Hm⟩
  unfold reg
  icombine Hauth Hreg gives %Hlk
  ihave Hm := (later_mono (BigSepM.bigSepM_lookup_acc
    (Φ := fun tx r => txEntry (GF := GF) B p sp t0 tx r) Hlk).1) $$ Hm
  icases Hm with ⟨He, Hback⟩
  imodintro
  iframe He
  iintro He
  imod Hclose $$ [Hauth Hback He] with -
  · inext
    iexists M
    iframe Hauth
    iapply Hback $$ He
  imodintro; itrivial

/-- **The exclusive part goes back under a later** (`txExcl_put` for `▷ txExcl`), for the whole
`ex` token. -/
theorem txExcl_put_later (B : BNs) (N : Namespace) (p : GoString) (sp : Loc) (t0 : Nat)
    (E : CoPset) (hE : ↑(txsN N) ⊆ E) (tx : Loc) (r : TxReg) :
    inv (txsN N) (txsInv (GF := GF) B p sp t0) ∗ reg tx B r ∗ ▷ txExcl B p sp t0 tx r ⊢
    |={E}=> ghostVar r.n.ex 1 () := by
  iintro ⟨#Hinv, #Hreg, Hx⟩
  imod txs_open_rt B N p sp t0 E hE tx r $$ [] with ⟨He, Hcl⟩
  · iframe Hinv Hreg
  unfold txEntry
  icases He with (⟨Hdb, >Hdone, Hst, (Hx' | >Hex), Hrh⟩ | ⟨>Hdone, >Hex, -⟩)
  · iunfold txExcl at Hx
    icases Hx with ⟨%c, %x, -, >Hd1, -⟩
    icombine Hdone Hd1 as Hd
    iunfold txExcl at Hx'
    icases Hx' with ⟨%c', %x', -, >Hd2, -⟩
    icombine Hd Hd2 gives %h
    exact absurd h.1 (by rw [Qp.le_iff]; simp; grind)
  · imod Hcl $$ [Hdb Hdone Hst Hx Hrh] with -
    · inext; ileft; iframe Hdb Hdone Hst Hrh
      ileft; iexact Hx
    imodintro; iexact Hex
  · iunfold txExcl at Hx
    icases Hx with ⟨%c, %x, -, >Hd1, -⟩
    icombine Hdone Hd1 gives %h
    exact absurd h.2 (by decide)

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos in
private theorem QpMul_one_left_rt (q : Qp) : QpMul 1 q = q :=
  Subtype.ext (by simp [QpMul])

private instance BC_full_persistent_rt (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance viewOf_persistent_rt (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

/-- **A writer's records `X'` closed back into `boltTx` at the view `T'`** (the inverse of
`boltTxDef_wtxW`): from the agreed state's half at the old `(c, X)`, the working state at `X'`
and its fixed view (`viewOf`, U6w's F2: `boltTxDef_wtxW` gives it at `X.v = X'.v`), the committed
data's quarter, `X'`'s facts for `T'`, and what the exclusive part keeps
(`XclKeep`, `txShape`). -/
theorem boltTxDef_wclose (K : BC) (tx : Loc) (r : TxReg) (c c' : TxViewC) (X X' : WX)
    (T' : TxView) (E : CoPset) (hE : ↑(txsN K.N) ⊆ E) (hT : T' = TxView.ofC c')
    (hk : XclKeep X X')
    (hsh : ∀ extra, txShape (GF := GF) r.n.pg X extra ⊢ txShape r.n.pg X' extra)
    (hf : wOK X' ∧ T'.rw = true ∧ T'.cur = wtxData X' ∧ T'.base = X'.v.data ∧ gensOK T' X' ∧
      wrFacts X' ∧ wrCurFacts T' X') :
    K.full (GF := GF) ∗ viewOf r X'.v ∗ ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ∗
        wtxW K tx r true X' ∗ ghostVar K.B.st (1 : Qp).half.half T'.base ⊢
      |={E}=> boltTxDef K.B K.N tx 1 T' := by
  iintro ⟨#Hb, #Hvf, Hv, Hw, Hst⟩
  unfold wtxW wtxCore statsTok
  simp only [↓reduceIte]
  icases Hw with ⟨⟨-, -, %Hr, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, #Hvo, Hex⟩, Hvc, %l, Hmf, %Hl⟩
  ihave #Hinv : inv (txsN K.N) (txsInv (GF := GF) K.B K.p K.sp K.t0) $$ []
  · unfold BC.full isBoltP isBoltCoreP
    icases Hb with ⟨⟨-, -, -, -, -, -, -, -, -, -, $⟩, -⟩
  imod txExcl_take K.B K.N K.p K.sp K.t0 E hE tx r $$ [Hex] with Hx
  · iframe; iframe #
  imod txExcl_retarget_later K.B K.p K.sp K.t0 tx r c c' X X' E hk hsh $$ [Hx Hv] with ⟨Hx, Hv⟩
  · iframe
  imod txExcl_put_later K.B K.N K.p K.sp K.t0 E hE tx r $$ [Hx] with Hex
  · iframe; iframe #
  imodintro
  unfold boltTxDef
  simp only [hf.2.1, ↓reduceIte]
  iexists K.db, K.p, K.sp, K.t0, r, c', X'
  isplitr
  · ipureintro; exact ⟨hT, Hr.1, Hr.2.1⟩
  unfold BC.full
  iframe Hreg Hb Hv Hex
  unfold wtxFrac
  simp only [QpMul_one_left_rt]
  iframe Hh Hf Hvc Hst Hbk Hnl
  isplitl [Hdb]
  · iexact Hdb
  isplitl [Hmf]
  · iexists l; iframe Hmf; ipureintro; exact Hl
  isplitr
  · unfold viewW; iframe #
  ipureintro
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, Hr.2.2.1, Hr.2.2.2.1,
    Hr.2.2.2.2.1, Hr.2.2.2.2.2, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2⟩

end retarget

end bbolt
end EtcdGrove
end Perennial
