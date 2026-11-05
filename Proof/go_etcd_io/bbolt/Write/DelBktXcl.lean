/-
U7m (`notes/bbolt-proof-plan.md`): **`Tx.DeleteBucket`'s exclusive part.** `DeleteBucket` frees the
deleted bucket's pages (`child.free()`, `Bucket.free.spec` over the writer's database side `wdbW`),
so, as `Commit` and `Rollback`, it takes the writer's exclusive part out of the transactions'
invariant and runs in mode `false` (`statsTok`: the exclusive part's `done` half):
- `dbk_open`: a writer's `wtxW` (mode `true`) and its agreed state's half give, under a later, the
  working state in mode `false`, the agreed state whole, and the exclusive part's contents (the
  `rwlock`, the closed flag's half, the database side with its facts and the page tokens);
- `dbk_close`: the converse at new records `X'`, database side `w'` and view `T'`: the agreed
  state moved to `(c', X')`, the exclusive part put back with `X'`'s facts, `boltTxDef` at `T'`.
  Unlike `boltTxDef_wclose` (`Write/Retarget`) the freelist may change (`flViewU X' w'.fl`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.Retarget
public import Proof.go_etcd_io.bbolt.Tx__Rollback

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Write

section xcl
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The exclusive part's contents but the agreed state and the `done` half, as `DeleteBucket`
holds them: the `rwlock`, the closed flag's half, the database side `w` on `X`'s view with the
page tokens and `w`'s facts. -/
def dbkXcl (K : BC) (tx : Loc) (r : TxReg) (X : WX) : IProp GF :=
  iprop(sync.ownMutex K.db.[DB, go!"rwlock"] ∗ ghostVar K.B.cls (1 : Qp).half false ∗
    ∃ (w : WDb) (extra : GMap Nat Unit), wdbW K tx X.v w ∗ txShape r.n.pg X extra ∗
      ⌜flViewU X w.fl ∧ metaCopyOK X.t.mv w.C ∧ treeOK w.C⌝)

/-- **The exclusive part taken out** (`txExcl_take`, `txExclWGap_holds`). -/
theorem dbk_open (K : BC) (tx : Loc) (r : TxReg) (X : WX) (c : TxViewC) :
    wtxW (GF := GF) K tx r true X ∗ ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ⊢
      |={⊤}=> ▷ (wtxW K tx r false X ∗ ghostVar r.n.v 1 (c, TxX.wr X) ∗ dbkXcl K tx r X) := by
  iintro ⟨Hw, Hv⟩
  iunfold wtxW at Hw
  icases Hw with ⟨Hcore, Hvc, Hmf⟩
  iunfold wtxCore at Hcore
  icases Hcore with ⟨#Hpkg, #Hkc, %Hc, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, #Hvo, Hstok⟩
  simp only [statsTok, ↓reduceIte]
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨#Hdbl, #Ht0, %Ht0, -, #Hos, #Hfix, #Hml, #Hmm, #Hsl, #Hpi, #Hti⟩
  imod txExcl_take K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hti Hreg Hstok] with Hx
  · iframe; iframe #
  imodintro
  inext
  ihave Hg := txExclWGap_holds K tx r X c Hc.1 $$ [Hx Hv]
  · iframe
  icases Hg with ⟨Hv, Hd, Hrwl, Hcls, Hg⟩
  iframe Hv
  isplitr [Hrwl Hcls Hg]
  · unfold wtxW wtxCore statsTok
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iframe #
    ipureintro; exact Hc
  unfold dbkXcl
  iframe

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos package_sem in
private theorem QpMul_one_left_dx (q : Qp) : QpMul 1 q = q :=
  Subtype.ext (by simp [QpMul])

omit package_sem in
private instance viewOf_persistent_dx (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

omit package_sem in
private instance BC_full_persistent_dx (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

omit package_sem in
/-- **The exclusive part put back** at `X'` (database side `w'`), `boltTxDef` closed at `T'`. -/
theorem dbk_close (K : BC) (tx : Loc) (r : TxReg) (c c' : TxViewC) (X X' : WX) (w' : WDb)
    (extra : GMap Nat Unit) (T' : TxView) (hT : T' = TxView.ofC c')
    (hf : wOK X' ∧ T'.rw = true ∧ T'.cur = wtxData X' ∧ T'.base = X'.v.data ∧ gensOK T' X' ∧
      wrFacts X')
    (hx : flViewU X' w'.fl ∧ metaCopyOK X'.t.mv w'.C ∧ treeOK w'.C) :
    K.full (GF := GF) ∗ viewOf r X'.v ∗ ghostVar r.n.v 1 (c, TxX.wr X) ∗ wtxW K tx r false X' ∗
        sync.ownMutex K.db.[DB, go!"rwlock"] ∗ ghostVar K.B.cls (1 : Qp).half false ∗
        wdbW K tx X'.v w' ∗ txShape r.n.pg X' extra ∗ ghostVar K.B.st (1 : Qp).half.half T'.base ⊢
      |={⊤}=> boltTxDef K.B K.N tx 1 T' := by
  iintro ⟨#Hb, #Hvf, Hv, Hw, Hrwl, Hcls, Hwdb, Hshape, Hst⟩
  unfold wtxW wtxCore statsTok
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hw with ⟨⟨-, -, %Hr, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, #Hvo, Hd⟩, Hvc, %l, Hmf, %Hl⟩
  ihave Hu := ghostVar_update (c', TxX.wr X') r.n.v (c, TxX.wr X) $$ Hv
  imod Hu with Hv
  icases (ghostVar_split_half r.n.v 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  ihave #Hinv : inv (txsN K.N) (txsInv (GF := GF) K.B K.p K.sp K.t0) $$ []
  · unfold BC.full isBoltP isBoltCoreP
    icases Hb with ⟨⟨-, -, -, -, -, -, -, -, -, -, $⟩, -⟩
  ihave Hx : txExcl (GF := GF) K.B K.p K.sp K.t0 tx r $$ [Hv1 Hd Hrwl Hcls Hwdb Hshape]
  · iunfold txExcl
    iexists c', TxX.wr X'
    dsimp only
    iframe Hv1 Hd
    rw [Hr.1]
    iframe Hrwl Hcls
    iexists w', extra
    unfold wdbW
    icases Hwdb with ⟨Hlive, %Hwok⟩
    iframe Hlive Hshape
    ipureintro; exact ⟨Hwok.1, Hwok.2.1, Hwok.2.2, hx.1, hx.2.1, hx.2.2⟩
  imod txExcl_put K.B K.N K.p K.sp K.t0 ⊤ CoPset.subseteq_top tx r $$ [Hx] with Hex
  · iframe; iframe #
  imodintro
  unfold boltTxDef
  simp only [hf.2.1, ↓reduceIte]
  iexists K.db, K.p, K.sp, K.t0, r, c', X'
  isplitr
  · ipureintro; exact ⟨hT, Hr.1, Hr.2.1⟩
  unfold BC.full
  iframe Hreg Hb Hv2 Hex
  unfold wtxFrac
  simp only [QpMul_one_left_dx]
  iframe Hh Hf Hvc Hst Hbk Hnl
  isplitl [Hdb]
  · iexact Hdb
  isplitl [Hmf]
  · iexists l; iframe Hmf; ipureintro; exact Hl
  isplitr
  · unfold viewW; iframe #
  ipureintro
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, Hr.2.2.1, Hr.2.2.2.1,
    Hr.2.2.2.2.1, Hr.2.2.2.2.2, hf.2.2.2.2.2⟩

end xcl

end Write

end bbolt
end EtcdGrove
end Perennial
