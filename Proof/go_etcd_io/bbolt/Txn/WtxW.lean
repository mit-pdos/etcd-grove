/-
A whole write transaction as its working state (U5 of `notes/bbolt-proof-plan.md`):
`boltTxDef_wtxW'`, the proof of `Inv/Ctx.lean`'s `boltTxDef_wtxW` (moved there once the shared
module is quiet).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section w
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

private instance isBoltP_persistent_w (B : BNs) (N : Namespace) (db : Loc) (p : GoString)
    (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance BC_full_persistent_w (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance viewOf_persistent_w (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

theorem QpMul_one_left (q : Qp) : QpMul 1 q = q :=
  Subtype.ext (by simp [QpMul])

theorem boltTxDef_wtxW' (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) (hrw : T.rw = true) :
    boltTxDef (GF := GF) B N tx 1 T ⊣⊢
      ∃ (K : BC) (r : TxReg) (c : TxViewC) (X : WX),
        ⌜K.B = B ∧ K.N = N ∧ T = TxView.ofC c⌝ ∗ K.full ∗
        ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ∗ wtxW K tx r true X ∗
        ghostVar B.st (1 : Qp).half.half T.base ∗
        ⌜wOK X ∧ T.cur = wtxData X ∧ T.base = X.v.data ∧ gensOK T X⌝ := by
  unfold boltTxDef
  simp only [hrw, ↓reduceIte]
  constructor
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    unfold wtxFrac
    simp only [QpMul_one_left]
    icases Hw with ⟨Hh, Hf, Hvc, Hst, Hbk, Hnl, Hdb, ⟨%l, Hmf, %Hl⟩, #Hvo, %Hfacts⟩
    iexists ⟨B, N, db, p, sp, t0⟩, r, c, X
    obtain ⟨hT, hdb, hrw'⟩ := Hc
    obtain ⟨h1, -, h3, h4, h5⟩ := Hfacts
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hT⟩
    unfold BC.full
    iframe Hb Hv Hst
    isplitl [Hh Hf Hvc Hbk Hnl Hdb Hex Hmf]
    · unfold wtxW wtxCore statsTok BC.core
      simp only [↓reduceIte]
      ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
      · unfold isBoltP isBoltCoreP
        icases Hb with ⟨⟨-, -, -, $, -⟩, -⟩
      ihave #Hc : isBoltCoreP B N db p sp t0 $$ []
      · unfold isBoltP; icases Hb with ⟨$, -⟩
      iframe Hpk Hc Hreg Hh Hf Hbk Hnl Hvc Hvo Hex
      iframe Hdb
      isplitr
      · ipureintro; exact ⟨hdb, hrw'⟩
      iexists l; iframe Hmf; ipureintro; exact Hl
    ipureintro; exact ⟨h1, h3, h4, h5⟩
  · iintro ⟨%K, %r, %c, %X, %HK, #Hb, Hv, Hw, Hst, %Hfacts⟩
    obtain ⟨rfl, rfl, hT⟩ := HK
    unfold wtxW wtxCore statsTok
    simp only [↓reduceIte]
    icases Hw with ⟨⟨-, -, %Hr, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, #Hvo, Hex⟩, Hvc, %l, Hmf, %Hl⟩
    iexists K.db, K.p, K.sp, K.t0, r, c, X
    isplitr
    · ipureintro; exact ⟨hT, Hr.1, Hr.2⟩
    unfold BC.full
    iframe Hreg Hb Hv Hex
    unfold wtxFrac
    simp only [QpMul_one_left]
    iframe Hh Hf Hvc Hst Hbk Hnl Hvo
    isplitl [Hdb]
    · iexact Hdb
    isplitl [Hmf]
    · iexists l; iframe Hmf; ipureintro; exact Hl
    ipureintro
    exact ⟨Hfacts.1, hrw, Hfacts.2.1, Hfacts.2.2.1, Hfacts.2.2.2⟩

end w
end bbolt
end EtcdGrove
end Perennial
