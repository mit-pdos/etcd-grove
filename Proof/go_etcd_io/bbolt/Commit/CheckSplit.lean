/-
A reader split in halves, and its root bucket next to it (U10e of `notes/bbolt-proof-plan.md`:
`recursivelyCheckBucket(&tx.root, …)` runs `ForEachBucket` on the root bucket, whose spec takes the
reader and the bucket side by side). Uses `Inv/Tx`'s private `rtxFrac_fractional`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx
import all Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section split
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A reader in halves.** -/
theorem rdTxK_halves (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊣⊢ rdTxK K tx src q.half T v ∗ rdTxK K tx src q.half T v := by
  constructor
  · unfold rdTxK
    iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex, Hw, Hpool⟩
    icases (ghostVar_split_half r.n.v q.half (c, TxX.rd v mv k)).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases (ghostVar_split_half r.n.ex q ()).1 $$ Hex with ⟨He1, He2⟩
    have hf := (rtxFrac_fractional (GF := GF) K.B tx r T v mv).fractional q.half q.half
    rw [Qp.half_add_half] at hf
    icases hf.1 $$ Hw with ⟨Hw1, Hw2⟩
    ihave Hp2 : (if src = .loan then threadPool.isThreadPool (poolN K.N) K.B.pool
        (rdPair (GF := GF) K.B K.db K.sp) else ghostVar K.B.spr q.half.half (some k)) ∗
        (if src = .loan then threadPool.isThreadPool (poolN K.N) K.B.pool
        (rdPair (GF := GF) K.B K.db K.sp) else ghostVar K.B.spr q.half.half (some k)) $$ [Hpool]
    · by_cases hs : src = .loan
      · simp only [hs, ↓reduceIte]
        icases Hpool with #Hpool
        iframe #
      · simp only [hs, ↓reduceIte]
        iapply (ghostVar_split_half K.B.spr q.half (some k)).1; iexact Hpool
    icases Hp2 with ⟨Hp1, Hp2⟩
    isplitl [Hv1 He1 Hw1 Hp1]
    · iexists r, c, mv, k; iframe; iframe #; ipureintro; exact Hc
    · iexists r, c, mv, k; iframe; iframe #; ipureintro; exact Hc
  · unfold rdTxK
    iintro ⟨⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex, Hw, Hpool⟩,
      ⟨%r2, %c2, %mv2, %k2, %Hc2, #Hreg2, -, -, Hv2, Hex2, Hw2, Hpool2⟩⟩
    iunfold reg at Hreg Hreg2
    icombine Hreg Hreg2 gives %hr
    obtain ⟨-, rfl⟩ := hr
    icombine Hv Hv2 gives %hv
    obtain ⟨-, hv⟩ := hv
    simp only [Prod.mk.injEq, TxX.rd.injEq] at hv
    obtain ⟨rfl, -, rfl, rfl⟩ := hv
    iexists r, c, mv, k
    isplitr
    · ipureintro; exact Hc
    iframe Hpk Hcore
    isplitr
    · iunfold reg; iexact Hreg

    have hf := (rtxFrac_fractional (GF := GF) K.B tx r T v mv).fractional q.half q.half
    rw [Qp.half_add_half] at hf
    isplitl [Hv Hv2]
    · iapply (ghostVar_split_half r.n.v q.half (c, TxX.rd v mv k)).2; iframe
    isplitl [Hex Hex2]
    · iapply (ghostVar_split_half r.n.ex q ()).2; iframe
    isplitl [Hw Hw2]
    · iapply hf.2; iframe
    by_cases hs : src = .loan
    · simp only [hs, ↓reduceIte]
      iexact Hpool
    · simp only [hs, ↓reduceIte]
      iapply (ghostVar_split_half K.B.spr q.half (some k)).2; iframe

/-- **A reader and its root bucket side by side** (half of each), and back. -/
theorem rdTxK_root_split (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ ibp pp : Loc, rdTxK K tx src q.half T v ∗
      rBktP v tx (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp ∗
      (rdTxK K tx src q.half T v -∗
        rBktP v tx (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp -∗
        rdTxK K tx src q T v) := by
  iintro Hk
  icases (rdTxK_halves K tx src q T v).1 $$ Hk with ⟨Hk1, Hk2⟩
  icases rdTxK_root K tx src q.half T v $$ Hk2 with ⟨Hb, Hback⟩
  rw [rBkt_eq]
  icases Hb with ⟨%ibp, %pp, Hb⟩
  iexists ibp, pp
  iframe Hk1 Hb
  iintro Hk1 Hb
  ihave Hk2 := Hback $$ [Hb]
  · iexists ibp, pp; iexact Hb
  iapply (rdTxK_halves K tx src q T v).2
  iframe

end split

end bbolt
end EtcdGrove
end Perennial
