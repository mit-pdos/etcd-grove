/-
`Inv/Tx`'s `boltTxDef_fill` (the law behind `Api.lean`'s `boltTx_fill`), proved with the same
statement, for the maintainer to move into `Inv/Tx` (replacing its `sorry`) with the next change
that rebuilds `Inv/Tx`'s importers anyway: replacing a `sorry` by a proof changes `Inv/Tx`'s public
`.olean` (the `sorry` version's mentions `sorryAx`), so moving it in stales its 719 importers.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Iris.ProofMode in
/-- **`Inv/Tx`'s `boltTxDef_fill`, proved** (same statement; `Api.lean`'s `boltTx_fill`): the
handle's registry fragment against `hdlAuth` puts it in `X.handles`, so its points-to is in
`fills`, given back with any non-NaN value. -/
theorem boltTxDef_fill_pf (B : BNs) (N : Namespace) (tx b : Loc) (T : TxView) (n : GoString)
    (g : Nat) (hrw : T.rw = true) :
    boltTxDef (GF := GF) B N tx 1 T ∗ boltBktDef B tx b n g ⊢
      ∃ f : w64, b.[Bucket, go!"FillPercent"] ↦ f ∗
        (∀ f' : w64, ⌜¬ float64IsNaN f'⌝ -∗ b.[Bucket, go!"FillPercent"] ↦ f' -∗
          boltTxDef B N tx 1 T) := by
  unfold boltTxDef boltBktDef reg
  simp only [hrw, ↓reduceIte]
  iintro ⟨⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, Hb, Hv, Hex, Hw⟩,
    ⟨%r', #Hreg', -, Hh', -⟩⟩
  icombine Hreg Hreg' gives %hr
  obtain ⟨-, rfl⟩ := hr
  unfold handleFrag
  rw [if_pos Hc.2.2]
  unfold wtxFrac hdlAuth
  icases Hw with ⟨Hheap, Hfills, Hcells, Hst, ⟨Hbk, #Hf⟩, Hrest⟩
  ihave %Hl := ghost_map_lookup $$ Hbk Hh'
  unfold fills
  icases (BigSepM.bigSepM_lookup_acc Hl).1 $$ Hfills with ⟨⟨%f, %Hnan, Hfp⟩, Hfb⟩
  iexists f
  iframe Hfp
  iintro %f' %Hnan' Hfp
  iexists db, p, sp, t0, r, c, X
  isplitr
  · ipureintro; exact Hc
  isplitr
  · iexact Hreg
  iframe Hb Hv Hex Hheap Hcells Hst Hbk Hrest
  isplitl [Hfb Hfp]
  · iapply Hfb
    iexists f'; iframe Hfp; ipureintro; exact Hnan'
  iexact Hf

end tx

end bbolt
end EtcdGrove
end Perennial
