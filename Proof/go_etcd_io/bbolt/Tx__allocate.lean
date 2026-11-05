/-
The proof of `Spec/go_etcd_io/bbolt/Tx__allocate.lean`: the flagged `Tx.allocate_f.spec`
(`Proof/go_etcd_io/bbolt/Tx__allocate_f.lean`, batch 44.1) at `fr = false`.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.Tx__allocate_f

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `Tx.allocate.spec` is `Tx.allocate_f.spec` at `fr = false` (`wdbW_wdbW'`, `wdbW'_wdbW`,
`wdbLost'_wdbLost`). -/
theorem Tx.allocate.spec_of_f (h : Tx.allocate_f.spec (GF := GF) (hG := hG)) :
    Tx.allocate.spec (GF := GF) (hG := hG) := by
  intro K tx r m X w count P hc0 hc htx hhwm hdp hlf hlr
  iintro %Φ ⟨Hw, Hdb, HR⟩ HΦ
  ihave Hdb := wdbW_wdbW' false K tx X.v w $$ Hdb
  wp_apply h false K tx r m X w count P hc0 hc htx hhwm hdp hlf hlr $$ [Hw Hdb HR] as %p %err
    ⟨HR, Hres⟩
  · iframe
  iapply HΦ
  iframe HR
  icases Hres with (⟨%he, %X', %w', %id, Hw, Hdb, %hr⟩ |
    ⟨%hne, #He, (⟨Hw, Hdb⟩ | ⟨%X', %w', Hw, Hdb, %hr⟩)⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    iexists X', w', id
    iframe Hw
    isplitl [Hdb]
    · iapply wdbW'_wdbW $$ Hdb
    · ipureintro; exact hr
  · iright
    isplitr
    · ipureintro; exact hne
    iframe He
    ileft
    iframe Hw
    iapply wdbW'_wdbW $$ Hdb
  · iright
    isplitr
    · ipureintro; exact hne
    iframe He
    iright
    iexists X', w'
    iframe Hw
    isplitl [Hdb]
    · iapply wdbLost'_wdbLost $$ Hdb
    · ipureintro; exact hr

theorem Tx.allocate.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hAlloc : DB.allocate.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hCount : TxStats.IncPageCount.spec (GF := GF) (hG := hG))
    (hPAlloc : TxStats.IncPageAlloc.spec (GF := GF) (hG := hG)) :
    Tx.allocate.spec (GF := GF) (hG := hG) :=
  Tx.allocate.spec_of_f (Tx.allocate_f.wp_proof hLogger hAlloc hTxid hId hCount hPAlloc)

end proof

end bbolt
end EtcdGrove
end Perennial
