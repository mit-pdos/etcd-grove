/-
**`Commit`'s tail over the flagged writer side, its resource lemmas** (U10m): `cm_wtxEnd_live`,
`cm_wtxEnd_lost`, `cm_wdbW_cfacts`, `cm_wdbW_mapLen` and `cm_wdbW_bounds` for `wdbW' fr` and
`wtxEnd' fr` (the writer's recorded-bytes token carried along).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailFPure
public import Proof.go_etcd_io.bbolt.Commit.AssembleEnd
public import Proof.go_etcd_io.bbolt.Commit.AssembleAcc
public import Proof.go_etcd_io.bbolt.Commit.PubFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A mapped writer ready to close, flagged.** -/
theorem cm_wtxEnd_live' (fr : Bool) (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb)
    (hwr : X.t.t.writable' = true) (hrl : (X.t.bs !! X.rl).isSome) :
    K.full (GF := GF) ∗ wtxW K tx r false X ∗ wdbW' fr K tx X.v w ∗ cmExcl K r X (treeData w.C) ⊢
      wtxEnd' fr K tx r X (wLive X.v w.C) w := by
  unfold wdbW' cmExcl wtxEnd'
  iintro ⟨#Hfull, Hw, ⟨Hl, %Hok, Htok⟩, Hrwl, Hcls, Hv, Hst⟩
  iframe Hfull Hl Hrwl Hcls Hv Hst Htok
  isplitl [Hw]
  · ileft; iexact Hw
  ipureintro; exact ⟨Hok.1, hwr, hrl⟩

/-- **A writer after a failed remap, ready to close, flagged.** -/
theorem cm_wtxEnd_lost' (fr : Bool) (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb)
    (hwr : X.t.t.writable' = true) (hrl : (X.t.bs !! X.rl).isSome) :
    K.full (GF := GF) ∗ wtxLost K tx r false X ∗ wdbLost' fr K tx X.v w ∗
        cmExcl K r X (treeData w.C) ⊢
      wtxEnd' fr K tx r X (some X.v, some (w.C.txid + 1), false, false) w := by
  unfold wdbLost' cmExcl wtxEnd'
  iintro ⟨#Hfull, Hw, ⟨Hl, %Hok, Htok⟩, Hrwl, Hcls, Hv, Hst⟩
  iframe Hfull Hl Hrwl Hcls Hv Hst Htok
  isplitl [Hw]
  · iright; iexact Hw
  ipureintro; exact ⟨Hok.1, hwr, hrl⟩

/-- `cm_wdbW_cfacts` for `wdbW' fr`. -/
theorem cm_wdbW'_cfacts (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    K.core (GF := GF) ∗ wdbW' fr K tx v w ⊢
      |={⊤}=> wdbW' fr K tx v w ∗ ⌜cFacts w.C w.fl (wLive v w.C)⌝ := by
  iintro ⟨#Hkc, Hd⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
  iunfold wdbW' at Hd
  icases Hd with ⟨Hlive, %Hok, Htok⟩
  iunfold wdbLive at Hlive
  icases Hlive with ⟨Hcg, Hflo, Hpair, Hrcpt⟩
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hrest⟩
  imod store_cfacts K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms _
    $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hcf⟩
  · iframe; iframe #
  imodintro
  isplitl
  · unfold wdbW' wdbLive wdbCoreG
    iframe
    ipureintro; exact Hok
  · ipureintro; exact Hcf

/-- `cm_wdbW_mapLen` for `wdbW' fr`. -/
theorem cm_wdbW'_mapLen (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) fr K tx v w ⊢ ⌜mapLen w.ms ≤ 0xFFFFFFFFFFFF⌝ := by
  unfold wdbW' wdbLive wdbCoreG
  iintro ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, Hmf, -⟩, -⟩, -⟩
  iapply cm_mapFields_len K.db _ _ $$ Hmf

/-- `cm_wdbW_bounds` for `wdbW' fr`. -/
theorem cm_wdbW'_bounds (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) fr K tx v w ⊢ ⌜w.fl.WF ∧ w.C.hwm < 2 ^ 48⌝ := by
  unfold wdbW' wdbLive wdbCoreG flPgOwn
  iintro ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, Hmf, -⟩, ⟨%a, %s, %al, %ca, %pe, %c, %pp, -, -, -, -, -,
    -, -, -, -, -, %Hwf⟩, -⟩, %Hok, -⟩
  ihave %Hl := cm_mapFields_len K.db _ _ $$ Hmf
  ipureintro
  refine ⟨Hwf.2, ?_⟩
  have h9 := Hok.1.2.2.2.2.2.2.2.2.1 v.base (mapLen w.ms) Hok.2.1
  have : mapLen w.ms ≤ 0xFFFFFFFFFFFF := Hl
  omega

/-- `cm_wdbW_ok` for `wdbW' fr`, keeping it. -/
theorem cm_wdbW'_ok (fr : Bool) (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW' (GF := GF) fr K tx v w ⊢
      ⌜wdbOK' fr w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝ := by
  unfold wdbW'; iintro ⟨-, %h, -⟩; ipureintro; exact h

end acc

end bbolt
end EtcdGrove
end Perennial
