/-
`Commit`'s store facts at the freelist's joins (U10l of `notes/bbolt-proof-plan.md`): the store's
`storeOK` facts of the committed state and the freelist (`cFacts`: `flBelow` for the writer's txid,
the freelist well-formed), read through the invariant with the writer side's ghost halves, and the
mapping's length bound; for `cmPubPg_of_spill`'s premises.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
public import Proof.go_etcd_io.bbolt.Commit.AssembleAcc

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

/-- **The store's facts at a live writer side** (`store_cfacts` through `K.core`'s invariant). -/
theorem cm_wdbW_cfacts (K : BC) (tx : Loc) (v : View) (w : WDb) :
    K.core (GF := GF) ∗ wdbW K tx v w ⊢ |={⊤}=> wdbW K tx v w ∗ ⌜cFacts w.C w.fl (wLive v w.C)⌝ := by
  iintro ⟨#Hkc, Hd⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hkc
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
  iunfold wdbW at Hd
  icases Hd with ⟨Hlive, %Hok⟩
  iunfold wdbLive at Hlive
  icases Hlive with ⟨Hcg, Hflo, Hpair, Hrcpt⟩
  iunfold wdbCoreG at Hcg
  icases Hcg with ⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hrest⟩
  imod store_cfacts K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms _
    $$ [Hpi Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv, %Hcf⟩
  · iframe; iframe #
  imodintro
  isplitl
  · unfold wdbW wdbLive wdbCoreG
    iframe
    ipureintro; exact Hok
  · ipureintro; exact Hcf

/-- **The writer side's mapping is at most `maxMapSize`** (`mapFields`). -/
theorem cm_wdbW_mapLen (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜mapLen w.ms ≤ 0xFFFFFFFFFFFF⌝ := by
  unfold wdbW wdbLive wdbCoreG
  iintro ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, Hmf, -⟩, -⟩, -⟩
  iapply cm_mapFields_len K.db _ _ $$ Hmf

end acc

end bbolt
end EtcdGrove
end Perennial
