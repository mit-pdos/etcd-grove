/-
`Commit`'s ends (U10g of `notes/bbolt-proof-plan.md`): `wtxEnd` (the pre of `Tx.rollback` and
`Tx.close`) assembled from `Commit`'s working state, mapped (`wdbW`, the store's writer state
`wLive`) or after a failed remap (`wdbLost`), with the exclusive part's other contents.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The exclusive part's contents beside the working state**: `rwlock`, the closed flag's half,
the agreed state (at the records `X`), the data's quarter at `D` (batch 44.3: the page tokens
are dropped, `wtxEnd` no longer takes them). -/
def cmExcl (K : BC) (r : TxReg) (X : WX) (D : Data) : IProp GF :=
  iprop(sync.ownMutex K.db.[DB, go!"rwlock"] ∗ ghostVar K.B.cls (1 : Qp).half false ∗
    (∃ c : TxViewC, ghostVar r.n.v 1 (c, TxX.wr X)) ∗ ghostVar K.B.st (1 : Qp).half.half D)

/-- **A mapped writer ready to close.** -/
theorem cm_wtxEnd_live (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb)
    (hwr : X.t.t.writable' = true) (hrl : (X.t.bs !! X.rl).isSome) :
    K.full (GF := GF) ∗ wtxW K tx r false X ∗ wdbW K tx X.v w ∗ cmExcl K r X (treeData w.C) ⊢
      wtxEnd K tx r X (wLive X.v w.C) w := by
  unfold wdbW cmExcl wtxEnd
  iintro ⟨#Hfull, Hw, ⟨Hl, %Hok⟩, Hrwl, Hcls, Hv, Hst⟩
  iframe Hfull Hl Hrwl Hcls Hv Hst
  isplitl [Hw]
  · ileft; iexact Hw
  ipureintro; exact ⟨Hok.1, hwr, hrl⟩

/-- **A writer after a failed remap, ready to close.** -/
theorem cm_wtxEnd_lost (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb)
    (hwr : X.t.t.writable' = true) (hrl : (X.t.bs !! X.rl).isSome) :
    K.full (GF := GF) ∗ wtxLost K tx r false X ∗ wdbLost K tx X.v w ∗ cmExcl K r X (treeData w.C) ⊢
      wtxEnd K tx r X (some X.v, some (w.C.txid + 1), false, false) w := by
  unfold wdbLost cmExcl wtxEnd
  iintro ⟨#Hfull, Hw, ⟨Hl, %Hok⟩, Hrwl, Hcls, Hv, Hst⟩
  iframe Hfull Hl Hrwl Hcls Hv Hst
  isplitl [Hw]
  · iright; iexact Hw
  ipureintro; exact ⟨Hok.1, hwr, hrl⟩

omit [GooseSemantics] hos in
/-- **The agreed state follows the records** (the transaction holds it whole). -/
theorem cm_excl_update (K : BC) (r : TxReg) (X X' : WX) (D : Data) :
    cmExcl (GF := GF) K r X D ⊢ |==> cmExcl K r X' D := by
  unfold cmExcl
  iintro ⟨Hrwl, Hcls, ⟨%c, Hv⟩, Hst⟩
  imod ghostVar_update (c, TxX.wr X') r.n.v _ $$ Hv with Hv
  imodintro
  iframe Hrwl Hcls Hst
  iexists c; iexact Hv

end res

end bbolt
end EtcdGrove
end Perennial
