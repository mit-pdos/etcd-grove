/-
**The constructor's posts' laws for clients** (mvccfull's Probe, 2026-11-09, the unfold list): what
a client of `New` that trades the fresh backend's payment rights (`newPostK`) used to get by
unfolding `bFresh`, `newPostKP` and the constants `wbInit`, `rdPoolN` (the destructuring of `newPostK` itself is `newPostK_named`,
`ClientLaws`). In a module of its own, so that adding them leaves the backend's other modules (and
their importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- The constructor's stock of write-back tokens (`wbInit`), by value. -/
theorem wbInit_val : wbInit = 2 ^ 40 - 1 := rfl

/-- The reader pool's size (`rdPoolN`), by value. -/
theorem rdPoolN_val : rdPoolN = 2 ^ 28 := rfl

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A fresh backend's payment rights** are every write-back token and the clients' whole open
token. -/
theorem bFresh_eq (γ : BNames) : bFresh (GF := GF) γ ⊣⊢ ownToks γ.wb wbInit ∗ bOpen γ 1 := by
  unfold bFresh; exact .rfl

/-- **`newPostKP` from its parts** (the converse of `newPostKP_named`): with the counted stock
`rdStock` whole, for a client that trades the payment rights `K` for others. -/
theorem newPostKP_intro (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc)
    (D : Data) :
    isBackend γ P (W γ) (Pk γ) b ∗ isStopChans γ P (W γ) (Pk γ) b ∗ K γ ∗
      bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ plHook γ func.nil ∗
      rbOwn γ (rbData P D) ∗ rdPool γ P b ∗ rdAuth γ P b ∗ rdStock γ P b ∗
      dlInit γ ∗ fkCl γ P D ∗ srSlot b ⊢
    newPostKP γ P W Pk K b D := by
  unfold newPostKP; exact .rfl

end laws

end backend
end EtcdGrove
end Perennial
