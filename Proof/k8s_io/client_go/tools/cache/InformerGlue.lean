/-
**The informer invariant's accessors** (phase 4 of `notes/k8s-daemonset-plan.md`, fourth round): the
linearization points the informer's components and its clients take through `infInv`. Lean-first.

* `infInv_readAU`: a reader of the store (the listers' `List`, `GetByKey`, `ByIndex`, `Index`, the
  consistency store's `LastStoreSyncResourceVersion`): at its linearization point it learns
  `readFacts` (the store is the server's table at its version, a lower bound of that version).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerInv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI Iris.ProofMode apimodel cache

section glue
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A store reader's linearization point**, through the invariant: the store's state `σs`, its
facts `readFacts`. -/
theorem infInv_readAU (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames) (γi : InfNames)
    (K : cache.St → IProp GF) :
    ⊢ infInv γa r γf γt γi -∗ (∀ σs, readFacts γa r γi σs -∗ K σs) -∗
      |={⊤ \ ∅, ∅}=> ∃ σs, storeSt γt σs ∗ (storeSt γt σs ={∅, ⊤ \ ∅}=∗ K σs) := by
  iintro #Hinv HK
  rw [Iris.Std.LawfulSet.diff_empty]
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, #Hp, Hreg, #Hsnap, Hq, Hst, Hsw, Hlast, Hpop, Hlb,
    %Hok⟩
  ihave #Hlb' := monoNatLbOwn_get γi.rvlb 1 (rvNat s.store.rv) $$ Hlb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑infN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σs
  iframe Hst
  iintro Hst
  imod Hclose2 with -
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, pd, ap
    iframe
    iframe #
    ipureintro; exact Hok
  imodintro
  iapply HK
  unfold readFacts
  iexists σp, s.store, R
  iframe #
  ipureintro
  exact ⟨Hok.2.2.2.2.1, Hok.1.1⟩

end glue

end informer
end EtcdGrove
end Perennial
