/-
**`HasSynced` through the informer invariant** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth
round): the FIFO's `HasSynced` (logically atomic, `RealFIFO.HasSynced.spec`) at the informer's
FIFO, with the invariant's `infInv_hasSyncedAU`: when it returns `true`, the first list's version
`v` (`infFirst`) and the store's version at least `v` from then on (`infRvLb`, which a later store
read turns into "the store is the server's table at a version at least the first list's":
`infInv_readLbAU`). Lean-first.

The informer's own `HasSynced` (`sharedIndexInformer.HasSynced` → `controller.HasSynced` → the
FIFO's) and the typed informers' forwards (C2) are not proved here.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerGlue
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__HasSynced

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The informer's FIFO's `HasSynced`**: `true` means the store has the first list. -/
theorem RealFIFO.wp_HasSynced_inf (wp_HasSynced : cache.RealFIFO.HasSynced.spec (GF := GF) (hG := hG))
    (f : Loc) (OK : GoInterface → IProp GF) (γa : ApiNames) (r : Res) (γf : FifoNames)
    (γt : TsNames) (γi : InfNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isFIFO f γf OK ∗
        infInv γa r γf γt γi }}
      (App (Val (f @!! go.GoType.PointerType RealFIFO.ty @!! go!"HasSynced")) (Val #()))
    {{ (b : Bool), RET #b; syncedFacts γi b }} := by
  iintro %Φ ⟨#Hpkg, #Hf, #Hinv⟩ HΦ
  iapply (wp_HasSynced f γf OK) $$ [$Hpkg $Hf]
  inext
  iapply (infInv_hasSyncedAU γa r γf γt γi (fun b => iprop(True -∗ Φ #b))) $$ Hinv
  iintro %b #Hb -
  iapply HΦ
  iexact Hb

end proof

end informer
end EtcdGrove
end Perennial
