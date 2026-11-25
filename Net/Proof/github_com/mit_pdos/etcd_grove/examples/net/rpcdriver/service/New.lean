/- Lean-first (no Rocq counterpart).

The proof of `service.New.spec`: the fresh `Svc`'s mutex gets its invariant `svcInv γid`, with
`runs` at the new empty map.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.New

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : service.Assumptions]

theorem New.wp_proof : New.spec (GF := GF) (hG := hG) := by
  intro γid
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %mref Hm
  irename «$r0» => Hc
  generalize «$r0_ptr» = c at *
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  imod sync.init_Mutex (svcInv γid c) ⊤ (muAddr c) $$ mu [runs Hm] with #Hmu
  · inext
    unfold svcInv
    iexists mref, ∅
    iframe
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  unfold isSvc
  iframe Hmu
  iPkgInit

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service
end Perennial
