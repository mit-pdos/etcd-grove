/- Lean-first (no Rocq counterpart). The proof of `drawConfig`: a field-by-field draw (`anyInt`, `anyInts`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.drawConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.anyInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.anyInts

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem drawConfig.wp_proof (wp_anyInt : anyInt.spec (GF := GF) (hG := hG))
    (wp_anyInts : anyInts.spec (GF := GF) (hG := hG)) :
    drawConfig.spec (GF := GF) (hG := hG) := by
  intro pfx
  wp_start
  wp_auto
  repeat (wp_apply wp_anyInt as %_ -; (try wp_auto))
  wp_apply wp_anyInts _ (by decide) as %s1 %ws1 H1
  (try wp_auto)
  wp_apply wp_anyInts _ (by decide) as %s2 %ws2 H2
  (try wp_auto)
  wp_apply wp_anyInts _ (by decide) as %s3 %ws3 H3
  (try wp_auto)
  wp_apply wp_anyInts _ (by decide) as %s4 %ws4 H4
  (try wp_auto)
  wp_apply wp_anyInts _ (by decide) as %s5 %ws5 H5
  (try wp_auto)
  wp_apply wp_anyInts _ (by decide) as %s6 %ws6 H6
  (try wp_auto)
  wp_apply wp_anyInts _ (by decide) as %s7 %ws7 H7
  (try wp_auto)
  repeat (wp_apply wp_anyInt as %_ -; (try wp_auto))
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iunfold mixOwn
  iexists DFrac.own 1, _, _, _, _, _, _
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
