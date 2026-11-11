/-
Lean-first (no Rocq counterpart).

The proof of `Run`: `RunLin` without its linearization.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

theorem Run.wp_proof
    (wp_RunLin : RunLin.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) :=
    fun σ S m apply gen clock inOk libState clockVal t0 Eapp Eclk clients ops dur HEapp HEclk
      Hc0 Hc31 Hops Hbound => by
  wp_start as ⟨#Hcc, #Hmodel, #Happly, #Hgen, #Hclock, Hlib, Hclk⟩
  wp_auto
  wp_apply wp_RunLin σ S m apply gen clock inOk libState clockVal t0 Eapp Eclk clients ops dur
    HEapp HEclk Hc0 Hc31 Hops Hbound $$ [$Hlib $Hclk] as %r %lsl ⟨%Hr, -⟩
  · iframe #
  iapply HΦ
  ipureintro; exact Hr

end proof

end lintest
end EtcdGrove
end Perennial
