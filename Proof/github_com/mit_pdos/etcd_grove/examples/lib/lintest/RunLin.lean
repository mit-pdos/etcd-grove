/-
Lean-first (no Rocq counterpart).

The proof of `RunLin`: it is `RunLin2` with an empty second group (2026-11-08, k8s 7f; until then
this file held the clients' and porcupine's proof, now `RunLin2.lean`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin2

@[expose] public section

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

theorem RunLin.wp_proof
    (wp_RunLin2 : RunLin2.spec (GF := GF) (hG := hG)) :
    RunLin.spec (GF := GF) (hG := hG) :=
    fun σ S m apply gen clock inOk libState clockVal t0 Eapp Eclk clients ops dur HEapp HEclk
      Hc0 Hc31 Hops Hbound => by
  wp_start as ⟨#Hcc, #Hmodel, #Happly, #Hgen, #Hclock, Hlib, Hclk⟩
  wp_auto
  have H0 : sint.Z (W64 0) = 0 := rfl
  wp_apply wp_RunLin2 σ S m apply gen clock inOk libState clockVal t0 Eapp Eclk clients ops
    (W64 0) (W64 0) dur HEapp HEclk Hc0 (by rw [H0]; omega) (by rw [H0]; omega) Hops (by rw [H0]; omega)
    (by rw [H0]; omega) $$ [$Hlib $Hclk] as %r %lsl ⟨%Hr, Hlin⟩
  · iframe #
  iapply HΦ
  isplitr
  · ipureintro; exact Hr
  iintro %Hok
  icases Hlin $$ %Hok with ⟨%lops, Hl, #Hio, %Hp⟩
  iexists lops
  iframe Hl Hio
  ipureintro
  refine ⟨?_, Hp.2⟩
  rw [Hp.1, H0]; omega

end proof

end lintest
end EtcdGrove
end Perennial
