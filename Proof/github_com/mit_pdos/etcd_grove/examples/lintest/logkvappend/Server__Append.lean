/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).Append`: it calls `write` with the entry `{app: true, val: v}`, whose
atomic update is the caller's: applying an append entry takes the register from `x` to `x ++ v`
(`entryStep`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server__Append
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server__write

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvappend

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Assumptions]

theorem Server.Append.wp_proof (wp_write : Server.write.spec (GF := GF) (hG := hG)) :
    Server.Append.spec (GF := GF) (hG := hG) := by
  intro γ s v
  iintro %Φ ⟨#Hpkg, #Hs⟩ HAU
  simp only [LawfulSet.diff_empty]
  wp_method_call
  wp_call
  wp_auto
  wp_apply_core (wp_write γ s ⟨true, v⟩) $$ [$Hpkg $Hs]
  simp only [LawfulSet.diff_empty]
  imod HAU with ⟨%x, Hx, Hclose⟩
  imodintro
  iexists x
  iframe Hx
  iintro Hw
  imod Hclose $$ [Hw] with HΦ
  · simp only [entryStep, ite_true]
    iexact Hw
  imodintro
  iintro -
  wp_auto
  iapply HΦ
  itrivial

end proof

end logkvappend
end lintest
end EtcdGrove
end Perennial
