/-
Lean-first (no Rocq counterpart).

The proof of `(*Server).Apply`: the input is a boxed `Op` (`regInOk`), so `input.(Op)` goes
through. A write calls `Put`, whose atomic update is the caller's: at its linearization point
the register goes to the written value, and the model's step on the write with the output `""`
(what `Apply` then returns) is that value (`regStep_put`). An append calls `Append`, likewise
(`regStep_app`: the state with the value appended). A read calls `Get`, whose update
leaves the register at `x` and returns `x`: the model's step on the read with the output `x`
leaves it at `x` (`regStep_get`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server__Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server__Put
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server__Append
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Server__Get

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvappend

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvappend.Assumptions]

theorem Server.Apply.wp_proof
    (wp_Put : Server.Put.spec (GF := GF) (hG := hG))
    (wp_Append : Server.Append.spec (GF := GF) (hG := hG))
    (wp_Get : Server.Get.spec (GF := GF) (hG := hG)) :
    Server.Apply.spec (GF := GF) (hG := hG) := by
  intro γ s
  iintro #Hpkg #Hs
  unfold applySpec
  iintro %i
  imodintro
  iintro %Φ ⟨%Hin, Htt⟩ HAU
  obtain ⟨b, ap, w, rfl⟩ := Hin
  wp_method_call
  wp_call
  wp_call
  wp_auto
  simp only [LawfulSet.diff_empty]
  cases b with
  | true =>
    wp_auto
    -- `s.Put(in.Val)`: its update is the caller's, with the output `""`
    wp_apply_core (wp_Put γ s w) $$ [$Hpkg $Hs]
    simp only [LawfulSet.diff_empty]
    imod HAU with ⟨%x, Hx, Hclose⟩
    imodintro
    iexists x
    iframe Hx
    iintro Hw
    imod Hclose $$ %w %(boxS go!"") [Hw] with HΦ
    · iframe
      ipureintro
      exact regStep_put x ap w _
    imodintro
    iintro -
    wp_auto
    iapply HΦ
    iframe Htt
    simp only [regS]
    ipureintro
    exact ⟨true, ap, w, rfl, nofun⟩
  | false =>
    cases ap with
    | true =>
      wp_auto
      -- `s.Append(in.Val)`: its update is the caller's, with the output `""`
      wp_apply_core (wp_Append γ s w) $$ [$Hpkg $Hs]
      simp only [LawfulSet.diff_empty]
      imod HAU with ⟨%x, Hx, Hclose⟩
      imodintro
      iexists x
      iframe Hx
      iintro Hw
      imod Hclose $$ %(x ++ w) %(boxS go!"") [Hw] with HΦ
      · iframe
        ipureintro
        exact regStep_app x w _
      imodintro
      iintro -
      wp_auto
      iapply HΦ
      iframe Htt
      simp only [regS]
      ipureintro
      exact ⟨false, true, w, rfl, fun _ => nofun⟩
    | false =>
      wp_auto
      -- `s.Get()`: its update is the caller's, with the output the state read
      wp_apply_core (wp_Get γ s) $$ [$Hpkg $Hs]
      simp only [LawfulSet.diff_empty]
      imod HAU with ⟨%x, Hx, Hclose⟩
      imodintro
      iexists x
      iframe Hx
      iintro Hx
      imod Hclose $$ %x %(boxS x) [Hx] with HΦ
      · iframe
        ipureintro
        show regStep x (boxOp ⟨false, false, w⟩, boxS x) = some x
        rw [regStep_get]
        simp
      imodintro
      iintro -
      wp_auto
      iapply HΦ
      iframe Htt
      simp only [regS]
      ipureintro
      exact ⟨false, false, w, rfl, fun _ _ => ⟨_, rfl⟩⟩

end proof

end logkvappend
end lintest
end EtcdGrove
end Perennial
