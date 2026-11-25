/-
`log.Printf` with arguments each well-formed for `fmt` or an error: H6 (`LogHyp`; the lab proved it
from its own `log` model, whose `touch` calls an error's `Error()`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Lemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- A log argument: well-formed for `fmt` (no method runs), or an error. -/
def logArg (v : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, v = interface.ok ii → fmt.ArgWf ii⌝ ∨ models_lab.errAny v)

instance logArg_persistent (v : GoInterface) : Persistent (logArg (hG := hG) v) := by
  unfold logArg; infer_instance

theorem logArg_argOk (v : GoInterface) : logArg (hG := hG) v ⊢ argOk v := by
  unfold logArg argOk
  iintro (%Hwf | #He)
  · ileft; ipureintro; intro ii h; exact Or.inl (Hwf ii h)
  · iright; iexact He

theorem logArgs_argOk (xs : List GoInterface) :
    ([∗list] v ∈ xs, logArg (hG := hG) v) ⊢ [∗list] v ∈ xs, argOk (GF := GF) v :=
  BI.BigSepL.bigSepL_mono (fun _ => logArg_argOk _)

theorem wp_Printf_args (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗
        [∗list] v ∈ xs, logArg (hG := hG) v }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  iintro %Φ ⟨#Hpkg, Hs, #Hargs⟩ HΦ
  ihave #Hok := logArgs_argOk xs $$ Hargs
  wp_apply LogHyp.wp_Printf msg arg xs dq $$ [$Hs $Hok] as Hs
  iapply HΦ; iframe

theorem logArg_str (x : GoString) : ⊢ logArg (hG := hG) (interface.mkOk go.string #x) := by
  unfold logArg
  ileft
  ipureintro
  intro ii h
  have := fmt.ArgsWf.cons_string x [] fmt.ArgsWf.nil
  exact this ii (by rw [← h]; exact List.mem_singleton.mpr rfl)

theorem logArg_err (e : GoInterface) : models_lab.errAny (GF := GF) e ⊢ logArg (hG := hG) e := by
  iintro #H; unfold logArg; iright; iexact H

end proof

end github_com.despreston.go_craq

end Perennial
