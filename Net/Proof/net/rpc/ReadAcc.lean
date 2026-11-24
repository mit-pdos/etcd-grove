/-
The accessor of a frame read (`readFull.spec`, `readFrame.spec` and the server codec's read specs):
besides the reader predicate after the `Read`, what a failed `Read` (a result that is not bytes)
gives the caller, `F`. A caller that needs nothing of a failed read (the client's codec) makes one
with `F := True` from an accessor of the plain shape (`readAcc_true`).
-/
module

public import Net.Proof.net.rpc.Base
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- An accessor of the plain shape, with nothing for a failed read (`F := True`). -/
theorem readAcc_true (cn : Nat) (s : Bool) (P : List w8 → IProp GF) :
    □ (∀ (got : List w8) (m : Nat), P got -∗
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
            P (got ++ r.got)) ⊢
    □ (∀ (got : List w8) (m : Nat), P got -∗
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
            P (got ++ r.got) ∗ (⌜∀ bs, r ≠ .bytes bs⌝ -∗ (True : IProp GF))) := by
  iintro #Hacc
  imodintro
  iintro %got %m HP
  imod Hacc $$ %got %m HP with ⟨%st, %d, HE, HD, Hcl⟩
  imodintro
  iexists st, d
  iframe HE HD
  iintro %r %d' %Hrd HE HD
  imod Hcl $$ %r %d' %Hrd HE HD with HP
  imodintro
  iframe HP
  iintro -
  itrivial

end acc

end net.rpc
end Perennial
