module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Misc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [replica.Assumptions]

theorem dlog.Logger.Println.spec_holds : dlog.Logger.Println.spec (GF := GF) := by
  intro l lg v
  wp_start as #Hl
  ihave %Hln := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  rw [show decide (l = null) = false from decide_eq_false Hln]
  wp_auto
  wp_end

theorem dlog.Logger.Printf.spec_holds : dlog.Logger.Printf.spec (GF := GF) := by
  intro l lg format v
  wp_start as #Hl
  ihave %Hln := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  rw [show decide (l = null) = false from decide_eq_false Hln]
  wp_auto
  wp_end

theorem dlog.Logger.Fatal.spec_holds : dlog.Logger.Fatal.spec (GF := GF) := by
  intro l lg v
  wp_start as #Hl
  ihave %Hln := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  wp_auto
  rw [show decide (l = null) = false from decide_eq_false Hln]
  wp_auto
  wp_end

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
