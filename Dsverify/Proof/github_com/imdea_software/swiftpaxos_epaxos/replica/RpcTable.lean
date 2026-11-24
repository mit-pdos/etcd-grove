/-
The rpc code table (`rpc/rpc.go`): `NewTableId`, `Register`, `Get`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcTable

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions]

theorem rpc.NewTableId.wp_proof : rpc.NewTableId.spec (GF := GF) := by
  intro id
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w8) (V := rpc.Pair'')) as %m Hm
  wp_end
  rw [ownTable_unseal]; unfold ownTableDef
  iexists m
  iframe

theorem rpc.Table.Register.wp_proof : rpc.Table.Register.spec (GF := GF) := by
  intro t n E obj ch
  wp_start as Ht
  rw [ownTable_unseal]; unfold ownTableDef
  icases Ht with ⟨%pm, Ht, Hm⟩
  wp_auto
  wp_apply wp_mapInsert $$ Hm as Hm
  wp_end
  iexists pm
  iframe

theorem rpc.Table.Get.wp_proof : rpc.Table.Get.spec (GF := GF) := by
  intro t E id
  wp_start as #Ht
  rw [isTable_unseal]; unfold isTableDef
  icases Ht with ⟨%n, %pm, #Ht, #Hm⟩
  iStructNamed Ht
  wp_auto
  wp_apply wp_map_lookup2 $$ Hm as Hm
  simp only [Bool.decide_eq_true]
  wp_end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
