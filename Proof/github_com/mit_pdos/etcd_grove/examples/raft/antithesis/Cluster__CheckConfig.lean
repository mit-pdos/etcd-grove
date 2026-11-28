/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__CheckConfig.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__CheckConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.names
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetOf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.CheckConfig.wp_proof (wp_names : names.spec (GF := GF) (hG := hG))
    (wp_SetOf : AntCheck.SetOf.spec (GF := GF) (hG := hG)) :
    Cluster.CheckConfig.spec (GF := GF) (hG := hG) := by
  intro c m
  wp_start as ⟨#Hm, %Hb⟩
  ihave #Hck : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check $$ []
  · iPkgInit
  ihave Hm' := Hm
  iStructNamed Hm'
  iapply wp_fupd
  wp_auto
  wp_apply wp_names m.Nodes' $$ [$Hpkg] as %sl #Hsl
  try wp_auto
  wp_apply wp_SetOf sl (AntSim.namesL (uint.nat m.Nodes')) $$ [$Hck $Hsl] as %u #Hu
  · ipureintro
    simp only [AntSim.namesL, List.length_map, List.length_range]
    word
  try wp_auto
  wp_apply wp_names m.Voters' $$ [$Hpkg] as %sl2 #Hsl2
  try wp_auto
  wp_apply wp_SetOf sl2 (AntSim.namesL (uint.nat m.Voters')) $$ [$Hck $Hsl2] as %u2 #Hu2
  · ipureintro
    simp only [AntSim.namesL, List.length_map, List.length_range]
    word
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #Hp
  imodintro
  iapply HΦ
  iunfold AntCheck.configRO
  iexists _
  iframe Hp
  iframe Hu Hu2
  ipureintro; rfl

end proof

end AntHarness
end EtcdGrove
end Perennial
