/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__Servers.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__Servers
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]


theorem Cluster.Servers.wp_proof (wp_names : names.spec (GF := GF) (hG := hG))
    (wp_SetOf : AntCheck.SetOf.spec (GF := GF) (hG := hG)) :
    Cluster.Servers.spec (GF := GF) (hG := hG) := by
  intro c N hN
  wp_start as #HN
  ihave #Hck : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_names N $$ [$Hpkg] as %sl #Hsl
  try wp_auto
  wp_apply wp_SetOf sl (AntSim.namesL (uint.nat N)) $$ [$Hck $Hsl] as %u #Hu
  · ipureintro
    simp only [AntSim.namesL, List.length_map, List.length_range]
    word
  try wp_auto
  iapply HΦ
  iexact Hu

end proof

end AntHarness
end EtcdGrove
end Perennial
