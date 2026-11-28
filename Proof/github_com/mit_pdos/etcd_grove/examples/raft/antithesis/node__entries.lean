/-
Lean-first (no Rocq counterpart). #33 parity B1 (B2: the spec reads only `n.c` and `c.mode`): the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__entries.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__entries
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.entriesOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

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
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem node.entries.wp_proof (wp_entriesOf : entriesOf.spec (GF := GF) (hG := hG)) :
    node.entries.spec (GF := GF) (hG := hG) := by
  intro c n md sl dq els es hnorm
  wp_start as ⟨#Hnc, #Hm, Hsl, #Hents⟩
  ihave Hm' := Hm
  iStructNamed Hm'
  wp_auto
  wp_apply wp_entriesOf sl dq els es md.Nodes' hnorm $$ [$Hpkg $Hsl $Hents] as %out ⟨Hsl, #Hout, Hr⟩
  try wp_auto
  iapply HΦ
  iframe
  iframe Hents Hout

end proof

end AntHarness
end EtcdGrove
end Perennial
