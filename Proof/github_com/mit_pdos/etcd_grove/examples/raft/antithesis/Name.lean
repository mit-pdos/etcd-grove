/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Name.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Name
public import Perennial.Spec.strconv.FormatUint

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

variable [strconv_sem : strconv.Assumptions]

theorem Name.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    Name.spec (GF := GF) (hG := hG) := by
  intro id
  by_cases h0 : id = W64 0
  · subst h0
    rw [show AntSim.nameOf (W64 0) = [] from rfl]
    wp_start
    wp_auto
    iapply HΦ
    ipureintro; trivial
  rw [show AntSim.nameOf id = go!"raft" ++ internal.strconv.fmtUint id (W64 10) by
    simp only [AntSim.nameOf, if_neg h0]]
  wp_start
  ihave #Hs : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · exact absurd rfl h0
  wp_apply wp_FormatUint id (W64 10) (by decide) (by decide) $$ [$Hs]
  iapply HΦ
  ipureintro; trivial

end proof

end AntHarness
end EtcdGrove
end Perennial
