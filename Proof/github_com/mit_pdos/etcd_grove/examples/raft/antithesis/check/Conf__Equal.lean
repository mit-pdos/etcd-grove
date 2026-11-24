/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Conf.Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Conf__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Conf.Equal.wp_proof (wp_SetEqual : Set.Equal.spec (GF := GF) (hG := hG)) :
    Conf.Equal.spec (GF := GF) (hG := hG) := by
  intro g c h d
  wp_start as ⟨#Hc, #Hd⟩
  iunfold confRO at Hc Hd
  icases Hc with ⟨#Hci, #Hco⟩
  icases Hd with ⟨#Hdi, #Hdo⟩
  wp_auto
  icases typedPointsto_split _ _ _ $$ c with Hcf
  icases typedPointsto_split _ _ _ $$ d with Hdf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  iNamed Hdf
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.TypeAssumptions.ptr_unfold'Equal.method_unfold]
  try wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Hci Hdi] as -
  · iframe Hci Hdi
  by_cases hi : c.cin = d.cin
  · rw [decide_eq_true hi]
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.TypeAssumptions.ptr_unfold'Equal.method_unfold]
    try wp_auto
    wp_apply wp_SetEqual _ _ _ _ $$ [Hco Hdo] as -
    · iframe Hco Hdo
    try wp_auto
    have : decide (c = d) = decide (c.cout = d.cout) := by
      cases c; cases d; simp_all
    rw [this]
    iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false hi]
    try wp_auto
    rw [decide_eq_false (fun (e : c = d) => hi (by rw [e]))]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
