/-
`container` (`examples/k8s/smd/smd.go`). Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.container
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Literals

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem container.wp_proof : container.spec (GF := GF) := fun n i => by
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %m Hm
  wp_apply wp_mapInsert $$ Hm as Hm
  wp_apply wp_mapInsert $$ Hm as Hm
  imod (ownUMap_lit m [(go!"name", interface.mkOk go.string #n, .str n),
      (go!"image", interface.mkOk go.string #i, .str i)] (by simp only [List.map]; decide) (by rfl))
      $$ [Hm] with #Hm
  · isplitl
    · simp only [litMap, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      iexact Hm
    · iintro !> %e %he
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at he
      rcases he with rfl | rfl <;> iapply ownU_str
  imodintro
  iapply HΦ
  rw [show containerKVs n i = mkKVs (List.map (fun e => (e.1, e.2.2))
    [(go!"name", interface.mkOk go.string #n, UVal.str n),
      (go!"image", interface.mkOk go.string #i, UVal.str i)]) from rfl]
  iexact Hm

end proof

end k8s_smd
end EtcdGrove
end Perennial
