/-
`container`: a `map[string]interface{}` literal of two strings (`isIface_ofMap`). Lean-first
(2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.container
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Maps

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

theorem container.wp_proof_of (hScalar : isIface_scalar.law (GF := GF))
    (hMap : isIface_ofMap.law (GF := GF)) :
    container.spec (GF := GF) := fun n i => by
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %m Hm
  wp_apply wp_mapInsert $$ Hm as Hm
  wp_apply wp_mapInsert $$ Hm as Hm
  imod ownMap_persist _ _ _ $$ Hm with #Hm
  imodintro
  iapply HΦ
  unfold isUMap containerKVs
  rw [show ∀ kvs, UVal.map (kvsOf kvs) = UVal.ofMap kvs from fun _ => rfl]
  iapply (hMap m _ [(go!"name", str n), (go!"image", str i)] 
    (by simp only [List.map_cons, List.map_nil]; decide) (fun k => by
    by_cases h1 : go!"image" = k <;> by_cases h2 : go!"name" = k <;> simp_all [lookupKV])) $$ Hm
  simp only [sepL, List.foldr_cons, List.foldr_nil, str]
  isplitr
  · iexists (interface.mkOk go.string #n)
    isplitr
    · ipureintro; simp
    · iapply hScalar.2.2.2; itrivial
  isplitr
  · iexists (interface.mkOk go.string #i)
    isplitr
    · ipureintro; simp
    · iapply hScalar.2.2.2; itrivial
  itrivial

theorem container.wp_proof : container.spec (GF := GF) :=
  container.wp_proof_of isIface_scalar_law_holds isIface_ofMap_law_holds

end proof

end k8s_smd
end EtcdGrove
end Perennial
