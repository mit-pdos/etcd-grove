module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newCache

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem newCache.wp_proof :
    newCache.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as -
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Obj)) as %m Hm
  (try wp_auto)
  iStructNamed «$r0»
  imod sync.init_Mutex (cacheInv c «$r0_ptr») ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache go!"mu" «$r0_ptr»)
    $$ [mu] [objs Hm] with #Hmu
  · iexact mu
  · inext
    unfold cacheInv
    iexists m, ∅
    iframe
    simp
    iempintro
  imodintro
  iapply HΦ
  unfold isCache
  iexact Hmu

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
