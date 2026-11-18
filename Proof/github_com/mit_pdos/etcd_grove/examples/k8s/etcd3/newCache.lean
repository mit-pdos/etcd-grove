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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem newCache.wp_proof :
    newCache.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as -
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Obj)) as %m Hm
  (try wp_auto)
  wp_apply (wp_map_make1 (K := w64) (V := Obj)) as %mw Hmw
  (try wp_auto)
  iStructNamed «$r0»
  imod sync.init_Mutex (cacheInv c «$r0_ptr») ⊤
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache go!"mu" «$r0_ptr»)
    $$ [mu] [objs Hm wobjs Hmw] with #Hmu
  · iexact mu
  · inext
    unfold cacheInv
    iexists m, ∅, mw, ∅
    iframe
    simp
    iempintro
  ihave Hdone : sync.atomic.ownInt64 (GF := GF)
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache go!"done" «$r0_ptr»)
      (DFrac.own 1) (W64 0) $$ [done]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact done
  imod inv_alloc cacheDoneN ⊤ (iprop(∃ v : w64, sync.atomic.ownInt64 (GF := GF)
      (structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache go!"done" «$r0_ptr»)
      (DFrac.own 1) v)) $$ [Hdone] with #Hdinv
  · inext; iexists W64 0; iexact Hdone
  ipersist watch
  ipersist unary
  ipersist total
  ipersist floor
  have h0 : uint.Z (0 : w64) < 2 ^ 62 := by word
  imodintro
  iapply HΦ
  unfold isCache cacheFloor
  iframe #
  (try (iexists _, _, _; iframe #))
  (try (ipureintro; exact h0))

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
