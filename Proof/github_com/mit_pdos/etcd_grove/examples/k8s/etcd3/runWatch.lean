/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/runWatch.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.runWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.lastObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeWEvents
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Perennial.Spec.time.Sleep

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem runWatch.wp_proof
    (wp_watchEvents : watchEvents.spec (GF := GF) (hG := hG))
    (wp_lastObj : lastObj.spec (GF := GF) (hG := hG))
    (wp_encodeWEvents : encodeWEvents.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    runWatch.spec (GF := GF) (hG := hG) := by
  intro _ _ sp c γk x k n Q hS hQ hQQ hnr htb hok
  wp_start as ⟨Hlt, #Hst, #Hsw, #Hwl, #Hrs, HQ0, #HQup⟩
  wp_auto
  cases hsk : x.Skip'
  rotate_left
  · -- skipped
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro
    exact ⟨rfl, rfl, Or.inl rfl⟩
  obtain ⟨hk, hkl, hn, hn63⟩ := hok hsk
  wp_auto
  wp_apply wp_Now as %t -
  wp_apply (wp_watchEvents sp c γk x k n Q hS hQ hQQ hnr htb hk hkl hn hn63) $$ [$Hlt HQ0]
    as %sl %rsl %failed ⟨Hlt, Hr⟩
  · iframe #; iframe HQ0
  simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.hiccupDuration]
  -- the hiccup sleep
  wp_join iprop(True) at next
  · wp_apply wp_Since as %d -
    wp_if_destruct
    · wp_apply wp_Sleep
      wp_join_done; itrivial
    · wp_join_done; itrivial
  iintro -
  cases failed
  · rw [ite_eq_right Bool.false_ne_true]
    icases Hr with ⟨%rs, %kes, Hsl, #Hrs, %Hrel, Hseen⟩
    imod wevsOwnM_persist sl _ $$ Hsl with #Hs
    wp_auto
    wp_apply wp_lastObj $$ [$Hs] as %o %ok %Hlo
    wp_apply wp_encodeWEvents $$ [$Hs] as %Hlen
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    iexists rs.map k8s_correctness.toWEvL, kes, rs, rsl
    iframe
    iframe #
    ipureintro
    exact ⟨trivial, rfl, rfl, Hlo, Hrel, Hlen⟩
  · rw [ite_eq_left rfl]
    icases Hr with %Hr
    wp_auto
    iapply HΦ
    iframe Hlt
    ileft
    ipureintro
    exact ⟨rfl, rfl, Or.inr Hr⟩

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
