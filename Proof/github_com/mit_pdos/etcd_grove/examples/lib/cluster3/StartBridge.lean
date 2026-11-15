/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/cluster3/StartBridge.lean`. Lean-first (no Rocq
counterpart). `net.Listen` at `addr`; on success, the bridge on the listener to `client`
(`bridge.New`, whose trust-boundary spec gives `forwards`, D26).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartBridge
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.New
public import Spec.net.Listen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

theorem StartBridge.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_New : bridge.New.spec (GF := GF) (hG := hG)) :
    StartBridge.spec (GF := GF) (hG := hG) := by
  intro addr client
  wp_start as Hfree
  ihave #Pbr : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge
    $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Listen go!"tcp" addr $$ [Hfree] as %l %err Hr
  · iframe; ipureintro; rfl
  icases Hr with (⟨%Herr, Hl⟩ | %Herr)
  · subst Herr
    wp_auto
    wp_apply wp_New client addr l $$ [Hl] as %br ⟨Hob, #Hfw, %Hnr⟩
    · iframe #; iframe
    iapply HΦ
    iframe
    ileft
    iframe
    isplitr
    · ipureintro; rfl
    unfold forwards
    iframe #
    ipureintro; exact Hnr
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      iright
      ipureintro; exact Herr

end proof

end cluster3
end EtcdGrove
end Perennial
