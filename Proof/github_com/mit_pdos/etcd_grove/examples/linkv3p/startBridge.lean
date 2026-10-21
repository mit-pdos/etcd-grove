/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/startBridge.lean`. Lean-first (no Rocq
counterpart). `net.Listen` at `addr`; on success, the listener given up to a relay to `client`
(the forwarding fact `grpc.relay`, D26), and the bridge on it (`bridge.New`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startBridge
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.New
public import Spec.net.Listen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem startBridge.wp_proof (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_New : bridge.New.spec (GF := GF) (hG := hG)) :
    startBridge.spec (GF := GF) (hG := hG) := by
  intro addr client Htb
  wp_start as ⟨Hfree, Htok⟩
  ihave #Pbr : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge
    $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Listen go!"tcp" addr $$ [Hfree] as %l %err Hr
  · iframe; ipureintro; rfl
  icases Hr with (⟨%Herr, Hl⟩ | %Herr)
  · subst Herr
    imod grpc.relay l addr client $$ Hl with ⟨%lo, %Hlo, #Hrl, #Hfw⟩
    subst Hlo
    wp_auto
    wp_apply wp_New client lo Htb $$ [Htok] as %br ⟨Hob, Htok⟩
    · iframe #; iframe
    iapply HΦ
    iframe
    ileft
    iframe
    isplitr
    · ipureintro; rfl
    unfold forwards
    iexact Hfw
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      iright
      ipureintro; exact Herr

end proof

end linkv3p
end EtcdGrove
end Perennial
