/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/New.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.New.wp_proof
    (hNB : backend.newBackend.spec (GF := GF) (hG := hG)) :
    backend.New.spec (GF := GF) (hG := hG) := by
  intro _ cfg P D W Pk K
  wp_start as ⟨#Hzl, Hfile, %HP, #Hhk, #Hvoff, Hmk, Htok⟩
  wp_auto
  wp_apply (hNB cfg P D W Pk K) $$ [Hfile Hmk Htok] as %r Hr
  · iframe
    iframe #
    ipureintro; exact HP
  icases Hr with (⟨%b, %γ, %Hr, Hp, #Hhka, #Hbf, Htok⟩ | %Hpan)
  · subst Hr
    wp_auto
    iapply HΦ
    ileft
    iexists b, γ
    iframe Hp Hhka Hbf Htok
    ipureintro; rfl
  · obtain ⟨Hno, pv, rfl⟩ := Hpan
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact ⟨Hno, _, rfl⟩

end proof

end EtcdGrove
end Perennial
