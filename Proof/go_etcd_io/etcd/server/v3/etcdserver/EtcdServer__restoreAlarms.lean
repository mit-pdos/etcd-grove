/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__restoreAlarms.lean`. Lean-first (no Rocq
counterpart); placed at the server-construction unit's stage N0 (2026-10-16), unit N1's to prove.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__restoreAlarms
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewAlarmBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.NewAlarmStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.restoreAlarms.wp_proof
    (hAB : schema.NewAlarmBackend.spec (GF := GF) (hG := hG))
    (hAS : v3alarm.NewAlarmStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.restoreAlarms.spec (GF := GF) (hG := hG) := by
  intro s lg d W Pk qo a0 dq S r hS hhas
  wp_start as ⟨#Hlg, %Hlgnn, Hbe, #Hb, Ho, Hwb, Hpl, Htk, Hrb, %Hal, Ha0⟩
  wp_auto
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hapkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  wp_apply hAB lg _ $$ [] as %ab ⟨%abl, %Hab, #Habl, #Habb⟩
  wp_apply hAS lg ab abl d W Pk qo S r hS hhas $$ [Ho Hwb Hpl Htk Hrb]
    as %a %err ⟨⟨%Herr, %Hann⟩, Ho, Hpl, Htk, Hrb, #Has, Hon, #Hap⟩
  · iframe #; iframe Ho Hwb Hpl Htk Hrb; ipureintro; exact ⟨Hlgnn, Hab, Hal⟩
  subst Herr
  wp_auto
  iapply HΦ
  iframe Ho Hbe Hpl Htk Hrb
  isplitr
  · ipureintro; rfl
  iexists a
  iframe
  iframe #
  ipureintro; exact Hann

end proof

end EtcdGrove
end Perennial
