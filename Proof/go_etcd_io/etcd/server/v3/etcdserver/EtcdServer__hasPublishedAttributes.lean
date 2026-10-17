/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__hasPublishedAttributes.lean`
(etcd-io/etcd#22525). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__hasPublishedAttributes
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Member
public import Spec.slices.EqualString

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem EtcdServer.hasPublishedAttributes.wp_proof
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Member.spec (GF := GF) (hG := hG))
    (hEq : slices.EqualString.spec (GF := GF) (hG := hG)) :
    EtcdServer.hasPublishedAttributes.spec (GF := GF) (hG := hG) := by
  intro s c id a cus
  wp_start as #Hma
  ihave #Hma' := Hma
  iunfold srvMemberAttrs at Hma'
  icases Hma' with ⟨#Hid, #Hc, #Hrc, #Ha, #Hcus⟩
  ihave #Pmem : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Psl : isPkgInit (PROP := IProp GF) pkg_id.slices $$ []
  · iPkgInit
  ihave Ha2 := Ha
  iStructNamed Ha2
  (try wp_auto)
  wp_apply hMID s id $$ []
  · iframe #
  (try wp_auto)
  wp_apply hMem c id $$ [] as %m Hm
  · iframe #
  (try wp_auto)
  icases Hm with (%Hmn | ⟨%nm, %cu, %cus', %Hmn, Hnm, Hcu, Hcus', %Hheld⟩)
  · subst Hmn
    (try wp_auto)
    iapply HΦ
    ipureintro
    intro h; cases h
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      ipureintro
      intro h; cases h
    · (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_apply hEq cu a.ClientURLs' cus' cus _ _ $$ [Hcus'] as %b ⟨-, -, %Hb⟩
        · iframe #; iframe Hcus'
        (try wp_auto)
        iapply HΦ
        ipureintro
        intro hb
        subst Hb
        have hl : cus' = cus := of_decide_eq_true hb
        subst hl
        simp_all
      · (try wp_auto)
        iapply HΦ
        ipureintro
        intro h; cases h

end proof

end EtcdGrove
end Perennial
