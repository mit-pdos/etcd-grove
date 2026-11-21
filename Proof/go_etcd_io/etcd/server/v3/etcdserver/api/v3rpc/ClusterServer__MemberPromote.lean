/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__MemberPromote
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClusterServer__header
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.membersToProtoMembers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__PromoteMember
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.TogRPCErrorPlain

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option hygiene false in
/-- An error `ei` of the server (`Hae : applyErrIs (ok ei)`): `togRPCError`, then the error
disjunct. -/
local macro "promote_rpc_err" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply (v3rpc.togRPCError_out hTog) $$ [] as %e ⟨%He, #Hse, #Hgo⟩
  · iframe #
    iapply (v3rpc.srvErrIs_applyErrIs (GoInterface.ok ei) (by intro h; cases h)) $$ Hae
  (try wp_auto)
  iapply HΦ
  iframe HRD Hr Hse
  iright
  isplitr
  · ipureintro; exact ⟨rfl, He⟩
  iexists GoInterface.ok ei
  isplitr
  · ipureintro; nofun
  iexact Hgo))

set_option hygiene false in
/-- A success with the members `sl` (`Hms : membersAt sl ms`): the header, the members, then the
success disjunct (its answer by `Hans`). -/
local macro "promote_ok" Hans:tacticSeq : tactic => `(tactic| (
  (try wp_auto)
  wp_apply (hHdr p s cl) $$ [] as %h -
  · iframe #
  (try wp_auto)
  wp_apply (hM2P sl ms) $$ [Hms] as %psl -
  · iframe
  (try wp_auto)
  iapply HΦ
  iframe HRD Hr
  isplitr
  · iapply go_etcd_io.etcd.cache.v3.srvErrOk_nil
  ileft
  isplitr
  · ipureintro; rfl
  ($Hans)))

theorem v3rpc.ClusterServer.MemberPromote.wp_proof
    (hPM : EtcdServer.PromoteMember.spec (GF := GF) (hG := hG))
    (hHdr : v3rpc.ClusterServer.header.spec (GF := GF) (hG := hG))
    (hM2P : v3rpc.membersToProtoMembers.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG)) :
    v3rpc.ClusterServer.MemberPromote.spec (GF := GF) (hG := hG) := by
  intro p s cl E ρ γr ctx cd tok r dq id Pin Pm Qm Qin Qfw n
  wp_start as ⟨#Hcs, #Hh, #Hq, #Hrd, #Hprt, #Hau, #Hlb, #Hctx, #Hlib, #HtokC, HRD, HPin, HPm, Hr,
    #Hmay, #Hconf, #Hfw⟩
  ihave #Hcs' := Hcs
  iunfold v3rpc.clusterServerIs at Hcs'
  icases Hcs' with ⟨#Hcl, #Hsv⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  wp_apply (hPM s E ρ γr ctx cd tok id Pin Pm Qm Qin (memCfgAns Qfw) n) $$ [$HRD $HPin $HPm]
    as %sl %err ⟨HRD, Hout⟩
  · iframe #
  (try wp_auto)
  icases Hout with (HQ | ⟨%Hne, -, #Hae, -⟩ | ⟨%Hen, HQ⟩ | ⟨%Hne, #Hae⟩)
  · -- `configure`'s answer
    iunfold memCfgAns at HQ
    icases HQ with ⟨HQ, (⟨%Hen, %ms, Hms⟩ | ⟨%Hen, #Hae, -⟩)⟩
    · subst Hen
      promote_ok (ileft; iexists sl; iexact HQ)
    · rcases err with ei | _
      · promote_rpc_err
      · exact absurd rfl Hen
  · rcases err with ei | _
    · promote_rpc_err
    · exact absurd rfl Hne
  · -- the leader's answer
    subst Hen
    iunfold memCfgAns at HQ
    icases HQ with ⟨HQ, (⟨-, %ms, Hms⟩ | ⟨%Hen, -⟩)⟩
    · promote_ok (iright; iexists sl; iexact HQ)
    · exact absurd rfl Hen
  · rcases err with ei | _
    · promote_rpc_err
    · exact absurd rfl Hne

end proof

end EtcdGrove
end Perennial
