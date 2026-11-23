/-
Proof of the spec of the same name (the lease rows at the gRPC level, `notes/lease-grpc-plan.md`).
Lean-first (no Rocq counterpart).

`s.LeaseLeases(ctx, rr)` through the `Lessor` interface (`ls.le`, the server); then
`errors.Is(err, lease.ErrLeaseNotFound)` twice (as `LeaseTimeToLive`'s handler), an empty listing,
or `togRPCError`; then the header's `fill`, the server's header revision kept unless `0`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.togRPCError
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.TogRPCErrorPlain
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header__fill
public import Perennial.Spec.errors.Is
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV

@[expose] public section

set_option linter.unusedSectionVars false
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
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem v3rpc.LeaseServer.LeaseLeases.wp_proof
    (hIs : _root_.Perennial.errors.Is.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseLeases.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid E γl S ci cd tok r n m
  wp_start as ⟨#Hls, #HL, HS, HR, #Hctx, #Hlib, #HtokC, #Hpub, #Hllb⟩
  ihave #Hls' := Hls
  iunfold v3rpc.leaseServerAt at Hls'
  icases Hls' with ⟨%Hpn, #Hhdr, #Hle, -⟩
  iunfold v3rpc.raftLeaseRead at HL
  icases HL with ⟨-, #HLs⟩
  iunfold v3rpc.lessorLeasesOk at HLs
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave ⟨%eNF, #HNF, #HNFe, %HNFl⟩ := v3rpc.leaseNotFoundErr $$ Hlp
  have hpt : ptrTarget (GoInterface.ok eNF) := fun tii h => by cases h; exact HNFl.1
  wp_auto
  wp_apply HLs $$ %ci %tok %cd %r %n %m [HS HR] as %resp %err ⟨HS, HR, Hans⟩
  · iframe; iframe #
  iunfold v3rpc.leasesAns at Hans
  icases Hans with (⟨%He, %i, %ids, %cs, %ms, %Hmi, #Hids, Hresp, #Hchk⟩ | ⟨%Hn, #Hae, #Hnf⟩)
  · subst He
    wp_auto
    -- `errors.Is(nil, ErrLeaseNotFound)`: `false` (an empty tree; `err` nil)
    wp_apply hIs (· = GoInterface.nil) (fun _ _ => True) (fun _ _ => True) GoInterface.nil
        (GoInterface.ok eNF)
        (_root_.Perennial.errors.comparableTarget_pointer _ _ hpt (fun _ _ h _ _ => by cases h)) $$ [] as %b ⟨%Hb1, -⟩
    · isplitr
      · iintro !> %ii %h; cases h
      ipureintro; rfl
    have hb : b = false := by simpa using Hb1 (Or.inl rfl)
    subst hb
    iunfold leasesRespIs at Hresp
    icases Hresp with ⟨%w, Hw, Hh, Hlist⟩
    iunfold srvHeaderAt at Hh
    icases Hh with ⟨%hv, %log, Hhv, #Hcert, -, -, %Hlog⟩
    ihave %Hh := typedPointsto_not_null _ _ _ $$ Hhv
    wp_auto
    -- `ls.hdr.fill(resp.Header)`
    iStructNamed Hhv
    ihave Hwh : v3rpc.hdrW w.Header' $$ [ClusterId MemberId RaftTerm LeaderId]
    · iunfold v3rpc.hdrW
      isplitr
      · ipureintro; exact Hh
      iexists _, _, _, _
      iframe
    imod (v3rpc.hdrRev_in ⊤ A.revR w.Header' hv.Revision') $$ [Revision HR] with ⟨Hin, Hkeep⟩
    · iframe
    wp_apply (hFill _ s A cid mid w.Header' hv.Revision') $$ [Hwh Hin] as ⟨Hfd, %r', Hout⟩
    · iframe; iframe #
    ihave ⟨HR, %dq', Hrev, %Hrr⟩ := v3rpc.hdrRev_out A.revR w.Header' hv.Revision' r' $$ [Hkeep Hout]
    · iframe
    (try wp_auto)
    ihave #HSn := go_etcd_io.etcd.cache.v3.srvErrOk_nil (GF := GF)
    iapply HΦ
    iframe HSn
    iframe HS HR
    iunfold v3rpc.leaseLeasesOut
    ileft
    isplitr
    · ipureintro; rfl
    iexists w
    iframe Hw
    iexists i, ids
    iframe Hlist
    iframe #
    isplitr
    · ipureintro; exact Hmi
    iunfold v3rpc.leasesHdrDone
    iframe Hfd
    iexists dq', r', log
    iframe Hrev
    iframe #
    ipureintro
    refine ⟨Hlog.2.1, fun h0 => ?_⟩
    rw [← Hlog.2.2.2.2]; exact Hrr (by rw [Hlog.2.2.2.2]; exact h0)
  · obtain ⟨rfl, Hen, HaOn⟩ := Hn
    cases err with
    | nil => exact absurd rfl Hen
    | ok ei =>
      (try wp_auto)
      ihave #HTr := applyErrIs_walk _ $$ Hae
      ihave ⟨%S', %I', %U', #Htree, %HS⟩ := HTr $$ %(GoInterface.ok eNF)
      -- `if err != nil && !errors.Is(err, lease.ErrLeaseNotFound)`
      wp_apply hIs S' I' U' (GoInterface.ok ei) (GoInterface.ok eNF)
        (_root_.Perennial.errors.comparableTarget_pointer _ _ hpt (HS.2.1 hpt)) $$ []
        as %b1 ⟨-, %Hw1⟩
      · iframe #; ipureintro; exact HS.1
      cases b1 with
      | false =>
        wp_auto
        wp_apply (v3rpc.togRPCError_plain hTog) $$ [] as %e ⟨%He, #HSn⟩
        · iapply srvErrIs_of_applyErrIs _ Hen $$ Hae
        (try wp_auto)
        iapply HΦ
        iframe HSn
        iframe HS HR
        iunfold v3rpc.leaseLeasesOut
        iright
        ipureintro; exact ⟨rfl, He, HaOn⟩
      | true =>
        -- `LeaseLeases` never returns `ErrLeaseNotFound` (Freeze §4.4 F4)
        ihave Hit : errIsTrue (GF := GF) (GoInterface.ok ei) (GoInterface.ok eNF) $$ []
        · iunfold errIsTrue
          iexists S', I', U'
          iframe Htree
          ipureintro; exact ⟨HS.1, HS.2.2, Hw1 (by simp) (by simp)⟩
        iexfalso
        iapply Hnf $$ %eNF HNF Hit

end proof

end EtcdGrove
end Perennial
