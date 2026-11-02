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

theorem v3rpc.LeaseServer.LeaseLeases.wp_proof
    (hIs : _root_.Perennial.errors.Is.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseLeases.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid E γl S ci cd r n m
  wp_start as ⟨#Hls, #HL, HS, HR, #Hctx, #Hpub, #Hllb⟩
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
  wp_apply HLs $$ [HS HR] as %resp %err ⟨HS, HR, Hans⟩
  · iframe; iframe #
  iunfold v3rpc.leasesAns at Hans
  icases Hans with (⟨%He, %i, %ids, %cs, %ms, %Hmi, #Hids, Hresp, #Hchk⟩ | ⟨%Hn, #Hae⟩)
  · subst He
    wp_auto
    -- `errors.Is(nil, ErrLeaseNotFound)`: `false` (an empty tree; `err` nil)
    wp_apply hIs (· = GoInterface.nil) (fun _ _ => True) (fun _ _ => True) GoInterface.nil
        (GoInterface.ok eNF) hpt (fun _ _ h _ _ => by cases h) $$ [] as %b ⟨%Hb1, -⟩
    · isplitr
      · iintro !> %ii %h; cases h
      ipureintro; rfl
    have hb : b = false := by simpa using Hb1 (Or.inl rfl)
    subst hb
    iunfold leasesRespIs at Hresp
    icases Hresp with ⟨%w, Hw, Hh, Hlist⟩
    iunfold srvHeaderAt at Hh
    icases Hh with ⟨%hv, %log, Hhv, #Hcert, %Hlog⟩
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
    iapply HΦ
    iframe HS HR
    iunfold v3rpc.leaseLeasesOut
    ileft
    isplitr
    · ipureintro; rfl
    iexists w
    iframe Hw
    ileft
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
    refine ⟨Hlog.1, fun h0 => ?_⟩
    rw [← Hlog.2.2.2]; exact Hrr (by rw [Hlog.2.2.2]; exact h0)
  · obtain ⟨rfl, Hen⟩ := Hn
    cases err with
    | nil => exact absurd rfl Hen
    | ok ei =>
      (try wp_auto)
      ihave #HTr := applyErrIs_walk _ $$ Hae
      ihave ⟨%S', %I', %U', #Htree, %HS⟩ := HTr $$ %(GoInterface.ok eNF)
      -- `if err != nil && !errors.Is(err, lease.ErrLeaseNotFound)`
      wp_apply hIs S' I' U' (GoInterface.ok ei) (GoInterface.ok eNF) hpt (HS.2.1 hpt) $$ []
        as %b1 ⟨-, %Hw1⟩
      · iframe #; ipureintro; exact HS.1
      cases b1 with
      | false =>
        wp_auto
        wp_apply hTog $$ [] as %e %He
        · iapply srvErrIs_of_applyErrIs _ Hen $$ Hae
        (try wp_auto)
        iapply HΦ
        iframe HS HR
        iunfold v3rpc.leaseLeasesOut
        iright
        ipureintro; exact ⟨rfl, He⟩
      | true =>
        wp_auto
        -- `if errors.Is(err, lease.ErrLeaseNotFound)`, again
        wp_apply hIs S' I' U' (GoInterface.ok ei) (GoInterface.ok eNF) hpt (HS.2.1 hpt) $$ []
          as %b2 ⟨-, %Hw2⟩
        · iframe #; ipureintro; exact HS.1
        cases b2 with
        | false =>
          -- a `true`, then a `false`: impossible, the tree is exact (`applyErrIs_walk`)
          exact absurd (_root_.Perennial.errors.isWalk_det HS.2.2.1 HS.2.2.2
            (Hw1 (by simp) (by simp)) (Hw2 (by simp) (by simp))) (by decide)
        | true =>
          -- the empty listing `{Header: &pb.ResponseHeader{}, Leases: []*pb.LeaseStatus{}}`
          (try wp_auto)
          wp_apply (wp_slice_literal (V := Loc) [])
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hlsl, -⟩
          (try wp_auto)
          ihave %Hvn := typedPointsto_not_null _ _ _ $$ «$v0»
          iStructNamed «$v0»
          ihave Hwh : v3rpc.hdrW «$v0_ptr» $$ [ClusterId MemberId RaftTerm LeaderId]
          · iunfold v3rpc.hdrW
            isplitr
            · ipureintro; exact Hvn
            iexists _, _, _, _
            iframe
          imod (v3rpc.hdrRev_in ⊤ A.revR «$v0_ptr» _) $$ [Revision HR] with ⟨Hin, Hkeep⟩
          · iframe
          wp_apply (hFill _ s A cid mid «$v0_ptr» _) $$ [Hwh Hin] as ⟨Hfd, %r', Hout⟩
          · iframe; iframe #
          ihave ⟨HR, %dq', Hrev, -⟩ := v3rpc.hdrRev_out A.revR «$v0_ptr» _ r' $$ [Hkeep Hout]
          · iframe
          (try wp_auto)
          iapply HΦ
          iframe HS HR
          iunfold v3rpc.leaseLeasesOut
          ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe «$r0»
          iright
          isplitl [Hfd Hrev]
          · iunfold v3rpc.leaseHdrDone
            iframe Hfd
            iexists dq', r'
            iframe Hrev
          iexact Hlsl

end proof

end EtcdGrove
end Perennial
