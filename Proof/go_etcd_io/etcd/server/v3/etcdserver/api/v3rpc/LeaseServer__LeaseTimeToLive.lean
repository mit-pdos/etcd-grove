/-
Proof of the spec of the same name (the lease rows at the gRPC level, `notes/lease-grpc-plan.md`).
Lean-first (no Rocq counterpart).

`s.LeaseTimeToLive(ctx, rr)` through the `Lessor` interface (`ls.le`, the server); then
`errors.Is(err, lease.ErrLeaseNotFound)` twice (on `nil` the tree is empty and the answer `false`;
on the server's error, its exact `applyErrIs` tree, so that the two answer the same), a fresh not-found response, or `togRPCError`; then
the header's `fill`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer__LeaseTimeToLive
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

theorem v3rpc.LeaseServer.LeaseTimeToLive.wp_proof
    (hIs : _root_.Perennial.errors.Is.spec (GF := GF) (hG := hG))
    (hTog : v3rpc.togRPCError.spec (GF := GF) (hG := hG))
    (hFill : v3rpc.header.fill.spec (GF := GF) (hG := hG)) :
    v3rpc.LeaseServer.LeaseTimeToLive.spec (GF := GF) (hG := hG) := by
  intro p s A cid mid E γl S ci cd r dq v n m
  wp_start as ⟨#Hls, #HL, HS, HR, #Hctx, #Hpub, #Hllb, Hr⟩
  ihave #Hls' := Hls
  iunfold v3rpc.leaseServerAt at Hls'
  icases Hls' with ⟨%Hpn, #Hhdr, #Hle, -⟩
  iunfold v3rpc.raftLeaseRead at HL
  icases HL with ⟨#HT, -⟩
  iunfold v3rpc.lessorTTLOk at HT
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  ihave ⟨%eNF, #HNF, #HNFe, %HNFl⟩ := v3rpc.leaseNotFoundErr $$ Hlp
  have hpt : ptrTarget (GoInterface.ok eNF) := fun tii h => by cases h; exact HNFl.1
  wp_auto
  wp_apply HT $$ [HS HR Hr] as %resp %err ⟨HS, HR, Hr, Hans⟩
  · iframe; iframe #
  iunfold v3rpc.ttlAns at Hans
  icases Hans with (⟨%He, ⟨%w, Hw, %Hh, %hv, Hhv⟩, #Hauth, #Hchk⟩ | ⟨%Hn, #Hae⟩)
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
    ihave ⟨HR, %dq', Hrev, -⟩ := v3rpc.hdrRev_out A.revR w.Header' hv.Revision' r' $$ [Hkeep Hout]
    · iframe
    (try wp_auto)
    iapply HΦ
    iframe HS HR Hr
    iunfold v3rpc.leaseTTLOut
    ileft
    isplitr
    · ipureintro; rfl
    iexists w
    iframe Hw
    isplitl [Hfd Hrev]
    · iunfold v3rpc.leaseHdrDone
      iframe Hfd
      iexists dq', r'
      iframe Hrev
    ileft
    iframe #
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
        iframe HS HR Hr
        iunfold v3rpc.leaseTTLOut
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
          -- the not-found response `{Header: &pb.ResponseHeader{}, ID: rr.ID, TTL: -1}`
          (try wp_auto)
          ihave ⟨Hr, %Hrn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hr
          iStructNamed Hr
          (try wp_auto)
          ihave Hr : r ↦{dq} v $$ [state ID Keys unknownFields sizeCache]
          · iapply typedPointsto_combine _ _ _ Hrn
            simp only [TypedPointsto.typedPointstoDef]
            iframe
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
          iframe HS HR Hr
          iunfold v3rpc.leaseTTLOut
          ileft
          isplitr
          · ipureintro; rfl
          iexists _
          iframe «$r0»
          isplitl [Hfd Hrev]
          · iunfold v3rpc.leaseHdrDone
            iframe Hfd
            iexists dq', r'
            iframe Hrev
          iright
          ipureintro; rfl

end proof

end EtcdGrove
end Perennial
