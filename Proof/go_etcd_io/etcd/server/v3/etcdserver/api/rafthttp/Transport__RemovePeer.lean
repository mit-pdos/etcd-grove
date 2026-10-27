/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__RemovePeer.lean`:
`(*rafthttp.Transport).RemovePeer(id)` on a live transport, by `RemovePeer_core` (`TransportRemove.lean`; D43 M5a,
2026-10-26).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__RemovePeer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportRemove

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.RemovePeer.wp_proof
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.RemovePeer.spec (GF := GF) (hG := hG) := by
  intro γn t c rs id
  wp_start_folded as Hl
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  ihave #Hst' := Hst
  iunfold trState at Hst'
  icases Hst' with ⟨#Hfix, #Hprb, #Hstp, #Hgd, -⟩
  wp_apply (rafthttp.Transport.RemovePeer_core hPeerStop hIDStringPtr hInfo hWarn hZString (netRh γn) t c.lid
      c.γd c.R c.γs c.γr c.L rs id) $$ [Hg] as Hg
  · iframe; iframe #
  iapply HΦ
  iunfold trLive
  iframe #
  iexact Hg

end proof

end EtcdGrove
end Perennial
