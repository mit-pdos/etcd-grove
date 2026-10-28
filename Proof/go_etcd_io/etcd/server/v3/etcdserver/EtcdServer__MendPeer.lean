/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__MendPeer.lean`. Lean-first (no Rocq
counterpart); the partition plan's stage S2 (2026-10-20). The type assertion on `s.r.transport`
succeeds: `srvNetMember` says the field holds the frozen `*rafthttp.Transport` `τ.t`
(`transportIface τ.t`), on which the transport's spec applies (with a reader's token, 2026-10-24).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MendPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__MendPeer

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

theorem EtcdServer.MendPeer.wp_proof
    (wp_MendPeer : rafthttp.Transport.MendPeer.spec (GF := GF) (hG := hG)) :
    EtcdServer.MendPeer.spec (GF := GF) (hG := hG) := by
  intro hpp γn s mid id τ
  wp_start as ⟨#Hm, Htok⟩
  iunfold srvNetMember at Hm
  icases Hm with ⟨-, #Htr, %Hlid, #Hst, -, -⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  wp_auto
  iunfold srvTrTok at Htok
  icases Htok with ⟨Htok, Hnrs⟩
  -- (D22 J-T) `id` has no remote: not budgeted, or its token (the peer control's)
  by_cases hL : id ∈ τ.c.L
  · icases BigSepL.bigSepL_mem_acc (Φ := fun f => trNoRem τ.c f) hL $$ Hnrs with ⟨Hn, Hback⟩
    wp_apply (wp_MendPeer hpp γn τ.t τ.c id) $$ [Htok Hn] as ⟨Htok, Hn⟩
    · iframe; iframe #; iunfold trNoRemOr; iright; iexact Hn
    iapply HΦ
    iunfold srvTrTok
    iframe Htok
    iapply Hback
    iunfold trNoRemOr at Hn
    icases Hn with (%Hc | Hn)
    · exact absurd hL Hc
    · iexact Hn
  · wp_apply (wp_MendPeer hpp γn τ.t τ.c id) $$ [Htok] as ⟨Htok, -⟩
    · iframe; iframe #; iunfold trNoRemOr; ileft; ipureintro; exact hL
    iapply HΦ
    iunfold srvTrTok
    iframe

end proof

end EtcdGrove
end Perennial
