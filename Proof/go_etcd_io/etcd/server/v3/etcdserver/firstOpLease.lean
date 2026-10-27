/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/firstOpLease.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstOpLease
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RequestOp__GetRequest
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.PutRequest__GetLease

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem firstOpLease.wp_proof (hGR : RequestOp.GetRequest.spec (GF := GF) (hG := hG))
    (hPL : PutRequest.GetLease.spec (GF := GF) (hG := hG)) :
    firstOpLease.spec (GF := GF) (hG := hG) := by
  intro sl ps ops
  wp_start as ⟨#Hsl, #Hops⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (v : Loc), "i" ∷ i_ptr ↦ n ∗ "operation" ∷ operation_ptr ↦ v ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i operation]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    ihave ⟨%op, -, #Hop⟩ := txn.requestOpsIs_elem ps ops (sint.nat n) p Hp $$ Hops
    icases txn.requestOpIs_req p op $$ Hop with ⟨%Hpn, %u, %w, #Hu, Hcase⟩
    wp_apply wp_load_slice_index sl (sint.Z n) _ DFrac.discard p Hn $$ [] as -
    · iframe #; ipureintro; exact Hp
    try wp_auto
    wp_apply hGR p u $$ []
    · iframe #; ipureintro; exact Hpn
    icases Hcase with (⟨%H, -⟩ | ⟨%H, %r, %o, #Hw, #Hr⟩ | ⟨%H, -⟩ | %H) <;> subst H
    rotate_left
    · wp_auto
      iunfold txn.putRequestIs at Hr
      icases Hr with ⟨%Hnn, %ksl, %vsl, %k, %vv, %lease, %pk, %iv, %il, -, -, -, -, #HL, -⟩
      wp_apply hPL r lease $$ []
      · iframe #; ipureintro; exact Hnn
      try wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    all_goals
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro; word
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
