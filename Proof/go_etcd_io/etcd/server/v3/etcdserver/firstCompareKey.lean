/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/firstCompareKey.lean`. Lean-first (no Rocq
counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.firstCompareKey
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetKey

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem firstCompareKey.wp_proof (hGK : Compare.GetKey.spec (GF := GF) (hG := hG)) :
    firstCompareKey.spec (GF := GF) (hG := hG) := by
  intro sl ps cs
  wp_start as ⟨#Hsl, #Hcs⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  iunfold txn.comparesIs at Hcs
  icases Hcs with ⟨%Hcl, #Hcs⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (v : Loc), "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ v ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i op]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨cm, Hcm⟩ : ∃ cm, cs[sint.nat n]? = some cm :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #Hc := Hcs $$ %(sint.nat n) %p %cm %Hp %Hcm
    iunfold txn.compareIs at Hc
    icases Hc with ⟨%Hpn, %ksl, %esl, %e, %u, -, -, #Hk, #Hks, -⟩
    wp_apply wp_load_slice_index sl (sint.Z n) _ DFrac.discard p Hn $$ [] as -
    · iframe #; ipureintro; exact Hp
    try wp_auto
    wp_apply hGK p ksl $$ []
    · iframe #; ipureintro; exact Hpn
    wp_apply wp_bytes_to_string $$ [Hks] as -
    · iexact Hks
    try wp_auto
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro; word
    · wp_for_post
      iapply HΦ
      itrivial
  · try wp_auto
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
