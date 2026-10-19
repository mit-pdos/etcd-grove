/-
Proof of `Spec/go_etcd_io/etcd/client/v3/keepAlive__close.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.keepAlive__close

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem keepAlive.close.wp_proof : keepAlive.close.spec (GF := GF) (hG := hG) := by
  intro γr ka
  wp_start as Hka
  iunfold kaOwn at Hka
  icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd, %γkd, Hchs, Hchsl, -, -, -, -, -,
    -, -, #Hkd, Hpend, Htoks, -, -⟩
  iunfold kaDone at Hkd
  icases Hkd with ⟨#Hkdf, -⟩
  ihave %Hsll := ownSlice_len $$ Hchsl
  wp_auto
  ihave #Htt : □ (True : IProp GF) $$ []
  · imodintro; itrivial
  wp_apply wp_broadcast_chan_close kd γkd iprop(True) $$ [$Hpend $Htt] as -
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (c0 : GoChan),
      "i" ∷ i_ptr ↦ n ∗ "ch" ∷ ch_ptr ↦ c0 ∗ "Hchsl" ∷ chsS ↦* chs ∗
      "Htoks" ∷ ([∗list] c ∈ chs.drop (sint.nat n), chanTok c) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ chs.length⌝) $$ [i ch Hchsl Htoks]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < chs.length := by word
    have Hc : chs[sint.nat n]? = some (chs[sint.nat n]'Hlt) := List.getElem?_eq_getElem Hlt
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chsS.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index chsS (sint.Z n) _ (DFrac.own 1) (chs[sint.nat n]'Hlt) Hn.1 $$ [Hchsl] as Hchsl
    · iframe; ipureintro; exact Hc
    rw [List.drop_eq_getElem_cons Hlt]
    icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, Htoks⟩
    (try wp_auto)
    wp_apply wp_chanTok_close (chs[sint.nat n]'Hlt) $$ [$Htok]
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, _
    iframe
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    iframe
    ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
