/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/setPeerURLsHeader.lean` (rafthttp
stage 6e, 2026-10-24). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.setPeerURLsHeader
public import Spec.strings.Join

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

theorem rafthttp.setPeerURLsHeader.wp_proof
    (hURLString : http.URLStringAny_spec (GF := GF))
    (hJoin : strings.Join.spec (GF := GF) (hG := hG))
    (hSet : http.HeaderSetPtr_spec (GF := GF)) :
    rafthttp.setPeerURLsHeader.spec (GF := GF) (hG := hG) := by
  intro r R urls uvs
  wp_start as ⟨Hreq, #Hurls⟩
  iunfold http.reqOwn at Hreq
  icases Hreq with ⟨%hm, #Hhf, Hhm, Hrest⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iexists R.hdr
    isplitr
    · ipureintro; intro k _; rfl
    iunfold http.reqOwn
    iexists hm
    iframe; iframe #
  ihave %Hul := ownSlice_len _ _ _ $$ Hurls
  wp_method_call
  wp_call
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_slice_make2 (V := GoString) as %pu ⟨Hpu, Hpucap⟩
  · ipureintro; exact Hul.2
  (try wp_auto)
  -- `for i := range urls { peerURLs[i] = urls[i].String() }`
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HF : (∃ (k iv : w64) (xs : List GoString),
      "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "Hpu" ∷ pu ↦* xs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z urls.len ∧ xs.length = uvs.length⌝ : IProp GF)
    $$ [i Hiu Hpu]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, Hul.2, ?_⟩
    rw [List.length_replicate, Hul.1]
  wp_for HF
  obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
  (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z urls.len := ⟨Hk1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem uvs (sint.nat k) as u
    -- the range's element, loaded (unused: the body indexes `urls` again)
    wp_apply (wp_load_slice_index urls (sint.Z k) uvs DFrac.discard u Hk1) $$ [] as -
    · iframe #; ipureintro; exact Hu_lookup
    (try wp_auto)
    (try simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave ⟨Hu, -⟩ := (ownSlice_elem_acc (sint.Z k) u urls DFrac.discard uvs Hk1 Hu_lookup) $$ Hurls
    wp_apply (hURLString _ DFrac.discard u) $$ [Hu] as %us -
    · iexact Hu
    (try wp_auto)
    ihave %Hpul := ownSlice_len $$ Hpu
    have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z pu.len := by
      constructor
      · exact Hk1
      · have : xs.length = uvs.length := Hk3
        word
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hpu] as Hpu
    · iframe; ipureintro; constructor <;> word
    wp_for_post
    iframe
    iexists k + W64 1, k, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hk3]⟩
  -- `req.Header.Set("X-PeerURLs", strings.Join(peerURLs, ","))`
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hJoin $$ [Hpu] as %js Hpu
  · iframe; try iframe #
  (try wp_auto)
  wp_apply (hSet _ hm R.hdr _ _) $$ [Hhm] as Hhm
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexists _
  isplitr
  · ipureintro; intro k hk; exact http.hdrGet_hdrSet_ne R.hdr _ k js (Ne.symm hk)
  iunfold http.reqOwn
  iexists hm
  iframe; iframe #
  iunfold http.reqRest at Hrest
  iunfold http.reqRest
  iexact Hrest

end proof

end EtcdGrove
end Perennial
