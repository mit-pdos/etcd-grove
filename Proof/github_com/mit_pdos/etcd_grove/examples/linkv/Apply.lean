/-
Lean-first (no Rocq counterpart).

The proof of `Apply(cli, input)` (D20 (c)): `NewProph()` gives a prophecy of the `ResolveBool` at
the end (`!out.Err`, the call's outcome), and the commit (`Inv.lean`'s steps) is chosen by its
head before the client is called:

- a put, prophecy `ok`: the client's update is `put_ok_au` (ordinary, fired at most once on a
  client that sends a write at most once, `clientWriteOnce`); it commits `lintest`'s update at the server's
  apply with output `ok`, and `Put`'s success returns its continuation. An error return
  contradicts the prophecy.
- a put, prophecy error: commit now, the put pending (`put_err_commit`); the client's update is
  `put_pend_au`, whose firing (during the call, after it, or never) is the pending put's late
  effect. One model step covers both a failed put the server applied and one it did not: the
  output step adds the pending put, the late effect is in the closed set. A success return
  contradicts the prophecy.
- a get, prophecy error: commit now with `Err` (`get_err_commit`); `Get` without an update. A
  success return (stepped through the reply) contradicts the prophecy.
- a get, prophecies `ok` and revision `R` (the second prophecy, `rp`, resolved with the reply's
  header revision): a call invariant (`callInv`) holds `lintest`'s update with a later credit and
  the commit bit `γc` at `none`; the client's read update is `get_ok_au`, persistent: at each
  firing at a state of revision `R` it commits once (the bit goes to the store's value, read-only)
  and later firings at `R` see the same store (the revisions' map in `linkvInv`). After the reply
  (`client_Get_st`: `□ Q σ` at the state read, whose revision is the header's),
  `ResolveU64` gives `R = m.hdr.revision`, so `Q σ` gives the bit at the reply's value, and
  `Apply` takes the continuation (`callInv_take`, with its token and a second credit). A revision
  that is not the reply's contradicts the resolution; an error return contradicts the first.

The client's calls are the client package's (`client/v3/ClientPutGet.lean`, D31: `client_Put_st`,
`client_Get_st`), at the client's one member, on a client that sends a write at most once
(`clientWriteOnce`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Apply
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]


theorem zero_val_Output :
    (zero_val github_com.mit_pdos.etcd_grove.examples.linkv.Output) = okOut := rfl

theorem Apply.wp_proof : Apply.spec (GF := GF) (hG := hG) := by
  intro _ γ cl ep V E γr cid mid hAs
  iintro #Hpkg #Pcli #Hcl #Hone #Hput #Hrange #Hinv
  -- the client's one member, as the client package's calls take it (`client/v3/ClientPutGet.lean`)
  let x0 : client.SrvAt GF := ⟨ep, E, γr, cid, mid⟩
  ihave #Hput1 : [∗list] y ∈ [x0], isGrpcRpc y.addr go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpec y.E y.γr y.cid y.mid) $$ []
  · iapply BigSepL.bigSepL_singleton.2; iexact Hput
  ihave #Hrange1 : [∗list] y ∈ [x0], isGrpcRpc y.addr go!"/etcdserverpb.KV/Range"
      (client.etcdRangeSpec y.E y.γr y.cid y.mid) $$ []
  · iapply BigSepL.bigSepL_singleton.2; iexact Hrange
  ihave #Hcl1 : isNewClient cl ([x0].map client.SrvAt.addr) V $$ []
  · iExactEq Hcl; rfl
  ihave #Hone1 : client.clientWriteOnce (GF := GF) cl ([x0].map client.SrvAt.addr) $$ []
  · iExactEq Hone; rfl
  iintro %i
  imodintro
  iintro %Φ %Hin HAU
  obtain ⟨x, rfl, Hgen⟩ := Hin
  wp_func_call
  wp_call
  wp_auto_lc 2
  wp_apply (wp_NewProph_typed (τ := Bool) github_com.goose_lang.primitive.wp_NewProph) as %p %xs Hp
  wp_apply (wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph) as %rp %rs Hrp
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  imod monoNatLbOwn_0 (GF := GF) γr.committed with #Hc0
  ihave #Hc0' : committedAtLeast (GF := GF) γr (W64 0) $$ []
  · iunfold committedAtLeast
    iExactEq Hc0; rfl
  ihave #HF1 : [∗list] y ∈ [x0], mvcc.idxCert y.E.γ.idx [] $$ []
  · iapply BigSepL.bigSepL_singleton.2; iexact HF0
  ihave #Hst1 : [∗list] y ∈ [x0], client.srvStart y $$ []
  · iapply BigSepL.bigSepL_singleton.2; iunfold client.srvStart; iframe #
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  cases hP : x.Put'
  · wp_pures
    by_cases Hok : xs.head? = some true
    · -- the prophecies say `ok` at revision `R`: the read update commits at its first firing at
      -- a state of revision `R` (`get_ok_au`), and `Apply` takes the continuation after the reply
      imod dghostVar_alloc (GF := GF) (none : Option (Option GoString)) with ⟨%γc, Hγc⟩
      imod dghostVar_alloc (GF := GF) () with ⟨%γt, Htok⟩
      imod inv_alloc callN ⊤ (iprop(
          (linU γ (boxIn x) Φ ∗ £ 1 ∗
            dghostVar γc (DFrac.own 1) (none : Option (Option GoString))) ∨
          (∃ (v : Option GoString) (L : List (GoString × GoString)),
            dghostVar γc DFrac.discard (some v) ∗
            ghostMapElem γ.r (uint.nat (rs.headD (W64 0))) DFrac.discard L ∗
            ⌜v = absP L x.Key'⌝ ∗
            ((linkvS.ioOk (boxIn x) (boxOut (getOut v)) -∗ Φ #(boxOut (getOut v))) ∨
              dghostVar γt (DFrac.own 1) ())))) $$ [HAU Hlc1 Hγc] with #Hci
      · inext
        ileft
        iframe Hlc1 Hγc
        iunfold linU
        iexact HAU
      ihave #Hc : callInv γ γc γt x (rs.headD (W64 0)) Φ $$ []
      · iunfold callInv; iexact Hci
      ihave #Hau := get_ok_au γ γr.kv γc γt x hP (rs.headD (W64 0)) Φ $$ []
      · iframe #
      wp_auto
      ihave #Hau2 : iprop(⌜getQ γc x (rs.headD (W64 0)) = (fun _ => iprop(True) : KVState → IProp GF)⌝ ∨
          kvReadAu (GF := GF) x0.γr.kv (getQ γc x (rs.headD (W64 0)))) $$ []
      · iright; iexact Hau
      ihave #Hau1 : □ ([∧list] y ∈ [x0], ⌜getQ γc x (rs.headD (W64 0)) = (fun _ => iprop(True) : KVState → IProp GF)⌝ ∨
          kvReadAu (GF := GF) y.γr.kv (getQ γc x (rs.headD (W64 0)))) $$ []
      · imodintro
        iapply BigAndL.bigAndL_singleton.2
        iexact Hau2
      wp_apply (client.client_Get_st cl [x0] V context.backgroundCtxVal cd x.Key' slice.nil
          (getQ γc x (rs.headD (W64 0)))) $$ [] as %resp %err Hout
      · iframe #
      icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hkvs, %Hrev, %Hbnd⟩ | %Herr)
      · have Hval : m.kvs.head?.map EtcdKv.value = absKV σ x.Key' := by
          rw [Hkvs, client.head_filter_key]; rfl
        subst Herr
        iunfold rangeRespMsg at Hm
        icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
        iunfold hdrFull at Hhf
        icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
        wp_auto
        iunfold txn.kvsIs at Hkvs
        icases Hkvs with ⟨%Hlen, #Hall⟩
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        wp_if_destruct
        · obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
            have : 0 < ps.length := by have := Hsll.1; word
            exact ⟨ps[0], List.getElem?_eq_getElem this⟩
          obtain ⟨kv0, Hkv0⟩ : ∃ kv0, m.kvs[0]? = some kv0 := by
            have : 0 < m.kvs.length := by
              rw [← Hlen]; exact List.length_pos_of_mem (List.mem_of_getElem? Hp0)
            exact ⟨m.kvs[0], List.getElem?_eq_getElem this⟩
          ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
          iunfold txn.kvIs at Hkv
          icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
          have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
            have := Hsll.1
            constructor <;> word
          simp only [Hbnd0, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
          · iframe Hsl; ipureintro; exact Hp0
          wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
          · iframe #
          wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          by_cases HR : rs.headD (W64 0) = m.hdr.revision
          rotate_left
          · wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
              rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
            · iframe
            exact absurd (by rw [Hrs]; rfl) HR
          have Hσr : σ.rev = uint.nat (rs.headD (W64 0)) := by rw [HR, Hrev]; word
          iunfold getQ at HQ
          ihave #Hv := HQ $$ %Hσr
          iapply fupd_wp
          imod (callInv_take γ γc γt x (rs.headD (W64 0)) Φ (absKV σ x.Key')) $$ [Htok Hlc2]
            with HΦ
          · iframe Hc Hv Htok Hlc2
          imodintro
          wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
            rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
          · iframe
          have Hg : getOut (absKV σ x.Key') = ⟨false, true, kv0.value⟩ := by
            rw [← Hval]
            cases hk : m.kvs with
            | nil => simp [hk] at Hkv0
            | cons a l => simp [hk] at Hkv0; subst Hkv0; rfl
          rw [Hg]
          iapply HΦ
          simp only [linkvS]
          ipureintro; exact ⟨x, _, rfl, rfl⟩
        · wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          by_cases HR : rs.headD (W64 0) = m.hdr.revision
          rotate_left
          · wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
              rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
            · iframe
            exact absurd (by rw [Hrs]; rfl) HR
          have Hσr : σ.rev = uint.nat (rs.headD (W64 0)) := by rw [HR, Hrev]; word
          iunfold getQ at HQ
          ihave #Hv := HQ $$ %Hσr
          iapply fupd_wp
          imod (callInv_take γ γc γt x (rs.headD (W64 0)) Φ (absKV σ x.Key')) $$ [Htok Hlc2]
            with HΦ
          · iframe Hc Hv Htok Hlc2
          imodintro
          wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
            rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
          · iframe
          have Hg : getOut (absKV σ x.Key') = okOut := by
            rw [← Hval]
            have : m.kvs = [] := by
              apply List.eq_nil_of_length_eq_zero
              rw [← Hlen]; have := Hsll.1; word
            simp [this, getOut]
          rw [zero_val_Output]
          rw [Hg]
          iapply HΦ
          simp only [linkvS]
          ipureintro; exact ⟨x, _, rfl, rfl⟩
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
    · -- the prophecy says error: commit now
      iapply fupd_wp
      imod (get_err_commit γ γr.kv x hP Φ) $$ [HAU] with HΦ
      · iframe Hinv; iunfold linU; iexact HAU
      imodintro
      wp_auto
      ihave #Hau0 : □ ([∧list] y ∈ [x0], ⌜(fun _ => iprop(True) : KVState → IProp GF) =
          (fun _ => iprop(True) : KVState → IProp GF)⌝ ∨
          kvReadAu (GF := GF) y.γr.kv (fun _ => iprop(True) : KVState → IProp GF)) $$ []
      · imodintro
        iapply BigAndL.bigAndL_singleton.2
        ileft; ipureintro; rfl
      wp_apply (client.client_Get_st cl [x0] V context.backgroundCtxVal cd x.Key' slice.nil
          (fun _ => iprop(True))) $$ [] as %resp %err Hout
      · iframe #
      icases Hout with (⟨%Herr, %m, %σ, #Hm, -, -⟩ | %Herr)
      · subst Herr
        iunfold rangeRespMsg at Hm
        icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
        iunfold hdrFull at Hhf
        icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
        wp_auto
        iunfold txn.kvsIs at Hkvs
        icases Hkvs with ⟨%Hlen, #Hall⟩
        ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
        wp_if_destruct
        · obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
            have : 0 < ps.length := by have := Hsll.1; word
            exact ⟨ps[0], List.getElem?_eq_getElem this⟩
          obtain ⟨kv0, Hkv0⟩ : ∃ kv0, m.kvs[0]? = some kv0 := by
            have : 0 < m.kvs.length := by
              rw [← Hlen]; exact List.length_pos_of_mem (List.mem_of_getElem? Hp0)
            exact ⟨m.kvs[0], List.getElem?_eq_getElem this⟩
          ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
          iunfold txn.kvIs at Hkv
          icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
          have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
            have := Hsll.1
            constructor <;> word
          simp only [Hbnd, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
          · iframe Hsl; ipureintro; exact Hp0
          wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
          · iframe #
          wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          simp [Hxs] at Hok
        · wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
            p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
          · iframe
          simp [Hxs] at Hok
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, p, Hp⟩
        · iframe
        wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
          rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
        · iframe
        iapply HΦ
        simp only [linkvS]
        ipureintro; exact ⟨x, errOut, rfl, rfl⟩
  · wp_pures
    by_cases Hok : xs.head? = some true
    · -- the prophecy says `ok`: the update the server fires commits
      ihave Hau := put_ok_au γ γr.kv x hP Φ $$ [HAU]
      · iframe Hinv; iunfold linU; iexact HAU
      wp_auto
      wp_apply (client.client_Put_st cl [x0] V context.backgroundCtxVal cd x.Key' x.Val'
          slice.nil _) $$ [Hau] as %resp %err Hout
      · iframe #
        iapply BigAndL.bigAndL_singleton.2; iexact Hau
      icases Hout with (⟨%Herr, %m, %σ, -, HΦ, -⟩ | %Herr)
      · subst Herr
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, p, Hp⟩
        · iframe
        wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
          rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
        · iframe
        rw [zero_val_Output]
        iapply HΦ
        simp only [linkvS]
        ipureintro; exact ⟨x, okOut, rfl, rfl⟩
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
    · -- the prophecy says error: commit now, the put pending
      iapply fupd_wp
      imod (put_err_commit γ γr.kv x hP Φ) $$ [HAU] with ⟨%n, HΦ, Htok⟩
      · iframe Hinv; iunfold linU; iexact HAU
      ihave Hau := put_pend_au γ γr.kv n x.Key' x.Val' $$ [Htok]
      · iframe Hinv; iexact Htok
      imodintro
      wp_auto
      wp_apply (client.client_Put_st cl [x0] V context.backgroundCtxVal cd x.Key' x.Val'
          slice.nil _) $$ [Hau] as %resp %err Hout
      · iframe #
        iapply BigAndL.bigAndL_singleton.2; iexact Hau
      icases Hout with (⟨%Herr, -⟩ | %Herr)
      · subst Herr
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, -, -⟩
        · iframe
        simp [Hxs] at Hok
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei => ?_
        wp_auto
        wp_apply (wp_ptr_ResolveBool_typed github_com.goose_lang.primitive.ProphId.wp_ResolveBool
          p_ptr _ p xs _) $$ [p Hp] as %xs' ⟨%Hxs, p, Hp⟩
        · iframe
        wp_apply (wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64
          rp_ptr _ rp rs _) $$ [rp Hrp] as %rs' ⟨%Hrs, -, -⟩
        · iframe
        iapply HΦ
        simp only [linkvS]
        ipureintro; exact ⟨x, errOut, rfl, rfl⟩

end proof

end linkv
end EtcdGrove
end Perennial
