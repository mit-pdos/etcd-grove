/-
Lean-first (no Rocq counterpart).

The proof of `kubernetes.Client.Keys`:
1. `GetPrefixRangeEnd(prefix)` and options `[WithRange(rangeEnd), WithKeysOnly(), WithRev(0)]`;
2. `client_range_any` through the client's `*kv`, with `rangeReply_state_count_bnd`,
   `srvRangeOk_keysPrefix`, and `srvCount_keysPrefix`;
3. `make([][]byte, len(rangeResp.Kvs))` and `slice.forRange` copying each `kv.Key` slice header
   into `resp.Keys[i]`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Keys
public import Spec.go_etcd_io.etcd.client.v3.GetPrefixRangeEnd
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.WithKeysOnly
public import Spec.go_etcd_io.etcd.client.v3.WithRev

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

theorem Client.Keys.wp_proof
    (wp_GetPrefixRangeEnd : GetPrefixRangeEnd.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_WithKeysOnly : WithKeysOnly.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG)) :
    Client.Keys.spec (GF := GF) (hG := hG) := by
  intro _ _ kc ms V ci cd pfx opts Q hrev
  wp_start as ⟨#Hcl, #Hregs, #Hctx, #Hce, #Hau⟩
  wp_auto
  wp_apply wp_GetPrefixRangeEnd pfx
  wp_apply wp_WithRange (prefixRangeEnd pfx) as %f1 #Hf1
  wp_apply wp_WithKeysOnly as %f2 #Hf2
  wp_apply wp_WithRev opts.Revision' as %f3 #Hf3
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  generalize hsl : slice.mk sl _ _ = optsSl
  have hfs :
      (([f1, zero_val GoFunc, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2).set
        (sint.nat (W64 (0 + 1 + 1))) f3) = [f1, f2, f3] := by
    show ([f1, zero_val GoFunc, zero_val GoFunc].set 1 f2).set 2 f3 = [f1, f2, f3]; rfl
  ihave #Hopts :
    optsAt optsSl
      ([withRangeM (prefixRangeEnd pfx), withKeysOnlyM, withRevM (W64 0)] : List (OpFull → OpFull))
    $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · cases Hf; cases Hg; rw [← hrev]; iexact Hf3
    · simp at Hf
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  ihave #Hopts' := optsAt_res optsSl _ iprop(True) $$ Hopts
  ihave #Hrr := client.kvRegs_range ms $$ Hregs
  ihave #Hst' := client.srvStart_both ms $$ Hst
  have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) ⊢
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel pfx
            [withRangeM (prefixRangeEnd pfx), withKeysOnlyM, withRevM (W64 0)])).base.serializable =
            false⌝ ∗ kvReadAu x.γr.kv Q)) :=
    fun _ _ _ => by
      iintro (%h | #h)
      · ileft; ipureintro; exact h
      · iright; iframe h; ipureintro; rfl
  ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  wp_auto
  wp_apply (client.client_range_any api ms (W64 0) ci cd pfx optsSl
      [withRangeM (prefixRangeEnd pfx), withKeysOnlyM, withRevM (W64 0)] iprop(True) Q []) $$ []
    as %rresp %err ⟨-, Hout⟩
  · iframe #
    isplitl []
    · rw [show (opGetModel pfx
          [withRangeM (prefixRangeEnd pfx), withKeysOnlyM, withRevM (W64 0)]).base.sortSet = false
        from rfl]
      iapply sortNamesIf_false
    ipureintro
    refine ⟨?_, rfl⟩
    unfold opGetPanics opFold OpFull.newOp
    simp [withRangeM, withKeysOnlyM, withRevM]
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
  · subst Herr
    ihave Hs := rangeReply_state_count_bnd x.E x.γr (W64 0) x.cid x.mid _ [] Q m rfl rfl $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, hcnt, hrevσ, hb⟩ := Hσ
    rw [rangeWireOf_keysPrefix] at hsel hcnt
    have hkvs := (srvRangeOk_keysPrefix pfx σ.kvs m.kvs m.more hsel).1
    rw [srvCount_keysPrefix] at hcnt
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl2, %ps, #Hh, #Hhf, #Hkvf2, #Hsl2, #Hkvs, #Hmore, #Hcount⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl2
    wp_auto
    wp_apply wp_slice_make2 (V := GoSlice) sl2.len $$ [] as %ksl0 ⟨Hksl0, -⟩
    · ipureintro; exact Hsll.2
    ihave %Hksl0_len := ownSlice_len _ _ _ $$ Hksl0
    -- `slice.forRange` counter is `i_ptr`; Go loop variable `i` is `igo`
    rename_i igo
    irename : (igo ↦ zero_val w64 : IProp GF) => Higo
    ihave IH : iprop(∃ (n iv : w64) (kvp : Loc) (ksls : List GoSlice),
        "i" ∷ i_ptr ↦ n ∗
        "Higo" ∷ igo ↦ iv ∗
        "kv" ∷ kv_ptr ↦ kvp ∗
        "resp" ∷ resp_ptr ↦ go_etcd_io.etcd.client.v3.kubernetes.KeysResponse.mk ksl0 (W64 0) (W64 0) ∗
        "rangeResp" ∷ rangeResp_ptr ↦ rresp ∗
        "Hksl0" ∷ ksl0 ↦* ksls ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ps.length : Int) ∧ ksls.length = ps.length⌝ ∗
        "#Hdone" ∷ □ (∀ (j : Nat) (ksl : GoSlice) (v : EtcdKv),
          ⌜j < sint.nat n⌝ -∗ ⌜ksls[j]? = some ksl⌝ -∗ ⌜m.kvs[j]? = some v⌝ -∗ ksl ↦*□ v.key))
      $$ [i Higo kv resp rangeResp Hksl0]
    · iexists W64 0, _, _, _
      simp only [named]
      iframe
      isplitr
      · ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [List.length_replicate, Hsll.1]
      imodintro
      iintro %j %ksl %v %hj
      exfalso
      rw [show sint.nat (W64 0) = 0 from rfl] at hj
      omega
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < ps.length := by word
      obtain ⟨p0, Hp0⟩ : ∃ p0, ps[sint.nat n]? = some p0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨v0, Hv0⟩ : ∃ v0, m.kvs[sint.nat n]? = some v0 :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl2.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl2 (sint.Z n) ps DFrac.discard p0 Hn.1 $$ [Hsl2] as -
      · iframe Hsl2; ipureintro; exact Hp0
      ihave #Hkv0 := Hall $$ %(sint.nat n) %p0 %v0 %Hp0 %Hv0
      iunfold txn.kvIs at Hkv0
      icases Hkv0 with ⟨%ksl_n, %vsl_n, #Hkfield, #Hkbytes, -⟩
      wp_auto
      have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksl0.len := by
        refine ⟨Hn.1, ?_⟩
        have h1 := Hksl0_len.1
        rw [List.length_replicate] at h1
        word
      simp only [Hbnd2, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index ksl0 (sint.Z n) ksls ksl_n $$ [$Hksl0] as Hksl0
      · ipureintro
        refine ⟨Hn.1, ?_⟩
        rw [Hn.2.2]
        word
      wp_for_post
      iframe
      iexists (n + W64 1), n, p0, ksls.set (sint.Z n).toNat ksl_n
      simp only [named]
      iframe
      isplitr
      · ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [List.length_set, Hn.2.2]
      imodintro
      iintro %j %ksl %v %hj %hksl %hv
      have hjn : j ≤ sint.nat n := by
        have : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        omega
      rcases Nat.eq_or_lt_of_le hjn with rfl | hjlt
      · have hidx : (sint.Z n).toNat < ksls.length := by rw [Hn.2.2]; exact Hlt
        rw [show sint.nat n = (sint.Z n).toNat from rfl, List.getElem?_set_self hidx] at hksl
        cases hksl
        rw [Hv0] at hv
        cases hv
        iexact Hkbytes
      · rw [show (sint.Z n).toNat = sint.nat n from rfl, List.getElem?_set_ne (by omega)] at hksl
        iapply Hdone $$ %j %ksl %v %hjlt %hksl %hv
    · have hn : sint.nat n = ps.length := by word
      iapply HΦ
      ileft
      isplitl []
      · ipureintro; rfl
      iexists σ
      iframe HQ
      isplitl []
      · ipureintro
        exact ⟨hrevσ, hcnt, hb⟩
      iunfold keysSlice
      iexists ksls
      iframe Hksl0
      isplitr
      · ipureintro
        rw [← hkvs, List.length_map, ← Hlen, Hn.2.2]
      iintro %j %ksl %k %hksl %hk
      rw [← hkvs, List.getElem?_map] at hk
      cases hmv : m.kvs[j]? with
      | none => rw [hmv] at hk; simp at hk
      | some v =>
        rw [hmv] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        subst hk
        have hj : j < sint.nat n := by
          rw [hn, ← Hn.2.2]
          rcases Nat.lt_or_ge j ksls.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hksl; cases hksl
        iapply Hdone $$ %j %ksl %v %hj %hksl %hmv
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iright
    iunfold kvErr at Hke
    icases Hke with ⟨%Hce, #Hse, -⟩
    iframe Hse
    isplitl []
    · ipureintro; exact Herr
    ipureintro; exact Hce

end proof

end kubernetes
end EtcdGrove
end Perennial
