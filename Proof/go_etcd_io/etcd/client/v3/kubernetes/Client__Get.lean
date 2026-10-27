/-
Lean-first (no Rocq counterpart).

The proof of `kubernetes.Client.Get`: the options `[WithRev(0), WithLimit(1)]`, then
`client_range_any` through the client's `*kv` (as linkvtxn's `client_Get_st`), and the response's
`KV` from the selection (`srvRangeOk_getKey1`; not `nil`: `kvIs_ne_null`). The prophecy
(`NewProph`, then the two `ResolveU64`s) is of the response's revision and the key's mod
revision: the read update used is `Q` at the prophesied pair, which the resolutions show is the
response's.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithLimit
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Proph
public import Perennial.Proof.github_com.goose_lang.primitive.Link

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

theorem Client.Get.wp_proof (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithLimit : WithLimit.spec (GF := GF) (hG := hG)) :
    Client.Get.spec (GF := GF) (hG := hG) := by
  intro _ _ kc ms V ci cd key opts Q0 hrev
  wp_start as ⟨#Hcl, #Hregs, #Hctx, #Hce, Hau0⟩
  wp_auto
  wp_apply (linkv.wp_NewProph_typed (τ := w64) github_com.goose_lang.primitive.wp_NewProph)
    as %pr %xs Hpr
  ispecialize Hau0 $$ %(xs.getD 0 (W64 0)) %(xs.getD 1 (W64 0))
  imod Hau0 with #Hau
  generalize hQ : Q0 (xs.getD 0 (W64 0)) (xs.getD 1 (W64 0)) = Q
  (try wp_auto)
  wp_apply wp_WithRev opts.Revision' as %f1 #Hf1
  wp_apply wp_WithLimit (W64 1) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  generalize hsl : slice.mk sl _ _ = optsSl
  have hfs : [f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2 = [f1, f2] := by
    show [f1, zero_val GoFunc].set 1 f2 = [f1, f2]; rfl
  ihave #Hopts : optsAt optsSl ([withRevM (W64 0), withLimitM (W64 1)] : List (OpFull → OpFull))
    $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | i
    · cases Hf; cases Hg; rw [← hrev]; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
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
        (⌜(rangeWireOf (opGetModel key [withRevM (W64 0), withLimitM (W64 1)])).base.serializable
            = false⌝ ∗ kvReadAu x.γr.kv Q)) :=
    fun _ _ _ => by
      iintro (%h | #h)
      · ileft; ipureintro; exact h
      · iright; iframe h; ipureintro; rfl
  ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  wp_auto
  wp_apply (client.client_range_any api ms (W64 0) ci cd key optsSl
      [withRevM (W64 0), withLimitM (W64 1)] iprop(True) Q) $$ []
    as %resp %err ⟨-, Hout⟩
  · iframe #
    isplitl []
    · rw [show (opGetModel key [withRevM (W64 0), withLimitM (W64 1)]).base.sortSet = false
        from rfl]
      iapply sortNamesIf_false
    ipureintro
    first
      | rfl
      | (refine ⟨?_, rfl⟩; unfold opGetPanics opFold OpFull.newOp; simp [withRevM, withLimitM])
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
  · subst Herr
    ihave Hs := client.rangeReply_state_bnd x.E x.γr (W64 0) x.cid x.mid _ [] Q m rfl rfl $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, hrevσ, hb⟩ := Hσ
    rw [rangeWireOf_getKey1] at hsel
    have hkvs := srvRangeOk_getKey1 key σ.kvs m.kvs m.more hsel
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl2, %ps, #Hh, #Hhf, #Hkvf2, #Hsl2, #Hkvs, #Hmore, #Hcount⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl2
    cases hk : mvcc.findKey key σ.kvs with
    | none =>
      rw [hk] at hkvs
      have hps : ps = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hlen, hkvs]; rfl
      subst hps
      wp_if_destruct
      · exfalso; simp at Hsll; word
      · wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64)
          $$ [$p $Hpr] as %xs1 ⟨%Hx1, p, Hpr⟩
        (try wp_auto)
        wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64)
          $$ [$p $Hpr] as %xs2 ⟨%Hx2, p, Hpr⟩
        (try wp_auto)
        subst Hx2; subst Hx1; subst hQ
        isimp only [List.getD_cons_zero, List.getD_cons_succ] at HQ
        have e1 : modAt key σ = W64 0 := by simp [modAt, hk]
        iapply HΦ
        ileft
        isplitl []
        · ipureintro; rfl
        iexists σ
        rw [e1, ← hrevσ]
        iframe HQ
        isplitl []
        · ipureintro; exact ⟨rfl, hb⟩
        rw [hk]
        simp only [kvOut]
        ipureintro; first | rfl | trivial
    | some v =>
      rw [hk] at hkvs
      obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
        have : 0 < ps.length := by rw [Hlen, hkvs]; simp
        exact ⟨ps[0], List.getElem?_eq_getElem this⟩
      have hv0 : m.kvs[0]? = some v := by rw [hkvs]; rfl
      ihave #Hkv := Hall $$ %0 %p0 %v %Hp0 %hv0
      wp_if_destruct
      · have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl2.len := by
          have := Hsll.1
          constructor <;> word
        simp only [Hbnd0, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl2] as -
        · iframe Hsl2; ipureintro; exact Hp0
        ihave %Hpn := kvIs_ne_null p0 v $$ Hkv
        ihave #Hkv' := Hkv
        iunfold txn.kvIs at Hkv'
        icases Hkv' with ⟨%ksl, %vsl, -, -, -, #Hmod, -, -, -, -⟩
        wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64)
          $$ [$p $Hpr] as %xs1 ⟨%Hx1, p, Hpr⟩
        (try wp_auto)
        wp_if_destruct
        · exact absurd rfl Hpn
        · wp_apply (linkv.wp_ptr_ResolveU64_typed github_com.goose_lang.primitive.ProphId.wp_ResolveU64)
            $$ [$p $Hpr] as %xs2 ⟨%Hx2, p, Hpr⟩
          (try wp_auto)
          subst Hx2; subst Hx1; subst hQ
          isimp only [List.getD_cons_zero, List.getD_cons_succ] at HQ
          have e1 : modAt key σ = v.modRev := by simp [modAt, hk]
          iapply HΦ
          ileft
          isplitl []
          · ipureintro; rfl
          iexists σ
          rw [e1, ← hrevσ]
          iframe HQ
          isplitl []
          · ipureintro; exact ⟨rfl, hb⟩
          rw [hk]
          iapply kvOut_some
          iexact Hkv
      · exfalso
        have h1 : ps.length = 1 := by rw [Hlen, hkvs]; rfl
        obtain ⟨h2, h3⟩ := Hsll
        rw [h1] at h2
        apply Hif
        word
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iright
    iunfold kvErr at Hke
    icases Hke with ⟨%Hce, #Hse, #Hcl⟩
    iframe Hse Hcl
    isplitl []
    · ipureintro; exact Herr
    ipureintro; exact Hce

end proof

end kubernetes
end EtcdGrove
end Perennial
