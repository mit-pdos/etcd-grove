/-
Lean-first (no Rocq counterpart).

The proof of `kubernetes.Client.Count`: the options `[WithPrefix(), WithCountOnly()]`, then
`client_range_any` through the client's `*kv`, and the response's `Count` from `srvCount_countPrefix`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Count
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithCountOnly

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

theorem Client.Count.wp_proof (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithCountOnly : WithCountOnly.spec (GF := GF) (hG := hG)) :
    Client.Count.spec (GF := GF) (hG := hG) := by
  intro _ _ kc ms V ci cd pfx _ Q
  wp_start as ⟨#Hcl, #Hregs, #Hctx, #Hce, #Hau⟩
  wp_auto
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithCountOnly as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  wp_auto
  generalize hsl : slice.mk sl _ _ = optsSl
  have hfs : [f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2 = [f1, f2] := by
    show [f1, zero_val GoFunc].set 1 f2 = [f1, f2]; rfl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withCountOnlyM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · simp at Hf
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  ihave #Hopts' := optsAt_res optsSl _ iprop(True) $$ Hopts
  ihave #Hrr := client.kvRegs_range ms $$ Hregs
  ihave #Hst' := client.srvStart_both ms $$ Hst
  have hser : (rangeWireOf (opGetModel pfx [withPrefixM, withCountOnlyM])).base.serializable = false := by
    rw [rangeWireOf_countPrefix]; rfl
  have hm : ∀ (k : Nat) (x : client.SrvAt GF), ms[k]? = some x →
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) ⊢
      iprop(⌜Q = fun _ => iprop(True)⌝ ∨
        (⌜(rangeWireOf (opGetModel pfx [withPrefixM, withCountOnlyM])).base.serializable = false⌝ ∗
          kvReadAu x.γr.kv Q)) :=
    fun _ _ _ => by
      iintro (%h | #h)
      · ileft; ipureintro; exact h
      · iright; iframe h; ipureintro; exact hser
  ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  wp_auto
  have hss : (opGetModel pfx [withPrefixM, withCountOnlyM]).base.sortSet = false := by
    by_cases hp : pfx = [] <;> (unfold opGetModel opFold OpFull.getInit OpFull.newOp OpModel.zero withPrefixM withCountOnlyM; simp [hp])
  have ht : (opGetModel pfx [withPrefixM, withCountOnlyM]).t = W64 1 := by
    by_cases hp : pfx = [] <;> (unfold opGetModel opFold OpFull.getInit OpFull.newOp OpModel.zero withPrefixM withCountOnlyM; simp [hp])
  wp_apply (client.client_range_any api ms (W64 0) ci cd pfx optsSl
      [withPrefixM, withCountOnlyM] iprop(True) Q []) $$ []
    as %resp %err ⟨-, Hout⟩
  · iframe #
    isplitl []
    · rw [hss]
      iapply sortNamesIf_false
    ipureintro
    refine ⟨?_, ht⟩
    unfold opGetPanics opFold OpFull.newOp withPrefixM withCountOnlyM
    simp
  icases Hout with (⟨%Herr, %m, #Hm, %x, %hx, #Hq⟩ | ⟨⟨%Herr, %Hrn⟩, #Hke⟩)
  · subst Herr
    have hrev0 : (rangeWireOf (opGetModel pfx [withPrefixM, withCountOnlyM])).base.rev = W64 0 := by
      rw [rangeWireOf_countPrefix]; rfl
    ihave Hs := rangeReply_state_count_bnd x.E x.γr (W64 0) x.cid x.mid _ [] Q m hser hrev0 $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨-, hcnt, -, hb⟩ := Hσ
    rw [rangeWireOf_countPrefix, srvCount_countPrefix] at hcnt
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl2, %ps, #Hh, #Hhf, #Hkvf2, #Hsl2, #Hkvs, #Hmore, #Hcount⟩
    wp_auto
    iapply HΦ
    ileft
    isplitl []
    · ipureintro; rfl
    iexists σ
    iframe HQ
    ipureintro
    exact ⟨hcnt, hb⟩
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
    · ipureintro; exact ⟨Herr, rfl⟩
    ipureintro; exact Hce

end proof

end kubernetes
end EtcdGrove
end Perennial
