/-
Lean-first (no Rocq counterpart).

The proof of `callGet`: `client.client_Get_st`, then the output from the reply's header revision and
first key-value (`getOut`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrOf
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem callGet.wp_proof (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_vrOf : vrOf.spec (GF := GF) (hG := hG)) :
    callGet.spec (GF := GF) (hG := hG) := by
  intro _ CRE CEC cl ms V hAs key Q hkl
  wp_start as ⟨#Hcl, #Hregs, #Hau⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  ihave #Hnil := optsAt_nil (GF := GF)
  (try wp_auto)
  ihave #Hrr := client.kvRegs_range ms $$ Hregs
  wp_apply (client.client_Get_st cl ms V cctx ccd key slice.nil Q
      (opSizeOk_opGetModel (K := inMax) (E := 0) (V := 0) (optsKeep_nil _ _ _) hkl (by decide))) $$ []
    as %resp %err Hout
  · iframe #
  -- `cancel()`
  (try wp_auto)
  wp_apply Hccancel
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hσ⟩ | ⟨%Herr, -⟩)
  · subst Herr
    obtain ⟨hkvs, hrev, hb⟩ := Hσ
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
      icases Hkv with ⟨%kSl, %vSl, -, -, -, #HmF, #HvF, #HvalF, #HvS, -⟩
      have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
        have := Hsll.1
        constructor <;> word
      simp only [Hbnd0, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact Hp0
      (try wp_auto)
      wp_apply wp_vrOf vSl kv0.value DFrac.discard kv0.modRev kv0.version $$ [HvS] as -
      · iframe #
      (try wp_auto)
      iapply HΦ
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [← hkvs, hrev]
      cases hk : m.kvs with
      | nil => simp [hk] at Hkv0
      | cons a l =>
        simp only [hk, List.getElem?_cons_zero, Option.some.injEq] at Hkv0
        subst Hkv0
        rfl
    · iapply HΦ
      iright
      iexists σ
      iframe HQ
      ipureintro
      refine ⟨?_, hb⟩
      rw [← hkvs, hrev]
      have : m.kvs = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [← Hlen]; have := Hsll.1; word
      rw [this]
      rfl
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    ileft
    ipureintro; rfl

end proof

end linkvtxn
end EtcdGrove
end Perennial
