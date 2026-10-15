/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__revokeRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revokeRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revokeLeaseKvs
public import Spec.go_etcd_io.etcd.client.v3.WithRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.revokeRange.wp_proof
    (hWR : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (hRLK : leasingKV.revokeLeaseKvs.spec (GF := GF) (hG := hG)) :
    leasingKV.revokeRange.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs b e
  wp_start as ⟨#Hlkv, Hrd, #Hsr, #Hctx, #Hcc⟩
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hcl, #Hkv, #Hp, -, -, -, #HKV, -⟩
  wp_auto
  wp_join iprop(∃ L : GoString, lend_ptr ↦ L ∗ lkv_ptr ↦ lkv ∗ ⌜L ≠ [W8 0]⌝) at (if: _ then _ else _)
    with [lend «end» lkv] as ⟨%L, lend, lkv, %HL⟩
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_if_destruct
    · (try wp_auto)
      wp_join_done
      iexists _; iframe
      ipureintro
      intro h
      have hl := congrArg List.length h
      have h1 : pfx.length ≠ 0 := by simpa using Hpfx
      cases e with
      | nil => simp_all
      | cons x e' => simp at hl; omega
    · (try wp_auto)
      wp_join_done
      iexists _; iframe
      ipureintro; simp
  wp_apply hWR L as %f #Hf
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts : optsAt (GF := GF) _ [withRangeM L] $$ []
  · unfold optsAt
    iexists [f]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg; subst Hf' Hg; iexact Hf
    · simp at Hf'
  (try wp_auto)
  iunfold isEtcdKV at HKV
  ihave #H0 := etcdReached_zero (GF := GF)
  ihave #HG := HKV $$ %ctx %cs %(pfx ++ b) %_ %([withRangeM L] : List (OpFull → OpFull)) %(W64 0)
  wp_apply HG $$ [] as %gresp %gerr #Hgres
  · iframe Hctx Hopts H0
    ipureintro
    simp [opGetPanics, opGetModel, opFold, withRangeM, OpFull.getInit, OpFull.newOp]
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, -, -, -, -, Hgr⟩)
  · obtain ⟨g, rfl⟩ : ∃ g, gerr = GoInterface.ok g := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok g => exact ⟨g, rfl⟩
    wp_auto
    iapply HΦ $$ Hrd
  subst Hgnil
  have HoP : (opGetModel (pfx ++ b) [withRangeM L]).isPrefixGet [] = false := by
    simp [OpFull.isPrefixGet, opGetModel, opFold, withRangeM, OpFull.getInit, OpFull.newOp]
    intros; exact HL
  rw [ite_eq_right (c := (opGetModel (pfx ++ b) [withRangeM L]).isPrefixGet [] = true)
    (by rw [HoP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (opGetModel (pfx ++ b) [withRangeM L]).base.rev = W64 0 ∧
      KeyRangeUnder [] (opGetModel (pfx ++ b) [withRangeM L]).key
        (opGetModel (pfx ++ b) [withRangeM L]).base.rangeEnd from
    ⟨by simp [opGetModel, opFold, withRangeM, OpFull.getInit, OpFull.newOp, OpModel.zero],
     fun _ _ => List.nil_prefix⟩)]
  icases Hgr with ⟨%s', %gsl, %gps, %gkvs, -, -, #Hgsl, #Hgps, #Hgkvs, -⟩
  wp_auto
  wp_apply hRLK lkv γ pfx ctx cs gsl gps gkvs $$ [$Hpkg $Hlkv $Hrd $Hsr $Hctx $Hcc $Hgps $Hgkvs]
    as %m %err ⟨Hrd, -⟩
  iapply HΦ $$ Hrd

end proof

end leasing
end EtcdGrove
end Perennial
