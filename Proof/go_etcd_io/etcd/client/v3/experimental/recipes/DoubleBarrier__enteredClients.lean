/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__enteredClients.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.DoubleBarrier__enteredClients
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithSort
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem DoubleBarrier.enteredClients.wp_proof
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithSort : WithSort.spec (GF := GF) (hG := hG)) :
    DoubleBarrier.enteredClients.spec (GF := GF) (hG := hG) := by
  intro b s γ client id key count lo
  wp_start as ⟨#Hb, #Hlo⟩
  ihave #Hb' := Hb
  iunfold isDoubleBarrier at Hb'
  icases Hb' with ⟨#Hbs, #Hbctx, #Hbkey, #Hbcount, %Hcount, #Hsess, #Hcl, #Hclosed⟩
  ihave ⟨%kv, #HKVf, #Hkvc⟩ := isEtcdRecipesClient_kv client (key ++ go!"/") $$ Hcl
  wp_auto
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithSort (W64 2) (W64 1) as %f2 #Hf2
  · ipureintro; decide
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  generalize hsl : slice.mk sl _ _ = optsSl
  ihave #Hopts : optsAt optsSl [withPrefixM, withSortM (W64 2) (W64 1)] $$ []
  · iunfold optsAt
    iexists _
    iframe Hsl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases i with _ | _ | i
    · cases Hf'; cases Hg; iexact Hf1
    · cases Hf'; cases Hg; iexact Hf2
    · simp at Hf'
  ihave #Hopts' := optsAt_res optsSl _ iprop(True) $$ Hopts
  iunfold isRecipesKV at Hkvc
  icases Hkvc with ⟨#HKV, -, -, -⟩
  iunfold isEtcdKVTodo at HKV
  have hwp : key ++ go!"/waiters" ≠ [] := by simp
  have hpw : key ++ go!"/" <+: key ++ go!"/waiters" := by
    rw [show go!"/waiters" = go!"/" ++ go!"waiters" from rfl, ← List.append_assoc]
    exact List.prefix_append _ _
  have hne : key ++ go!"/waiters" ≠ key ++ go!"/" := by simp
  ihave #HG := HKV $$ %(key ++ go!"/waiters") %optsSl %([withPrefixM, withSortM (W64 2) (W64 1)] : List (OpFull → OpFull))
    %iprop(True) %lo
  wp_auto
  wp_apply HG $$ [] as %gresp %gerr ⟨-, #Hgres, -⟩
  · iframe Hopts' Hlo
    ipureintro
    exact ⟨waitersOp_not_panics.1, (waitersOp_t _).1⟩
  have Hop : opGetModel (key ++ go!"/waiters") [withPrefixM, withSortM (W64 2) (W64 1)] =
      waitersOp (key ++ go!"/waiters") := rfl
  rw [Hop]
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright; ipureintro; exact Hgne
  subst Hgnil
  obtain ⟨Hrev0, Hser, HnP, -⟩ :=
    waitersOp_rev (key ++ go!"/") (key ++ go!"/waiters") hne hwp (by simp)
  have HRle' : sint.Z lo ≤ sint.Z R := HRle.1 Hser
  rw [ite_eq_right (c := (waitersOp (key ++ go!"/waiters")).isPrefixGet (key ++ go!"/") = true)
    (by rw [HnP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (waitersOp (key ++ go!"/waiters")).base.rev = W64 0 ∧
      KeyRangeUnder (key ++ go!"/") (waitersOp (key ++ go!"/waiters")).key
        (waitersOp (key ++ go!"/waiters")).base.rangeEnd from
    ⟨Hrev0, (waitersOp_under _ _ hwp hpw).1⟩)]
  icases Hgr with ⟨%s', %gsl', %gps, %gkvs, #Hs', %Hwf', #Hgsl', #Hgps, #Hgkvs, %Hgok⟩
  obtain ⟨Hperm, Hsorted⟩ := waitersOp_kvs _ s' gkvs hwp Hgok
  wp_auto
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  iexists R, gkvs
  iframe HRR
  isplitr
  · unfold waitersResp
    iexists s', gsl', gps
    iframe Hs' Hgsl' Hgps Hgkvs
    ipureintro; exact ⟨Hwf', Hperm, Hsorted⟩
  ipureintro; exact HRle'

end proof

end recipes
end EtcdGrove
end Perennial
