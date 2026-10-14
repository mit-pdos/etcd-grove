/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/readSet__first.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__first
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMMaps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem readSet.first.wp_proof : readSet.first.spec (GF := GF) (hG := hG) := by
  intro m dq pfx rsMap reads
  wp_start as ⟨Hm, #Hrs⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (r : w64) (rp : Loc),
      "ret" ∷ ret_ptr ↦ r ∗ "resp" ∷ resp_ptr ↦ rp ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hr" ∷ ⌜FirstUpTo reads keys i.toNat r⌝)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ret resp]
  · iexists _, _
    simp only [named]
    iframe ret resp
    ipureintro
    exact ⟨Int.le_refl _, FirstUpTo_init reads keys⟩
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    ihave #Hrs' := Hrs
    unfold readsAt
    icases Hrs' with ⟨%Hdom, #Hall⟩
    obtain ⟨e, He⟩ : ∃ e, reads !! key = some e := by
      have h := Hdom key
      rw [Hp] at h
      exact Option.isSome_iff_exists.1 (by simpa using h.symm)
    ihave #Hr := Hall $$ %key %p %e %Hp %He
    unfold readRespAt
    icases Hr with ⟨%Hpnn, -, ⟨%h, #Hhdr, %Hhnn, #Hrev⟩, -⟩
    wp_auto
    have Hstep := FirstUpTo_step Hr Hkey He
    rw [show i.toNat + 1 = (i + 1).toNat by omega] at Hstep
    wp_if_destruct
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iframe ret resp
      ipureintro
      refine ⟨by omega, ?_⟩
      simpa [Hif] using Hstep
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      simp only [named]
      iframe ret resp
      ipureintro
      refine ⟨by omega, ?_⟩
      simpa [Hif] using Hstep
  iintro HP Hm
  iNamed HP
  unfold readsAt
  icases Hrs with ⟨%Hdom, -⟩
  wp_auto
  iapply HΦ
  iframe Hm
  ipureintro
  apply FirstUpTo_final (rsMap := rsMap) (keys := keys) _ Hdom Hkset
  rwa [show (((GMap.size rsMap : Nat) : Int)).toNat = keys.length by omega] at Hr

end proof

end concurrency
end EtcdGrove
end Perennial
