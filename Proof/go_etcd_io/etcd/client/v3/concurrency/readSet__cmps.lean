/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/readSet__cmps.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__cmps
public import Spec.go_etcd_io.etcd.client.v3.concurrency.isKeyCurrent
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem readSet.cmps.wp_proof (hIKC : isKeyCurrent.spec (GF := GF) (hG := hG)) :
    readSet.cmps.spec (GF := GF) (hG := hG) := by
  intro m dq pfx rsMap reads
  wp_start as ⟨Hm, #Hrs⟩
  ihave #Hrs' := Hrs
  unfold readsAt
  icases Hrs' with ⟨%Hdom, #Hall⟩
  wp_auto
  wp_apply wp_map_len_lt (t := readSet.ty) $$ Hm as ⟨Hm, %Hsz'⟩
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Cmp) (W64 0) (W64 (GMap.size rsMap))
    (by word) as %sl0 ⟨Hs0, Hcap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (sl : GoSlice)
      (cs : List go_etcd_io.etcd.client.v3.Cmp) (kx : GoString) (rk : Loc),
      "cmps" ∷ cmps_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* cs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Cmp sl (DFrac.own 1) ∗
      "k" ∷ k_ptr ↦ kx ∗ "rk" ∷ rk_ptr ↦ rk ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hlen" ∷ ⌜cs.length = ((keys.take i.toNat).filterMap
        (fun k => (reads !! k).map (readCmp k))).length⌝ ∗
      "#Hcs" ∷ □ (∀ (j : Nat) (c : go_etcd_io.etcd.client.v3.Cmp) (mm : CmpModel), ⌜cs[j]? = some c⌝ -∗
        ⌜((keys.take i.toNat).filterMap (fun k => (reads !! k).map (readCmp k)))[j]? = some mm⌝ -∗
        cmpAt c mm))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [cmps Hs0 Hcap0 k rk]
  · iexists sl0, _, _, _
    simp only [named]
    iframe cmps Hs0 Hcap0 k rk
    simp only [List.replicate_zero, Int.toNat_zero,
      List.take_zero, List.filterMap_nil]
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro; rfl
    iapply pointwise_nil
  isplitr
  · imodintro
    iintro %i %key %p ⟨%Hkey, %Hp⟩ HP
    iNamed HP
    obtain ⟨e, He⟩ : ∃ e, reads !! key = some e := by
      have h := Hdom key
      rw [Hp] at h
      exact Option.isSome_iff_exists.1 (by simpa using h.symm)
    ihave #Hr := Hall $$ %key %p %e %Hp %He
    wp_auto
    wp_apply hIKC pfx key p e $$ [$Hpkg $Hr] as %c #Hc
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_etcd_io.etcd.client.v3.Cmp) [c]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
    · iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have Hstep := filterMap_take_succ (fun k => (reads !! k).map (readCmp k)) keys i.toNat key
      (readCmp key e) Hkey (by simp [He])
    rw [show i.toNat + 1 = (i + 1).toNat by omega] at Hstep
    iexists sl', cs ++ [c], key, p
    simp only [named]
    iframe cmps Hsl Hcap k rk
    rw [Hstep]
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; simp [Hlen]
    iapply pointwise_snoc (fun c mm => cmpAt (GF := GF) c mm) _ _ c (readCmp key e) Hlen
    iframe Hcs Hc
  iintro HP Hm
  iNamed HP
  rw [show (((GMap.size rsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length] at Hlen
  rw [show (((GMap.size rsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length]
  ipersist Hsl
  wp_auto
  iapply HΦ
  iframe Hm
  iexists _
  isplitl [Hsl]
  · unfold cmpsAt
    iexists cs
    iframe Hsl Hcs
    ipureintro; exact Hlen
  iframe Hcap
  ipureintro
  refine ⟨keys, ⟨Hknodup, fun k => by rw [Hkset, Hdom]⟩, rfl⟩

end proof

end concurrency
end EtcdGrove
end Perennial
