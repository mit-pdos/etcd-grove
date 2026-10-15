/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/writeSet__cmps.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__cmps
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
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

theorem writeSet.cmps.wp_proof (hMR : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG)) :
    writeSet.cmps.spec (GF := GF) (hG := hG) := by
  intro m dq pfx wsMap writes rev
  wp_start as ⟨Hm, #Hws⟩
  ihave #Hws' := Hws
  unfold writesAt
  icases Hws' with ⟨%Hdom, -⟩
  wp_auto
  wp_apply wp_map_len_lt (t := writeSet.ty) $$ Hm as ⟨Hm, %Hsz'⟩
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Cmp) (W64 0) (W64 (GMap.size wsMap))
    (by word) as %sl0 ⟨Hs0, Hcap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (sl : GoSlice)
      (cs : List go_etcd_io.etcd.client.v3.Cmp) (kx : GoString),
      "cmps" ∷ cmps_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* cs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Cmp sl (DFrac.own 1) ∗
      "key" ∷ key_ptr ↦ kx ∗ "rev" ∷ rev_ptr ↦ rev ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hlen" ∷ ⌜cs.length = ((keys.take i.toNat).map (writeCmp rev)).length⌝ ∗
      "#Hcs" ∷ □ (∀ (j : Nat) (c : go_etcd_io.etcd.client.v3.Cmp) (mm : CmpModel), ⌜cs[j]? = some c⌝ -∗
        ⌜((keys.take i.toNat).map (writeCmp rev))[j]? = some mm⌝ -∗
        cmpAt c mm))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [cmps Hs0 Hcap0 key rev]
  · iexists sl0, _, _
    simp only [named]
    iframe cmps Hs0 Hcap0 key rev
    simp only [List.replicate_zero, Int.toNat_zero,
      List.take_zero, List.map_nil]
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro; rfl
    iapply pointwise_nil
  isplitr
  · imodintro
    iintro %i %k %sp ⟨%Hkey, %Hsp⟩ HP
    iNamed HP
    wp_auto
    ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
    · iPkgInit
    wp_apply hMR k $$ [$Hcv] as %c0 #Hc0
    (try wp_auto)
    wp_apply hCmp c0 _ go!"<" .lt _ (.num rev) $$ [$Hcv $Hc0] as %c #Hc
    · ipureintro
      refine ⟨by simp [cmpOpOf], ?_⟩
      simp [cmpKeyM, cmpArgOf]
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
    have Hstep := map_take_succ (writeCmp rev) keys i.toNat k Hkey
    rw [show i.toNat + 1 = (i + 1).toNat by omega] at Hstep
    iexists sl', cs ++ [c], k
    simp only [named]
    iframe cmps Hsl Hcap key rev
    rw [Hstep]
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; simp [Hlen]
    iapply pointwise_snoc (fun c mm => cmpAt (GF := GF) c mm) _ _ c (writeCmp rev k) Hlen
    iframe Hcs
    iExactEq Hc
    rfl
  iintro HP Hm
  iNamed HP
  rw [show (((GMap.size wsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length] at Hlen
  rw [show (((GMap.size wsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length]
  ipersist Hsl
  wp_auto
  iapply HΦ
  iframe Hm
  iexists _
  isplitl
  · unfold cmpsAt
    iexists cs
    iframe Hsl Hcs
    ipureintro; exact Hlen
  ipureintro
  refine ⟨keys, ⟨Hknodup, fun k => by rw [Hkset, Hdom]⟩, rfl⟩

end proof

end concurrency
end EtcdGrove
end Perennial
