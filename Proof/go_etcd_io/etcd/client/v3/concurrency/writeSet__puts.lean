/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/writeSet__puts.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__puts
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem writeSet.puts.wp_proof : writeSet.puts.spec (GF := GF) (hG := hG) := by
  intro m dq pfx wsMap writes
  wp_start as ⟨Hm, #Hws⟩
  ihave #Hws' := Hws
  unfold writesAt
  icases Hws' with ⟨%Hdom, #Hall⟩
  wp_auto
  wp_apply wp_map_len_lt (t := writeSet.ty) $$ Hm as ⟨Hm, %Hsz'⟩
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Op) (W64 0) (W64 (GMap.size wsMap))
    (by word) as %sl0 ⟨Hs0, Hcap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (sl : GoSlice)
      (vs : List go_etcd_io.etcd.client.v3.Op) (os : List OpFull) (sv : stmPut),
      "puts" ∷ puts_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* vs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Op sl (DFrac.own 1) ∗
      "v" ∷ v_ptr ↦ sv ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hlen" ∷ ⌜vs.length = os.length ∧ os.map txnOpOf =
        ((keys.take i.toNat).filterMap (fun k => (writes !! k).map (WriteM.op k))).map some⌝ ∗
      "#Hvs" ∷ □ (∀ (j : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs[j]? = some v⌝ -∗
        ⌜os[j]? = some o⌝ -∗ opFullAt v o))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [puts Hs0 Hcap0 v]
  · iexists sl0, _, [], _
    simp only [named]
    iframe puts Hs0 Hcap0 v
    simp only [List.replicate_zero, Int.toNat_zero, List.take_zero, List.filterMap_nil]
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iapply pointwise_nil
  isplitr
  · imodintro
    iintro %i %k %sp ⟨%Hkey, %Hsp⟩ HP
    iNamed HP
    obtain ⟨w, Hw⟩ : ∃ w, writes !! k = some w := by
      have h := Hdom k
      rw [Hsp] at h
      exact Option.isSome_iff_exists.1 (by simpa using h.symm)
    ihave #Hwa := Hall $$ %k %sp %w %Hsp %Hw
    unfold writeAt
    icases Hwa with ⟨-, %o, #Ho, %Hto⟩
    wp_auto
    wp_apply wp_slice_literal (V := go_etcd_io.etcd.client.v3.Op) [sp.op']
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
    have Hstep := filterMap_take_succ (fun k => (writes !! k).map (WriteM.op k)) keys i.toNat k
      (WriteM.op k w) Hkey (by simp [Hw])
    rw [show i.toNat + 1 = (i + 1).toNat by omega] at Hstep
    iexists sl', vs ++ [sp.op'], os ++ [o], sp
    simp only [named]
    iframe puts Hsl Hcap v
    rw [Hstep]
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro
      refine ⟨by simp [Hlen.1], ?_⟩
      simp [List.map_append, Hlen.2, Hto]
    iapply pointwise_snoc (fun v o => opFullAt (GF := GF) v o) _ _ sp.op' o Hlen.1
    iframe Hvs Ho
  iintro HP Hm
  iNamed HP
  rw [show (((GMap.size wsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length] at Hlen
  ipersist Hsl
  wp_auto
  iapply HΦ
  iframe Hm
  iexists os, _
  isplitl
  · unfold opsAt
    iexists vs
    iframe Hsl Hvs
    ipureintro; exact Hlen.1
  ipureintro
  exact ⟨Hlen.2, keys, ⟨Hknodup, fun k => by rw [Hkset, Hdom]⟩, rfl⟩

end proof

end concurrency
end EtcdGrove
end Perennial
