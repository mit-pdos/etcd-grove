/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__Keys.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Keys
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.Keys.wp_proof : lease.Lease.Keys.spec (GF := GF) (hG := hG) := by
  intro l I id
  wp_start as ⟨#Hlo, Hslot, Hio⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (sync.RWMutex.wp_RLock (lsF go!"mu" l) (leaseItems l)) $$ [$Hslot] as ⟨Hlk, HR⟩
  iunfold leaseItems at HR
  icases HR with ⟨%sm, %S, Hsm, HS⟩
  iunfold leaseItemsOwn at Hio
  icases Hio with ⟨%sm', %S0, Hsm', HS', %HSI⟩
  icombine Hsm Hsm' gives %Hsmeq
  subst Hsmeq
  ihave %HSeq := ownMap_agree sm _ _ S S0 $$ [$HS $HS']
  subst HSeq
  wp_auto
  wp_apply (wp_map_len_lt sm S _) $$ [$HS] as ⟨HS, %Hsz⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 (GMap.size S : Int)) ⟨by word, by word⟩)
    as %sl0 ⟨Hsl0, Hcap0, -⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun (keys : List LeaseItem) (i : Int) => iprop(∃ (x : LeaseItem)
      (sl : GoSlice),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "keys" ∷ keys_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* ((keys.take i.toNat).map LeaseItem.Key') ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1)))) $$ HS
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k keys Hsl0 Hcap0]
  · iexists _, sl0
    simp only [named]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %sl' ⟨Hsl, Hcap, -⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, sl'
    simp only [named]
    iframe
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.map_append, List.map_singleton]
    iframe
    ipureintro; omega
  iintro HP HS
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length]
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock (lsF go!"mu" l) (leaseItems l)) $$ [$Hlk Hsm HS] as Hslot
  · inext; iunfold leaseItems; iexists sm, S; iframe
  iapply HΦ
  iframe Hsl Hslot
  isplitl [Hsm' HS']
  · iunfold leaseItemsOwn; iexists sm, S; iframe; ipureintro; exact HSI
  ipureintro
  have hS : ∀ it : LeaseItem, (S.lookup it).isSome = true ↔ I.lookup it = some id := by
    intro it; rw [← HSI it]
    cases S.lookup it with
    | none => simp
    | some u => cases u; simp
  constructor
  · intro k
    rw [List.mem_map]
    constructor
    · rintro ⟨it, hit, rfl⟩
      have h := (hS it).1 ((Hkset it).1 hit)
      cases it; exact h
    · intro h
      exact ⟨LeaseItem.mk k, (Hkset _).2 ((hS _).2 h), rfl⟩
  · unfold List.Nodup at Hknodup ⊢
    rw [List.pairwise_map]
    refine Hknodup.imp (fun {a b} hab heq => hab ?_)
    cases a; cases b; simp only at heq; rw [heq]

end proof

end EtcdGrove
end Perennial
