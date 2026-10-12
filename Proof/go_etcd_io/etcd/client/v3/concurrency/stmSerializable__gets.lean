/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stmSerializable__gets.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__gets
public import Spec.go_etcd_io.etcd.client.v3.OpGet
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

theorem stmSerializable.gets.wp_proof (hGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG)) :
    stmSerializable.gets.spec (GF := GF) (hG := hG) := by
  intro p pfx reads
  wp_start as ⟨Hrs⟩
  unfold stmRsetOwn
  icases Hrs with ⟨%m, %rsMap, Hf, Hm, #Hat⟩
  ihave #Hat' := Hat
  unfold readsAt
  icases Hat' with ⟨%Hdom, -⟩
  wp_auto
  wp_apply wp_map_len_lt (t := readSet.ty) $$ Hm as ⟨Hm, %Hsz'⟩
  wp_apply wp_slice_make3 (V := GoString) (W64 0) (W64 (GMap.size rsMap))
    (by word) as %ksl0 ⟨Hk0, Hkcap0, -⟩
  (try wp_auto)
  wp_apply wp_map_len_lt (t := readSet.ty) $$ Hm as ⟨Hm, %Hsz''⟩
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Op) (W64 0) (W64 (GMap.size rsMap))
    (by word) as %osl0 ⟨Ho0, Hocap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (ksl osl : GoSlice)
      (vs : List go_etcd_io.etcd.client.v3.Op) (kx : GoString),
      "keys" ∷ keys_ptr ↦ ksl ∗ "Hksl" ∷ ksl ↦* keys.take i.toNat ∗
      "Hkcap" ∷ ownSliceCap GoString ksl (DFrac.own 1) ∗
      "ops" ∷ ops_ptr ↦ osl ∗ "Hosl" ∷ osl ↦* vs ∗
      "Hocap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Op osl (DFrac.own 1) ∗
      "k" ∷ k_ptr ↦ kx ∗ "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hlen" ∷ ⌜vs.length = ((keys.take i.toNat).map keyOp).length⌝ ∗
      "#Hvs" ∷ □ (∀ (j : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs[j]? = some v⌝ -∗
        ⌜((keys.take i.toNat).map keyOp)[j]? = some o⌝ -∗ opFullAt v o))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [keys Hk0 Hkcap0 ops Ho0 Hocap0 k]
  · iexists ksl0, osl0, _, _
    simp only [named]
    iframe keys Hkcap0 ops Ho0 Hocap0 k
    simp only [Int.toNat_zero, List.take_zero, List.map_nil, List.replicate_zero]
    isplitl
    · iExactEq Hk0; rfl
    isplitr
    · ipureintro; exact Int.le_refl _
    isplitr
    · ipureintro; rfl
    iapply pointwise_nil
  isplitr
  · imodintro
    iintro %i %key %rp ⟨%Hkey, %Hrp⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := GoString) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [Hksl Hkcap Hsl2] as %ksl' ⟨Hksl, Hkcap, -⟩
    · iframe
    (try wp_auto)
    ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
    · iPkgInit
    ihave #Hnil := optsAt_nil (GF := GF)
    wp_apply hGet key slice.nil [] $$ [$Hcv $Hnil] as %op #Hop
    · ipureintro; exact keyOp_not_panics
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_etcd_io.etcd.client.v3.Op) [op]
    isplitr
    · ipureintro; rfl
    iintro %sl3 ⟨Hsl3, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [Hosl Hocap Hsl3] as %osl' ⟨Hosl, Hocap, -⟩
    · iframe
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    have Hk1 : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    iexists ksl', osl', vs ++ [op], key
    simp only [named]
    rw [Hk1]
    iframe keys Hksl Hkcap ops Hosl Hocap k
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; simp [Hlen]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iapply pointwise_snoc (fun v o => opFullAt (GF := GF) v o) _ _ op (keyOp key) Hlen
    iframe Hvs
    unfold keyOp
    iexact Hop
  iintro HP Hm
  iNamed HP
  rw [show (((GMap.size rsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length] at Hlen
  rw [show (((GMap.size rsMap : Nat) : Int)).toNat = keys.length by omega, List.take_length]
  ipersist Hksl
  ipersist Hosl
  wp_auto
  iapply HΦ
  isplitl [Hf Hm]
  · iexists m, rsMap
    iframe Hf Hm Hat
  iexists keys
  iframe Hksl
  isplitl
  · unfold opsAt
    iexists vs
    iframe Hosl Hvs
    ipureintro; simpa using Hlen
  ipureintro
  exact ⟨Hknodup, fun k => by rw [Hkset, Hdom]⟩

end proof

end concurrency
end EtcdGrove
end Perennial
