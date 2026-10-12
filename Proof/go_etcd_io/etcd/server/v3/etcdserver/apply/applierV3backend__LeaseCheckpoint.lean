/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseCheckpoint
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.LeaseCheckpoint.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.LeaseCheckpoint.spec (GF := GF) (hG := hG) := by
  intro E p r log Pre Q Post
  wp_start as ⟨#Hb, ⟨%cms, #Hr, %Hlen1⟩, Hpre⟩
  iunfold apply.mPre at Hpre
  iunfold apply.kvOwn at Hpre
  icases Hpre with ⟨⟨Hrd, Hsw, #Hknown⟩, Hres, Hcs⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlg, -, -, #Hle, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨-, %li, %Hli, -, -, #HCk, -⟩
  iunfold apply.leaseCheckpointIs at Hr
  icases Hr with ⟨%Hrn, %sl, %ps, #Hcps, #Hsl, %Hlen, #Hall⟩
  iStructNamed Hopts
  wp_auto
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (n : w64) (c0 : Loc),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ c0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ps.length : Int)⌝ ∗
      "Hst" ∷ ((⌜n = W64 0⌝ ∗ mvcc.csContract E.P E.f Pre Q Post) ∨
        (⌜n ≠ W64 0⌝ ∗ (Post ∨ Pre)))) $$ [i c Hcs]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  have Hslz : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hsll.2
  wp_if_destruct
  · -- the (only) checkpoint
    have h0 : sint.Z n = 0 := by
      have := Hsll.1; have := Hn.1; omega
    have Hn0 : n = W64 0 := by word
    subst Hn0
    icases Hst with (⟨-, Hcs⟩ | ⟨%Hne, -⟩)
    rotate_left
    · exact absurd rfl Hne
    have Hlt : 0 < ps.length := by have := Hsll.1; omega
    obtain ⟨pc, ps', rfl⟩ : ∃ pc ps', ps = pc :: ps' := by
      cases ps with
      | nil => simp at Hlt
      | cons a l => exact ⟨a, l, rfl⟩
    obtain ⟨cm, cms', rfl⟩ : ∃ cm cms', cms = cm :: cms' := by
      cases cms with
      | nil => simp at Hlen
      | cons a l => exact ⟨a, l, rfl⟩
    ihave #Hc := (BigSepL.bigSepL_mem
      (Φ := fun x : Loc × CheckpointModel => apply.checkpointIs (GF := GF) x.1 x.2)
      (x := (pc, cm)) (by simp)) $$ Hall
    icases ownSlice_elem_acc 0 pc sl DFrac.discard (pc :: ps') (Int.le_refl 0) rfl $$ Hsl
      with ⟨#Hpe, -⟩
    have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := ⟨by omega, Hif⟩
    rw [ite_eq_left Hbnd]
    rw [h0]
    ihave #Hc' : apply.checkpointIs (GF := GF) pc cm $$ Hc
    iunfold apply.checkpointIs at Hc'
    icases Hc' with ⟨%Hpcn, #HcID, #HcTTL⟩
    wp_auto
    rw [Hli]
    wp_auto
    wp_apply HCk $$ [$Hcs] as %err HPP
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists W64 0 + W64 1, pc
      simp only [named]
      iframe
      isplitr
      · ipureintro; simp only [List.length_cons]; constructor <;> word
      iright
      iframe
      ipureintro; decide
    | ok ei =>
      wp_auto
      wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
      · iexact Hb
      wp_alloc resp as Hresp
      wp_auto
      wp_for_post
      iapply HΦ
      iunfold apply.mPost
      iunfold apply.kvOwn
      iframe
      iframe #
  · -- the loop is done
    ihave HPP : iprop(Post ∨ Pre) $$ [Hst]
    · icases Hst with (⟨-, Hcs⟩ | ⟨-, HPP⟩)
      · iright; iapply apply.csContract_pre $$ Hcs
      · iexact HPP
    wp_apply hHdr $$ [$Hrd $Hsw] as %h ⟨Hrd, Hsw, %Hh⟩
    · iexact Hb
    wp_alloc resp as Hresp
    wp_auto
    iapply HΦ
    iunfold apply.mPost
    iunfold apply.kvOwn
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
