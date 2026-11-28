/-
Proof of `Spec/.../schema/UnsafeUpdateConsistentIndexRaftTerm.lean` (keepfix (c)). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeUpdateConsistentIndexRaftTerm
public import Spec.encoding.binary.bigEndian__PutUint64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.UnsafeUpdateConsistentIndexRaftTerm.wp_proof
    (hP : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG)) :
    schema.UnsafeUpdateConsistentIndexRaftTerm.spec (GF := GF) (hG := hG) := by
  intro tx TMx PTr m r idx rft
  wp_start as ⟨#Hw, HTM, HPr⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%mb, #Hmb, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%rk, #Hrk, #Hrkb⟩⟩
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  unfold metaRtWriter
  wp_auto
  wp_if_destruct
  · -- `index == 0`: nothing is written
    iapply HΦ
    simp only [rtAfterSave, _root_.true_or, ↓reduceIte]
    iexact HTM
  have hi : idx ≠ W64 0 := by intro h; subst h; simp at Hif
  (try wp_auto)
  wp_if_destruct
  · -- `raftTerm == 0`: nothing is written
    iapply HΦ
    simp only [rtAfterSave, _root_.or_true, ↓reduceIte]
    iexact HTM
  have ht : rft ≠ W64 0 := by intro h; subst h; simp at Hif
  wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs ⟨Hbs, Hcap⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len $$ Hbs
  ihave %Hcw := ownSliceCap_wf $$ Hcap
  have hl : sint.Z bs.len = 16 := by
    obtain ⟨h1, h2⟩ := Hlen
    simp only [List.length_replicate] at h1
    word
  have hc : 16 ≤ sint.Z bs.cap := by omega
  have h8 : sint.Z (W64 8) = 8 := by decide
  have hn8 : sint.nat (W64 8) = 8 := by decide
  icases (ownSlice_split_all (V := w8) (W64 8) bs _ _ ⟨by decide, by rw [hl]; decide⟩).1 $$ Hbs with ⟨H1, H2⟩
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z bs.cap from
    ⟨by decide, by decide, by omega⟩)]
  wp_auto
  have hl1 : (List.take (sint.nat (W64 8)) (List.replicate 16 (zero_val w8))).length = 8 := by
    rw [hn8]; simp
  wp_apply wp_bePutUint64 hP _ _ idx hl1 $$ [$H1] as H1
  (try wp_auto)
  rw [if_pos (show 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z bs.len ∧ sint.Z bs.len ≤ sint.Z bs.cap from
    ⟨by decide, by omega, by omega⟩)]
  wp_auto
  have hl2 : (List.drop (sint.nat (W64 8)) (List.replicate 16 (zero_val w8))).length = 8 := by
    rw [hn8]; simp
  wp_apply wp_bePutUint64 hP _ _ rft hl2 $$ [$H2] as H2
  ihave Hbs := (ownSlice_split_all (V := w8) (W64 8) bs (DFrac.own 1) (u64Be idx ++ u64Be rft)
    ⟨by decide, by omega⟩).2 $$ [H1 H2]
  · rw [hn8, List.take_left' (u64Be_length idx), List.drop_left' (u64Be_length idx)]
    iframe H1 H2
  (try wp_auto)
  ihave #Hput := Hw $$ %mb %rk %bs %m %r %idx %rft
  wp_bind (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #mb)) (Val #rk)) (Val #bs))
  iapply Hput $$ [Hbs HTM HPr]
  · iframe Hmb Hrkb Hbs HTM HPr
    ipureintro; exact ⟨hi, ht⟩
  inext
  iintro HTM
  (try wp_auto)
  iapply HΦ
  simp only [rtAfterSave, hi, ht, or_self, ↓reduceIte]
  iexact HTM

end proof

end EtcdGrove
end Perennial
