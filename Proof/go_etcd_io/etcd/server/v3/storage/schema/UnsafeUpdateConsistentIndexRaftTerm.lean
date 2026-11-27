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
    have h0 : idx = W64 0 := by word
    iapply HΦ
    simp only [rtAfterSave, h0, true_or, ↓reduceIte]
    iexact HTM
  have hi : idx ≠ W64 0 := by intro h; subst h; simp at Hif
  wp_auto
  wp_if_destruct
  · -- `raftTerm == 0`: nothing is written
    have h0 : rft = W64 0 := by word
    iapply HΦ
    simp only [rtAfterSave, h0, or_true, ↓reduceIte]
    iexact HTM
  have ht : rft ≠ W64 0 := by intro h; subst h; simp at Hif
  wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs ⟨Hbs, Hcap⟩
  · ipureintro; decide
  ihave %Hlen := ownSlice_len $$ Hbs
  ihave %Hcw := ownSliceCap_wf $$ Hcap
  have hl : sint.Z bs.len = 16 := by simp at Hlen; omega
  have hc : 16 ≤ sint.Z bs.cap := by omega
  icases (ownSlice_split_all (V := w8) (W64 8) bs _ _ ⟨by decide, by omega⟩).1 $$ Hbs with ⟨H1, H2⟩
  wp_auto
  wp_apply wp_bePutUint64 hP _ _ idx (by simp) $$ [$H1] as H1
  wp_auto
  wp_apply wp_bePutUint64 hP _ _ rft (by simp; omega) $$ [$H2] as H2
  ihave Hbs := (ownSlice_split_all (V := w8) (W64 8) bs _ (u64Be idx ++ u64Be rft)
    ⟨by decide, by omega⟩).2 $$ [H1 H2]
  · simp [u64Be_length]
    iframe H1 H2
  wp_auto
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
