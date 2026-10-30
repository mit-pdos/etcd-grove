module
public import Spec.go_etcd_io.bbolt.Tx__init
public import Proof.go_etcd_io.bbolt.StructSplit
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Copy
public import Spec.go_etcd_io.bbolt.internal.common.Meta__RootBucket
public import Spec.go_etcd_io.bbolt.internal.common.Meta__IncTxid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

-- `hash.Hash64`'s type, which `Meta.Validate`'s spec takes: bbolt reaches `hash` only through
-- `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The field `writable` of a transaction (and back). -/
theorem Tx_writable_acc (l : Loc) (dq : DFrac) (t : Tx) :
    (l ↦{dq} t : IProp GF) ⊢ structFieldRef Tx go!"writable" l ↦{dq} t.writable' ∗
      (structFieldRef Tx go!"writable" l ↦{dq} t.writable' -∗ l ↦{dq} t) := by
  iintro Ht
  icases (Tx_split_stats l dq t).1 $$ Ht with ⟨Hs, Hr⟩
  unfold Tx_rest_stats
  icases Hr with ⟨Hw, Hm, Hdb, Hmeta, Hroot, Hpages, Hch, HWF, %Hn⟩
  iframe Hw
  iintro Hw
  iapply (Tx_split_stats l dq t).2
  unfold Tx_rest_stats
  iframe
  ipureintro; exact Hn

theorem Tx.init.wp_proof (hmeta : DB.meta.spec (GF := GF) (hG := hG))
    (hCopy : Meta.Copy.spec (GF := GF) (hG := hG))
    (hnewBucket : newBucket.spec (GF := GF) (hG := hG))
    (hRootBucket : Meta.RootBucket.spec (GF := GF) (hG := hG))
    (hIncTxid : Meta.IncTxid.spec (GF := GF) (hG := hG)) :
    Tx.init.spec (GF := GF) (hG := hG) := by
  intro txl t dbl m0 m1 dq dq0 dq1 v0 v1 Hc0 Hc1 Hval
  wp_start as ⟨Ht, Hf0, Hf1, H0, H1⟩
  wp_auto
  try simp only
  wp_apply hmeta dbl m0 m1 dq dq0 dq1 v0 v1 Hc0 Hc1 Hval $$ [Hf0 Hf1 H0 H1] as ⟨%Hv, Hf0, Hf1, H0, H1⟩
  · iframe
  -- the meta `db.meta()` picked, at its fraction
  ihave Hm : (if metaPick v0 v1 then m1 else m0) ↦{if metaPick v0 v1 then dq1 else dq0}
      (if metaPick v0 v1 then v1 else v0) ∗
      ((if metaPick v0 v1 then m1 else m0) ↦{if metaPick v0 v1 then dq1 else dq0}
        (if metaPick v0 v1 then v1 else v0) -∗ m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1) $$ [H0 H1]
  · cases metaPick v0 v1
    · simp only [Bool.false_eq_true, ↓reduceIte]; iframe; iintro H0; iframe
    · simp only [↓reduceIte]; iframe; iintro H1; iframe
  icases Hm with ⟨Hm, Hmback⟩
  wp_apply hCopy _ _ _ _ _ $$ [Hm «$r0»] as ⟨Hm, Hml⟩
  · iframe
  ihave ⟨H0, H1⟩ := Hmback $$ Hm
  try wp_auto
  try simp only
  icases Tx_writable_acc _ _ _ $$ Ht with ⟨Htw, Htback⟩
  wp_apply hnewBucket txl _ (DFrac.own 1) $$ [Htw] as %bm %nm ⟨Htw, Hmaps⟩
  · iframe
  ihave Ht := Htback $$ Htw
  try wp_auto
  try simp only
  wp_apply hRootBucket _
  try wp_auto
  try simp only
  rename_i mlp
  cases Hw : t.writable'
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hmaps with %Hbn
    obtain ⟨rfl, rfl⟩ := Hbn
    try wp_auto
    ispecialize HΦ $$ %mlp %«$r0_ptr» %map.nil %map.nil %map.nil
    simp only [txInitOf, txMetaOf, newBucketOf, Hw, Bool.false_eq_true, ↓reduceIte]
    iapply HΦ; iframe; ipureintro; exact ⟨Hv, trivial, trivial, trivial⟩
  · simp only [↓reduceIte]
    icases Hmaps with ⟨Hbm, Hnm⟩
    try wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %pm Hpm
    try wp_auto
    try simp only
    wp_apply hIncTxid mlp _ $$ [Hml] as Hml
    · iframe
    try wp_auto
    ispecialize HΦ $$ %mlp %«$r0_ptr» %pm %bm %nm
    simp only [txInitOf, txMetaOf, newBucketOf, Hw, ↓reduceIte]
    iapply HΦ; iframe; ipureintro; exact Hv

end proof

end bbolt
end EtcdGrove
end Perennial
