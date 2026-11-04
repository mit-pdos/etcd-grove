/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Cursor_i.lean` (U6, `notes/bbolt-proof-plan.md`), over `TxStats.IncCursorCount`'s spec.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.TxStats__IncCursorCount
public import Proof.go_etcd_io.bbolt.Read.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Cursor_i.wp_proof (hInc : TxStats.IncCursorCount.spec (GF := GF) (hG := hG)) :
    Bucket.Cursor_i.spec (GF := GF) (hG := hG) := by
  intro K tx r m q b dq
  wp_start as ⟨#Hcore, #Hreg, Hst, Hbtx⟩
  wp_auto
  wp_apply (hInc K tx r m q (W64 1)) $$ [Hst] as %n Hst
  · iframe; iframe #
  try wp_auto
  wp_apply wp_slice_make2 (V := elemRef) (W64 0) $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  try wp_auto
  iapply HΦ
  iexists sl
  simp only [List.replicate_zero]
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
