/-
`tx.recursivelyCheckPageKeyOrder(pgId, keyToString, ch)` of `tx_check.go` (U10h of
`notes/bbolt-proof-plan.md`) on a root of a reader's view whose tree has B+tree keys: the internal
check from the root with no bounds and an empty stack sends nothing (`Commit/CheckKeyOrderInt`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckInv
public import Proof.go_etcd_io.bbolt.Commit.CheckKeyOrderInt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.recursivelyCheckPageKeyOrder_ok.wp_proof
    (wp_int : Tx.recursivelyCheckPageKeyOrderInternal_ok.spec (GF := GF) (hG := hG)) :
    Tx.recursivelyCheckPageKeyOrder_ok.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v r f ch hwm hwf hkeys
  wp_start as Hk
  obtain ⟨pg, hpg⟩ : ∃ pg, v.pages !! r.toNat = some pg := by
    cases hwf with | page _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩
  wp_auto
  ihave Hs := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hcap := ownSliceCap_nil (V := w64) (GF := GF)
  wp_apply (wp_int K tx src q T v r pg hwm none none none slice.nil slice.nil slice.nil [] f ch
    hpg hwf hkeys rfl (.inl rfl) rfl) $$ [Hk Hs Hcap] as %res ⟨Hk, -, -, -⟩
  · iframe
    isplitr
    · iexact Hs
    · iexact Hcap
  try wp_auto
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
