/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/transfers__take.lean`.
Lean-first (no Rocq counterpart), 2026-10-13.
-/
module

public import Proof.ReceiptTactics
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.transfers__take

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [StorageModel GF]

theorem transfers.take.wp_proof : transfers.take.spec (GF := GF) (hG := hG) := by
  intro bud tr
  wp_start as #Htr
  unfold isTransfers
  -- the transfer's tick credit (D19b): the receipt of the resolution of `Lock`
  wp_take_receipt as Hc1
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Htr] as ⟨Hlocked, HR⟩
  iunfold transfersInv at HR
  icases HR with ⟨%n, Hleft⟩
  by_cases Hn : n = W64 0
  · subst Hn
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Htr $Hlocked Hleft]
    · inext
      unfold transfersInv
      iexists W64 0
      iframe Hleft
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · have Hn' : uint.nat n = uint.nat (n - W64 1) + 1 := by
      have : uint.Z n ≠ 0 := fun h => Hn (by word)
      word
    wp_auto
    try (rw [decide_eq_false Hn])
    try simp only [Bool.not_false]
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Htr $Hlocked Hleft]
    · inext
      unfold transfersInv
      iexists n - W64 1
      iframe Hleft
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    unfold tickCred
    iexact Hc1

end proof

end kvwitness
end EtcdGrove
end Perennial
