/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/transfers__take.lean`.
Lean-first (no Rocq counterpart), 2026-10-13.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.transfers__take

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [StorageModel GF]

theorem transfers.take.wp_proof : transfers.take.spec (GF := GF) (hG := hG) := by
  intro bud tr
  wp_start as #Htr
  unfold isTransfers
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Htr] as ⟨Hlocked, HR⟩
  iunfold transfersInv at HR
  icases HR with ⟨%n, Hleft, Hcred⟩
  by_cases Hn : n = W64 0
  · subst Hn
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Htr $Hlocked Hleft Hcred]
    · inext
      unfold transfersInv
      iexists W64 0
      iframe Hleft Hcred
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
    rw [Hn']
    icases (tickCred_split bud (uint.nat (n - W64 1)) 1).1 $$ Hcred with ⟨Hcred, Hc1⟩
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Htr $Hlocked Hleft Hcred]
    · inext
      unfold transfersInv
      iexists n - W64 1
      iframe Hleft Hcred
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iexact Hc1

end proof

end register
end EtcdGrove
end Perennial
