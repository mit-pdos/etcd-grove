/-
Proof of `checker.randomID`: `addrs` (read-only, `isChecker`), its length, `1 + below(len)`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__randomID
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

theorem checker.randomID.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    checker.randomID.spec (GF := GF) (hG := hG) := by
  intro c γ ls Hne
  wp_start as #Hc
  iunfold isChecker at Hc
  icases Hc with ⟨%sl, #Ha, #Hsl, #Hmu⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_apply wp_below as %r %Hr
  iapply HΦ
  ipureintro
  have hl : sint.nat sl.len = ls.length := by rw [Hlen.1]
  have h1 : sl.len ≠ W64 0 := by intro h; rw [h] at hl; rw [show sint.nat (W64 0) = 0 from rfl] at hl; omega
  have := Hr.2 h1
  constructor <;> word

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
