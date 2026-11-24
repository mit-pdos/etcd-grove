/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kv/Main.lean`. Lean-first (no Rocq
counterpart). `Main()` is `MainN(3)` (2026-11-15, kvraftN: until then `StartCluster([]uint64{1, 2,
3})` and `Check` here, now `MainN.lean`'s proof at `k = 3`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kv.MainN

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]

theorem Main.wp_proof (wp_MainN : raft_kv.MainN.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro Hrb
  wp_start as #Hcc
  wp_apply (wp_MainN (W64 3) Hrb) $$ [$Hcc]
  iapply HΦ
  itrivial

end proof

end raft_kv
end EtcdGrove
end Perennial
