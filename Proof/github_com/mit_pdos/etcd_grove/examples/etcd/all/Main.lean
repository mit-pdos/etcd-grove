/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Main.lean`: `Main` calls `Restart` with
the main thread's token. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Main

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

theorem Main.wp_proof
    (wp_Restart : Restart.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro N k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR TB RB48 RBN HLv
    hk₅ hlen₅ Hbf₅ HbfR Hwb Haf Hbuq Hdbo
  wp_start as ⟨Hms₅, HresR, Htok, Hp₅, HpR⟩
  (try wp_auto)
  -- `Restart(k5)`, with the main thread's token
  wp_apply (wp_Restart N k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR HLv hk₅ hlen₅ Hbf₅ HbfR Hwb Haf
    Hbuq Hdbo) $$ [Hms₅ HresR Htok Hp₅ HpR]
  · iframe; (try iframe #)
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end etcd_all
end EtcdGrove
end Perennial
