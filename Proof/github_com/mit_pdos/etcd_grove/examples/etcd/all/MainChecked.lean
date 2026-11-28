/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/MainChecked.lean`: `ParamsOk`; out of
range, the early return; in range, the start bundle out of its wand and `Main`'s triple at the member
count `uint.nat k₅`, its range premise from `paramsOk`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked

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

theorem MainChecked.wp_proof
    (wp_ParamsOk : ParamsOk.spec (GF := GF) (hG := hG))
    (wp_Main : Main.spec (GF := GF) (hG := hG)) :
    MainChecked.spec (GF := GF) (hG := hG) := by
  intro N k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR TB RB48 RBN HLv
    hlen₅ Hbf₅ HbfR Hwb Haf Hbuq Hdbo
  wp_start as ⟨Hbundle, Htok, Hp₅, HpR⟩
  (try wp_auto)
  wp_apply wp_ParamsOk k₅ as %b %Hb
  (try wp_auto)
  cases b
  · -- out of range: `return`
    (try simp only [Bool.not_false])
    (try wp_auto)
    iapply HΦ
    itrivial
  -- in range
  (try simp only [Bool.not_true])
  (try wp_auto)
  have hok : paramsOk k₅ := Hb.1 rfl
  obtain ⟨h51, h52⟩ := id hok
  ihave Hb := Hbundle $$ %hok
  iunfold startBundle at Hb
  icases Hb with ⟨Hms₅, HresR⟩
  (try wp_auto)
  -- `Main`, at the member count `uint.nat k₅`
  have hM := wp_Main N (uint.nat k₅) ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR HLv (by word) hlen₅
    Hbf₅ HbfR Hwb Haf Hbuq Hdbo
  have e : ∀ k : w64, W64 ((uint.nat k : Nat) : Int) = k := fun k => by word
  simp only [e] at hM
  wp_apply hM $$ [Hms₅ HresR Htok Hp₅ HpR]
  · iframe; (try iframe #)
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end etcd_all
end EtcdGrove
end Perennial
