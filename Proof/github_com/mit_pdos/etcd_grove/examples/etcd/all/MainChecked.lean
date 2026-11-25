/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/MainChecked.lean`: `ParamsOk`; out of
range, the early return; in range, the start bundle out of its wand, the two schedules drawn
(`cluster3.RandomSchedule`, made read-only), and `Main`'s triple at the member counts `uint.nat kᵢ`,
its range premises from `paramsOk`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.RandomSchedule

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
    (wp_RandomSchedule : cluster3.RandomSchedule.spec (GF := GF) (hG := hG))
    (wp_Main : Main.spec (GF := GF) (hG := hG)) :
    MainChecked.spec (GF := GF) (hG := hG) := by
  intro CS ER FM RT N k₁ ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId ctxsCW
    bootCW cId ctxsC bootC kvId ctxsK bootK k₂ ids₂ ps₂ ctxs₂ boot₂ k₃ ids₃ ps₃ ctxs₃ boot₃
    k₄ ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL bootL k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR
    clients ops n₁ nw nops n₂ cnw cnops TB RB48 RBN HLv
    hlen₁ Hbf₁ HbfP HbfCW HbfC HbfK hlen₂ Hbf₂ hlen₃ Hbf₃ Hap hlen₄ Hbf₄ HbfL hlen₅ Hbf₅ HbfR Hwb
    Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat
  wp_start as ⟨Hbundle, Htok, Hp1, HpP, HpCW, HpC, HpK, Hp₂, Hp₃, Hp₄, HpL, Hp₅, HpR⟩
  ihave #Pc3 : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_ParamsOk k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅ as %b %Hb
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
  have hok : paramsOk k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅ := Hb.1 rfl
  obtain ⟨h1, h2, hc0, hc31, hops, hmul, hnw0, hnw31, hnops, hnmul, hcnw0, hcnw31, hcnops, hcmul,
    h21, h22, h31, h32, h41, h42, h51, h52⟩ := id hok
  ihave Hb := Hbundle $$ %hok
  iunfold startBundle at Hb
  icases Hb with ⟨Hms1, Hbs1, HresP, HresCW, HresC, HresK, Hms₂, Hms₃, Hms₄, HresL, Hms₅, HresR⟩
  (try wp_auto)
  -- the two schedules, drawn
  wp_apply wp_RandomSchedule n₁ as %sl₁ ⟨%steps₁, Hsl₁, -⟩
  imod ownSlice_persist _ _ _ $$ Hsl₁ with #Hsl₁
  (try wp_auto)
  wp_apply wp_RandomSchedule n₂ as %sl₂ ⟨%steps₂, Hsl₂, -⟩
  imod ownSlice_persist _ _ _ $$ Hsl₂ with #Hsl₂
  (try wp_auto)
  -- `Main`, at the member counts `uint.nat kᵢ`
  have hM := wp_Main N (uint.nat k₁) ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId
    ctxsCW bootCW cId ctxsC bootC kvId ctxsK bootK (uint.nat k₂) ids₂ ps₂ ctxs₂ boot₂
    (uint.nat k₃) ids₃ ps₃ ctxs₃ boot₃ (uint.nat k₄) ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL
    bootL (uint.nat k₅) ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR clients ops nw nops cnw cnops sl₁ sl₂
    steps₁ steps₂ HLv (by word) (by word) hlen₁ Hbf₁ HbfP HbfCW HbfC HbfK (by word) (by word) hlen₂
    Hbf₂ (by word) (by word) hlen₃ Hbf₃ Hap (by word) (by word) hlen₄ Hbf₄ HbfL (by word) hlen₅
    Hbf₅ HbfR Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat hc0 hc31 hops hmul hnw0 hnw31 hnops hnmul
    hcnw0 hcnw31 hcnops hcmul
  have e : ∀ k : w64, W64 ((uint.nat k : Nat) : Int) = k := fun k => by word
  simp only [e] at hM
  wp_apply hM $$ [Hms1 Hbs1 HresP HresCW HresC HresK Hms₂ Hms₃ Hms₄ HresL Hms₅ HresR Htok
    Hp1 HpP HpCW HpC HpK Hp₂ Hp₃ Hp₄ HpL Hp₅ HpR]
  · iframe; (try iframe #)
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end etcd_all
end EtcdGrove
end Perennial
