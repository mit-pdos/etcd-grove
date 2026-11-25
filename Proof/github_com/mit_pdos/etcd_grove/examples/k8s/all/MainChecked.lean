/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/MainChecked.lean`: `ParamsOk`; out of
range, the early return; in range, the start bundle out of its wand, the two schedules drawn
(`cluster3.RandomSchedule`, made read-only), and `Main`'s triple at the member counts `uint.nat kᵢ`,
its range premises from `paramsOk`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.MainChecked
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.RandomSchedule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

theorem MainChecked.wp_proof
    (wp_ParamsOk : ParamsOk.spec (GF := GF) (hG := hG))
    (wp_RandomSchedule : cluster3.RandomSchedule.spec (GF := GF) (hG := hG))
    (wp_Main : Main.spec (GF := GF) (hG := hG)) :
    MainChecked.spec (GF := GF) (hG := hG) := by
  intro CS SE RT SC ST SV CRE CEC k₁ N ids ps ctxs boot k₂ ids' ps' ctxs' boot' clients ops
    watchers wops n₁ n₂ TB RB48 RBN HLv hlen Hbf hlen' Hbf' HwbN Haf Hbuq Hrf Hdbo Hms hAs Hse Hot
  wp_start as ⟨Hbundle, Htok, #Hprem1, #Hprem2, Hreg⟩
  ihave #Pc3 : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_ParamsOk k₁ clients ops watchers wops k₂ as %b %Hb
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
  have hok : paramsOk k₁ clients ops watchers wops k₂ := Hb.1 rfl
  obtain ⟨h1, h2, h21, h22, hc0, hw0, hc31, hops, hwops, hmul⟩ := id hok
  ihave Hb := Hbundle $$ %hok
  iunfold startBundle at Hb
  icases Hb with ⟨Hms1, Hbs1, Hms2, Hbs2⟩
  (try wp_auto)
  -- the two schedules, drawn
  wp_apply wp_RandomSchedule n₁ as %sl₁ ⟨%steps₁, Hsl₁, -⟩
  imod ownSlice_persist _ _ _ $$ Hsl₁ with #Hsl₁
  (try wp_auto)
  wp_apply wp_RandomSchedule n₂ as %sl₂ ⟨%steps₂, Hsl₂, -⟩
  imod ownSlice_persist _ _ _ $$ Hsl₂ with #Hsl₂
  (try wp_auto)
  -- `Main`, at the member counts `uint.nat kᵢ`
  have hM := wp_Main (uint.nat k₁) N ids ps ctxs boot (uint.nat k₂) ids' ps' ctxs' boot' clients ops
    watchers wops sl₁ sl₂ steps₁ steps₂ HLv (by word) (by word) hlen Hbf (by word) (by word) hlen'
    Hbf' HwbN Haf Hbuq Hrf Hdbo Hms hAs Hse Hot hc0 hw0 hc31 hops hwops hmul
  have e : ∀ k : w64, W64 ((uint.nat k : Nat) : Int) = k := fun k => by word
  simp only [e] at hM
  wp_apply hM $$ [Hms1 Hbs1 Hms2 Hbs2 Htok Hreg]
  · iframe; (try iframe #)
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end k8s_all
end EtcdGrove
end Perennial
