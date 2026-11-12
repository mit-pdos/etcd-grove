/- Port of election_proof/proof_traceInitState.v. -/
module

public import Spec.go_etcd_io.raft.v3.traceInitState
public import Spec.go_etcd_io.raft.v3.traceNodeEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceInitState.wp_proof
    (wp_traceNodeEvent : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceInitState.spec (GF := GF) (hG := hG) := by
  intro r tl tr E Q R
  wp_start as ⟨#Htl, Hown, Hfire⟩
  cases tl with
  | nil =>
    wp_auto
    iapply HΦ
    isplitl [Hown]
    · iapply trOwn_wand
      iframe Hown
      iintro ⟨%c, %id, %s, %P, Hp, -, -, Hb⟩
      iapply Hb $$ Hp
    iapply traceFire_nil $$ Hfire
  | ok l =>
    cases tr with
    | none =>
      icases (traceFire_none _ E Q).1 $$ Hfire with ⟨%Hok, -⟩
      exact absurd Hok (by unfold TraceLoggerOk; exact nofun)
    | some γd =>
      icases (trOwn_some γd _).1 $$ Hown with ⟨%c, %id, %s, %P, Hphys, #Hlend, %Hp, Hback⟩
      obtain ⟨Hs, HE⟩ := Hp
      wp_auto
      wp_apply wp_traceNodeEvent (W64 0) c r id s _ Q P (by decide) $$ [$Htl Hphys Hfire]
        as ⟨Hphys, HQ⟩
      · rw [Hs]
        isplitl [Hphys]
        · iapply (trOwn_some γd _).2; iframe Hphys Hlend
        iapply traceFire_mono_E _ _ E _ Q HE $$ Hfire
      iapply HΦ
      iframe HQ
      iapply (trOwn_some γd R).2
      rw [Hs]
      iapply Hback
      iapply (trOwn_some γd _).1
      iexact Hphys

end proof

end EtcdGrove
end Perennial
