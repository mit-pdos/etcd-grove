/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `r.tick` is one of the two tick functions (`TickFnOk`, since `r.tick` is set:
`NStateWf`); either one's `TickStep` keeps `ownRawNode` but for the term. -/
theorem RawNode.Tick.wp_proof
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hterm
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  wp_apply raft.wp_load_tick γ.reCfg rnv.raft' id s Hrel.2.2 $$ Hphys as %f ⟨Hphys, %Hf⟩
  rcases Hf with rfl | rfl
  all_goals first
    | wp_apply wp_tickElection γ.reCfg γ rnv.raft' id s ps rfl Hin
        (by rw [← Htrm]; exact Hterm) Hrel
        $$ [$Hphys $Hghost] as %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, %Htk⟩
    | wp_apply wp_tickHeartbeat γ.reCfg γ rnv.raft' id s ps rfl Hin Hrel
        $$ [$Hphys $Hghost] as %s' %ps' ⟨Hphys, Hghost, %Hrel', %Href, %Htk⟩
  all_goals (
    obtain ⟨⟨Ha, Hsn, Hu⟩, Ht1, Ht2, Hi⟩ := Htk
    have Hc : uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
      obtain ⟨recv, Hst⟩ := Href
      have H := Step.commit_mono Hst
      rw [← Hrel.1, ← Hrel'.1] at H
      exact H
    iapply HΦ $$ %s'.term
    isplitl
    · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' ps' rnv sv steps Hrel' Hin
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
        (fun h => stepsOk_mono_le s s' _ Ht1 Hi Hc Ha (Hadv h)) rfl
        $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv
    ipureintro
    rw [Htrm]
    exact ⟨Ht1, Ht2⟩)

end proof

end EtcdGrove
end Perennial
