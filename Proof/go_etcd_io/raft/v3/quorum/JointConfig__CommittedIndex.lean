/-
Port of election_proof/proof_JointConfig__CommittedIndex.v.

Lean notes: the two halves are read through their fields (`jointConfig_acc_Incoming`/
`_Outgoing`, `Base.lean`; until raft#285 `JointConfig` was a `[2]MajorityConfig`, read through
a local `array_acc_same'`).
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__CommittedIndex
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__CommittedIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The receiver is a value-receiver copy `c`: `c.Incoming` and `c.Outgoing` are handed to
`MajorityConfig.CommittedIndex` one after the other, each with its half's id set and the
indexer's resource; then `min`. The field reads go through `jointConfig_acc_*`. -/
theorem quorum.JointConfig.CommittedIndex.wp_proof
    (wp_MajorityConfig_CommittedIndex :
      quorum.MajorityConfig.CommittedIndex.spec (GF := GF) (hG := hG)) :
    quorum.JointConfig.CommittedIndex.spec (GF := GF) (hG := hG) := by
  intro cp dqc a v0 v1 s0 s1 l PP acked Harr Hsz0 Hsz1
  wp_start as ⟨Hc, Hv0, Hv1, #Hidx, HP⟩
  wp_auto
  wp_method_call
  wp_call
  wp_call
  wp_auto
  icases jointConfig_acc_Incoming _ _ _ v0 ((quorum.JointConfig.halves_eq _ _ _).1 Harr).1
    $$ c with ⟨Hc0, Hcback⟩
  ihave Hv0 := ownIdsetQ_toMaj _ _ $$ Hv0
  wp_apply wp_MajorityConfig_CommittedIndex s0 $$ [$Hc0 $Hidx $HP $Hv0]
    as %N0 ⟨Hc0, Hv0, HP, %Hemp0, %Hq0⟩
  · ipureintro; exact Hsz0
  ihave c := Hcback $$ Hc0
  icases jointConfig_acc_Outgoing _ _ _ v1 ((quorum.JointConfig.halves_eq _ _ _).1 Harr).2
    $$ c with ⟨Hc1, Hcback⟩
  ihave Hv1 := ownIdsetQ_toMaj _ _ $$ Hv1
  wp_apply wp_MajorityConfig_CommittedIndex s1 $$ [$Hc1 $Hidx $HP $Hv1]
    as %N1 ⟨Hc1, Hv1, HP, %Hemp1, %Hq1⟩
  · ipureintro; exact Hsz1
  ihave c := Hcback $$ Hc1
  ihave Hv0 := ownIdsetQ_ofMaj _ _ $$ Hv0
  ihave Hv1 := ownIdsetQ_ofMaj _ _ $$ Hv1
  wp_if_destruct
  · iapply HΦ
    iframe Hc Hv0 Hv1 HP
    ipureintro
    exact ⟨N0, N1, ⟨Hemp0, Hq0⟩, ⟨Hemp1, Hq1⟩, by rw [ite_eq_left (by word)]⟩
  · iapply HΦ
    iframe Hc Hv0 Hv1 HP
    ipureintro
    exact ⟨N0, N1, ⟨Hemp0, Hq0⟩, ⟨Hemp1, Hq1⟩, by rw [ite_eq_right (by word)]⟩

end proof

end EtcdGrove
end Perennial
