/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/Entry__GetType.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.Entry.GetType.wp_proof :
    raftpb.Entry.GetType.spec (GF := GF) (hG := hG) := by
  constructor
  · intro l dq e
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cY
    · subst Hp
      wp_auto
      rw [show raftpb.EntryType_EntryNormal = #e.Type' by rw [Hv]; rfl]
      wp_auto
      iapply HΦ
      iunfold entPts
      iframe
      iexists uf
      isplitr
      · ipureintro; exact Hnn
      iframe cT cI cY Hd Hpb
    · wp_if_destruct
      · exact absurd rfl Hpn
      · iapply HΦ
        iunfold entPts
        iframe
        iexists uf
        isplitr
        · ipureintro; exact Hnn
        iframe cT cI cY Hd Hpb
  · wp_start
    wp_auto
    rw [show raftpb.EntryType_EntryNormal = #(W32 0) from rfl]
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
