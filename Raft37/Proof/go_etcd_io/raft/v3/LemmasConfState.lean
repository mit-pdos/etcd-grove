/-
`EnsureConfState` on a snapshot's nested conf state (`csOptA`, D7, stage R4 of the raft v3.7
retarget): the conf state frozen read-only for good with its `AutoLeave` set. Used where raft
keeps a snapshot's conf state pointer while the snapshot stays its owner's
(`MemoryStorage.InitialState`, `raft.restore`).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPbLog
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `EnsureConfState` on a snapshot's non-`nil` nested conf state held at `1` (`csOptA`): `pc`
itself, the conf state with its `AutoLeave` set, frozen read-only for good (an owned one after
`EnsureConfState` wrote its `AutoLeave`, a frozen one as it was). The snapshot then holds it as
`csOptA`'s third case. -/
theorem wp_EnsureConfState_freeze
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (pc : Loc) (c : ConfStateM) (Hpc : pc ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csOptA pc (DFrac.own 1) c }}
      (App (Val #(functions raftpb.EnsureConfState [])) (Val #pc))
    {{ RET #pc; csPts pc DFrac.discard c true }} := by
  iintro %Φ ⟨#Hinit, Hc⟩ HΦ
  iunfold csOptA at Hc
  icases Hc with (⟨%Hp, -⟩ | Hc | #Hc)
  · exact absurd Hp Hpc
  · iapply wp_fupd
    wp_apply wp_EnsureConfState.1 pc (DFrac.own 1) c false $$ [Hc] as Hcs
    · iframe; ipureintro; intro h; exact absurd rfl h
    imod csPts_persist _ _ _ _ $$ Hcs with #Hcs
    imodintro
    iapply HΦ; iexact Hcs
  · wp_apply wp_EnsureConfState.1 pc DFrac.discard c true $$ [] as #Hcs
    · iframe Hc; ipureintro; intro _; rfl
    iapply HΦ; iexact Hcs

end lemmas

end EtcdGrove
end Perennial
