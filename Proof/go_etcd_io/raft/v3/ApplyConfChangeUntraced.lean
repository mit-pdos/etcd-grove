/-
Lean-first (no Rocq counterpart). Trace-check step 5 (2026-11-12): `raft.applyConfChange.untraced`, the
untraced statement `raft.applyConfChange.specU` from the one statement `raft.applyConfChange.spec`
(`Spec/go_etcd_io/raft/v3/raft__applyConfChange.lean`), out of the spec file (the layout). Raft-internal.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__applyConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section specLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- The untraced instance: the gate from the struct's nil logger (`hookGate_none`), `Q := emp`. -/
theorem raft.applyConfChange.untraced (H : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.specU (GF := GF) (hG := hG) := by
  intro c r id s cc ccm dq c' Happ Hsz Hltz Hcand Hli2 Htr
  iintro %Φ ⟨#Hpkg, Hphys, Hccs⟩ HΦ
  icases ownRaftPhysC_traceLogger (c := c) (V := c.voters) r id s Htr $$ Hphys with ⟨%tl, #Htl, %Hok, Hphys⟩
  iapply H c r id s cc ccm dq c' iprop(emp) Happ Hsz Hltz Hcand Hli2 (fun h => absurd Htr h)
    $$ [$Hpkg $Hphys $Hccs]
  · rw [Htr]
    iapply hookGate_none r _ tl iprop(emp) Hok
    iframe Htl
  inext
  iintro %cs %xs %os %ls %lns %s' ⟨Hphys, Hccs, Hcs, %Hp, %Hok', -⟩
  iapply HΦ $$ %cs %xs %os %ls %lns %s'
  iframe Hphys Hccs Hcs
  ipureintro; exact ⟨Hp, Hok'⟩

end specLC

end EtcdGrove
end Perennial
