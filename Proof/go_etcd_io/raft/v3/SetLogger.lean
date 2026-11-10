/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.SetLogger

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

/-- The store under `raftLoggerMu`, whose invariant (`isInitialized`'s `HloggerMu`) owns
`raftLogger`. -/
theorem SetLogger.wp_proof : SetLogger.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start
  ihave #HI := isInitialized_access $$ Hpkg
  iNamed HI
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock (globalAddr raftLoggerMu)
    iprop(∃ l : GoInterface, (globalAddr raftLogger ↦ l : IProp GF)) $$ [] as ⟨Hlocked, ⟨%l0, Hl⟩⟩
  · iframe #
  wp_apply sync.Mutex.wp_Unlock (globalAddr raftLoggerMu)
    iprop(∃ l : GoInterface, (globalAddr raftLogger ↦ l : IProp GF)) $$ [Hlocked Hl]
  · iframe #; iframe Hlocked; inext; iexists _; iexact Hl
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
