/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09).

**The recorder is a trace logger**: `isSyncRecorder γt r` gives raft's logger contract,
`isTraceLogger γt` (`InvTrace.lean`), of the interface value the harness puts in raft's
`Config.TraceLogger` (`c.rec`, a `*SyncRecorder`), from `(*SyncRecorder).TraceEvent`'s spec.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder__TraceEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section logger
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
theorem isSyncRecorder_traceLogger
    (wp_TraceEvent : SyncRecorder.TraceEvent.spec (GF := GF) (hG := hG)) (γt : GName) (r : Loc) :
    isSyncRecorder (GF := GF) γt r ⊢
      isTraceLogger γt (interface.mkOk
        (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder.ty) #r) := by
  iintro #Hrec
  unfold isTraceLogger
  iright
  iexists ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder.ty, #r⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %p %e %Q #Hev Hau
  ihave #Hinit : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck $$ [Hrec]
  · iunfold isSyncRecorder at Hrec
    icases Hrec with ⟨#Hi, -⟩
    iexact Hi
  iapply wp_TraceEvent γt r p e Q $$ [Hau]
  · iframe Hinit Hrec Hev Hau
  inext
  iintro HQ
  isplitr
  · ipureintro; rfl
  iexact HQ

end logger

end TraceCheck
end EtcdGrove
end Perennial
