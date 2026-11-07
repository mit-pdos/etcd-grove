/-
**The stop arm of `run`'s restart branch: what `raftNode.stop` takes, in restart form** (R2d'a A10
item 3, Q27 (i), 2026-11-06; `notes/restart-plan.md`, "R2d'a A10 item 3"). Lean-first (no Rocq
counterpart).

`stop_splitR`: `stop_split` over `applyResR` (`RunR.lean`), the rest kept as `applyResStopR`
(`StopShutdown.lean`), which `stopCleanupImage.spec` takes. (Swap batch 4, 2026-11-07: this file's
`applyResStopR`, `restReplay_bk`, `restLeasesWith_bk_congr` moved to `StopShutdown.lean`, and its
`stopCleanupImageR.spec`/`stop_cleanup_imageR`, inside the window only, merged into
`stopCleanupImage.spec`/`stop_cleanup_image`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopShutdown
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What `raftNode.stop` takes of the apply thread's resources, in restart form** (`stop_split`'s):
the WAL's apply half and the live transport. -/
theorem stop_splitR (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) :
    applyResR K C rp A ⊢
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ srvTrStop C.s ∗ applyResStopR K C rp A := by
  unfold applyResR applyResStopR
  iintro ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %hB, H1, H2, H3, H4, H5, H6, H7, H8, H9,
    H10, H11, H12, H13, H14, H15, H16, H17, Hap, Hlb, H18, Hwt, H19, H20, H21, %hp⟩
  iframe Hwt
  isplitl [Hap]
  · iapply srvApRes_trStop $$ Hap
  iexists B, st, ai, at', a, t, cs, x, sa, g
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 Hlb H18 H19 H20 H21
  ipureintro; exact ⟨hB, hp⟩

end laws

end EtcdGrove
end Perennial
