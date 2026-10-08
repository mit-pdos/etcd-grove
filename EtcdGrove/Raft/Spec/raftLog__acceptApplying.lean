/-
Port of `election_proof/spec_raftLog__acceptApplying.v` (857d09190).
-/
import EtcdGrove.Raft.InvReadylog

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.acceptApplying(i, size, allowUnstable)` (`log.go:345`): the entries up to `i`
have been handed out for applying.

    if l.committed < i { l.logger.Panicf(...) }
    l.applying = i
    l.applyingEntsSize += size
    l.applyingEntsPaused = l.applyingEntsSize >= l.maxApplyingEntsSize ||
        i < l.maxAppliableIndex(allowUnstable)

`applying` becomes `i` and `applyingEntsSize` grows by `size` (a `uint64` sum, as Go
computes it); the paused flag is internal. The premise is the `Panicf`'s guard and,
below, what keeps `applied <= applying` (`acceptReady` passes the last committed entry
handed out, above `applying`). -/
abbrev raftLog.acceptApplying.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64) (au : Bool),
  uint.Z ls.applied ≤ uint.Z i ∧ uint.Z i ≤ uint.Z ls.committed →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"acceptApplying"))
      (Val #i)) (Val #size)) (Val #au))
  {{ RET #(); ownRaftLog l { ls with applying := i, apsize := ls.apsize + size } }}

end spec

end EtcdGrove
end Perennial
