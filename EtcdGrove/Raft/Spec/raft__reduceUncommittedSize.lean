/-
Port of `election_proof/spec_raft__reduceUncommittedSize.v` (857d09190).
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

/-- `r.reduceUncommittedSize(s)` (`raft.go:2104`): the uncommitted-size estimate drops
by `s`, saturating at `0`. `uncommittedSize` is not in `NState`, so the state is
unchanged. -/
abbrev raft.reduceUncommittedSize.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (sz : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"reduceUncommittedSize"))
      (Val #sz))
  {{ RET #(); ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial
