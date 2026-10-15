/-
`EnsureConfState` (`raftpb/util.go`, new in raft v3.7). Lean-first (raft v3.7 retarget, stage
R1).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `EnsureConfState(cs)` of a conf state pointer, `nil` or owned (fully: it may write its
`AutoLeave`) holding `c`: a non-`nil` conf state holding `c`, with `AutoLeave` set (`csPts _ _ _
true`), owned; `cs` itself when `cs` was not `nil` (a fresh one otherwise). The model value does
not change: a `nil` `AutoLeave` read `false`, the cell it is given holds `false` (decision on the
plan's Q5: `Ensure*` takes ownership where it writes). -/
abbrev raftpb.EnsureConfState.spec : Prop :=
  ∀ (cs : Loc) (c : ConfStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csOpt cs (DFrac.own 1) c }}
    (App (Val #(functions raftpb.EnsureConfState [])) (Val #cs))
  {{ (r : Loc), RET #r; csPts r (DFrac.own 1) c true ∗ ⌜cs ≠ null → r = cs⌝ }}

end spec

end EtcdGrove
end Perennial
