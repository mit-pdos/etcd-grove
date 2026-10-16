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

/-- `EnsureConfState(cs)` of a non-`nil` conf state holding `c` returns `cs`, its `AutoLeave` set
(`csPts _ _ _ true`): it writes a `nil` `AutoLeave` (a fresh cell holding `false`, which reads the
same), so it takes the conf state fully owned unless its `AutoLeave` is already set (`al`), when
it writes nothing and a fraction will do (D7, stage R4: `MemoryStorage.InitialState` freezes the
storage's conf state, read-only for good with its `AutoLeave` set; the statement before D7 is the
instance `dq = 1`). Of `nil`, a fresh conf state holding the zero record, owned, its `AutoLeave`
set. (Decision on the plan's Q5: `Ensure*` takes ownership where it writes.) -/
abbrev raftpb.EnsureConfState.spec : Prop :=
  (∀ (cs : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csPts cs dq c al ∗
        ⌜dq ≠ DFrac.own 1 → al = true⌝ }}
      (App (Val #(functions raftpb.EnsureConfState [])) (Val #cs))
    {{ RET #cs; csPts cs dq c true }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val #(functions raftpb.EnsureConfState [])) (Val #(null : Loc)))
  {{ (r : Loc), RET #r; csPts r (DFrac.own 1) (ConfStateM.mk [] [] [] [] false) true }}

end spec

end EtcdGrove
end Perennial
