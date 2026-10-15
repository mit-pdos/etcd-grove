/-
`(*ConfState).Equivalent` (`raftpb/confstate.go:26`). Port of the old
`Spec/go_etcd_io/raft/v3/raftpb/ConfState__Equivalent.lean` to raft v3.7 (pointer receiver and
argument; `proto.Clone`, in-place sorts, `AutoLeave` normalized, `proto.Equal`; stage R1).
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

/-- `cs1.Equivalent(cs2)` returns `nil` iff the two `ConfState`s are `proto.Equal` after each was
cloned, its four id slices sorted and its `AutoLeave` made explicit (a nil one reads `false`).

For any two conf states with equal `AutoLeave` and each id list a permutation of the other's
(`CSLists.Perm` of their `lists`), each at most `2^62` long (`slices.Sort`'s bound): the sorted
clones hold the same record, so `proto.Equal` answers `true` (`proto.EqualConfState.spec`; neither
side has unknown fields, `csPts`) and the result is `nil`. As in the old spec, only the `nil`
outcome is specified: the one caller, `assertConfStatesEquivalent`, panics on anything else. Both
pointers are non-nil (`ownCSM`), so the nil-input error is not reached. -/
abbrev raftpb.ConfState.Equivalent.spec : Prop :=
  ∀ (p q : Loc) (c1 c2 : ConfStateM) (dq1 dq2 : DFrac),
  c1.lists.Perm c2.lists → c1.lists.Bounded → c1.AutoLeave' = c2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCSM p dq1 c1 ∗ ownCSM q dq2 c2 }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfState.ty @!! go!"Equivalent")) (Val #q))
  {{ RET #interface.nil; ownCSM p dq1 c1 ∗ ownCSM q dq2 c2 }}

end spec

end EtcdGrove
end Perennial
