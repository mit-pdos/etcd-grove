/-
`proto.Equal` of two raft v3.7 `*pb.ConfState`s: the trust boundary, stage R1. `ConfState.Equivalent`
compares its sorted clones with it (`raftpb/confstate.go:48`), replacing `reflect.DeepEqual` (the
old axiom `reflect.DeepEqual`, `notes/decisions.md`, "`ConfState.Equivalent`: `reflect.DeepEqual` is
the axiom, not the raft code").
Lean-first; stated over the raftpb ownership predicates of `Proof/go_etcd_io/raft/v3/InvPb.lean`
(a raft v3.7 statement about `proto.*`, kept apart from the etcd side's `Clone.lean`, `Size.lean`,
`Marshal.lean`, `Unmarshal.lean`, as `MarshalIRR.lean` is from `Marshal.lean`; until stage R6 swapped
the raft trees, 2026-10-16, this file was the only one importing the `Raft37` tree's raftpb).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

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

/-- `proto.Equal(cs1, cs2)` of two `*pb.ConfState`s holding `c1` and `c2`, each with its
`AutoLeave` set (`csPts _ _ _ true`), is `true` iff `c1 = c2`.

Against protobuf-go v1.36.11 (`proto/equal.go`, `internal/impl/equal.go`): two valid messages
are equal iff they have the same populated known fields with equal values and equal unknown
fields; repeated fields are equal iff of the same length with equal elements (`nil` and empty
alike); an optional `bool` is populated iff its pointer is set. Both `AutoLeave`s are set (the
premise, as `Equivalent` makes them), so they compare by value; neither side has unknown fields
(`csPts`); and the identical-pointer shortcut (`x == y`) answers `true` only where the two records
agree anyway. So the answer is the equality of the records. -/
abbrev proto.EqualConfState.spec : Prop :=
  ∀ (p q : Loc) (dq1 dq2 : DFrac) (c1 c2 : ConfStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ csPts p dq1 c1 true ∗ csPts q dq2 c2 true }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Equal)) (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p)))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #q)))
  {{ (b : Bool), RET #b; csPts p dq1 c1 true ∗ csPts q dq2 c2 true ∗ ⌜b = true ↔ c1 = c2⌝ }}

end spec

end EtcdGrove
end Perennial
