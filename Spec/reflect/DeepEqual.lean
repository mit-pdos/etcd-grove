/-
`reflect.DeepEqual(cs1, cs2)` on two `raftpb.ConfState` values, as
`ConfState.Equivalent` calls it. Lean-first (no Rocq counterpart); see
`InvRaftpb.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftpb

@[expose] public section

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

/-- **Trust boundary.** `reflect.DeepEqual` is Go reflection, which Goose does not
model (`reflect` is translated names-only), so this is an `axiom`: Go's `DeepEqual`
on two `ConfState` values (`raft.pb.go`: four `[]uint64` fields and a `bool`), read
against `reflect/deepequal.go`: structs field by field; a `bool` by `==`; a slice
field is `DeepEqual` iff both are nil or both non-nil with equal length and
`DeepEqual` elements, here `uint64`s by `==`. That is `confStateDeepEq`
(`InvRaftpb.lean`). It reads the eight slices and returns them.

Stated for the one caller: both arguments converted from `ConfState`
(`interface.mkOk raftpb.ConfState.ty`), every slice fully owned (they are
`Equivalent`'s fresh sorted copies). -/
abbrev reflect.DeepEqual.spec : Prop :=
  ∀ (a b : raftpb.ConfState) (av al avo aln bv bl bvo bln : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect ∗
      a.Voters' ↦* av ∗ a.Learners' ↦* al ∗ a.VotersOutgoing' ↦* avo ∗ a.LearnersNext' ↦* aln ∗
      b.Voters' ↦* bv ∗ b.Learners' ↦* bl ∗ b.VotersOutgoing' ↦* bvo ∗ b.LearnersNext' ↦* bln }}
    (App (App (Val #(functions reflect.DeepEqual []))
      (Val #(interface.mkOk raftpb.ConfState.ty #a))) (Val #(interface.mkOk raftpb.ConfState.ty #b)))
  {{ RET #(decide (confStateDeepEq a b av al avo aln bv bl bvo bln));
      a.Voters' ↦* av ∗ a.Learners' ↦* al ∗ a.VotersOutgoing' ↦* avo ∗ a.LearnersNext' ↦* aln ∗
      b.Voters' ↦* bv ∗ b.Learners' ↦* bl ∗ b.VotersOutgoing' ↦* bvo ∗ b.LearnersNext' ↦* bln }}

end spec

end EtcdGrove
end Perennial
