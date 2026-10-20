/- Port of election_proof/spec_assertConfStatesEquivalent.v (feb5c73d4). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `assertConfStatesEquivalent l cs1 cs2` returns iff `cs1.Equivalent(cs2)` is `nil`,
and otherwise calls `l.Panic`. Stated for the case `ConfState.Equivalent`'s triple covers
(`Spec/ConfState__Equivalent.lean`): since 2026-10-14 (reconfiguration stage B8) any two
`ConfState`s with equal `AutoLeave` and each id list a permutation of the other's, joint ones
included (until then the non-joint case, now `specS`); the `Panic` path is then unreachable,
which is why the logger needs no contract here.

raft v3.7 (2026-10-15, stage R4): `cs1`, `cs2` are `*pb.ConfState`s (`ownCSM`, R1's
`ConfState.Equivalent` premise) holding `c1`, `c2`; the lists are the records' (`c1.lists`, until
the retarget `ownCSIds` over the slices). The non-joint statement `specS` and its derivation
`spec_simple` are gone with the slices they were stated on. -/
abbrev assertConfStatesEquivalent.spec : Prop :=
  ∀ (l : Logger) (cs1 cs2 : Loc) (c1 c2 : ConfStateM) (dq1 dq2 : DFrac),
  c1.lists.Perm c2.lists → c1.lists.Bounded →
  c1.AutoLeave' = c2.AutoLeave' →
  -- (2026-10-20, witness support) the same witness
  c1.Witness' = c2.Witness' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownCSM cs1 dq1 c1 ∗ ownCSM cs2 dq2 c2 }}
    (App (App (App (Val #(functions assertConfStatesEquivalent [])) (Val #l))
      (Val #cs1)) (Val #cs2))
  {{ RET #(); ownCSM cs1 dq1 c1 ∗ ownCSM cs2 dq2 c2 }}

end spec

end EtcdGrove
end Perennial
