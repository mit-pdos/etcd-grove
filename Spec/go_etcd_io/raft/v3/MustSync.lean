/-
Port of `election_proof/spec_MustSync.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `MustSync(st, prevst, entsnum)` (`rawnode.go:193`): whether the `Ready` has to be
written durably before its messages are sent --
`entsnum != 0 || st.Vote != prevst.Vote || st.Term != prevst.Term`.

raft v3.7 (2026-10-15, stage R4): `st`, `prevst` are `*pb.HardState`s read through their
getters, each possibly `nil` (`hsOpt`). -/
abbrev MustSync.spec : Prop :=
  ∀ (st prevst : Loc) (hs phs : HardStateM) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "#Hst" ∷ hsOpt st hs ∗ "#Hprev" ∷ hsOpt prevst phs }}
    (App (App (App (Val #(functions MustSync [])) (Val #st)) (Val #prevst)) (Val #n))
  {{ RET #(decide (n ≠ W64 0 ∨ hs.Vote' ≠ phs.Vote' ∨ hs.Term' ≠ phs.Term'));
      True }}

end spec

end EtcdGrove
end Perennial
