/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*bootStorage).InitialState()`: its `MemoryStorage`'s hard state, and the conf state
`bootConfState vs sv`: a fresh `ConfState{Voters: s.voters}` while the stored snapshot `sv` is at
index `0`, the storage's otherwise. Before the storage's invariant is allocated (`memStorFresh`, as
`MemoryStorage.InitialState.spec`; the `Snapshot` call is its detached mode), what
`restartStorage`'s `InitialState` triple asks (`hsOpt`, `csPts … DFrac.discard`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev bootStorage.InitialState.spec : Prop :=
  ∀ (s ms : Loc) (vs : List w64) (γs : MemStorNames) (hs : HardStateM) (c : Nat) (sv : SnapshotM)
    (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ bootStorRec s ms vs ∗ memStorLock ms γs ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs c sv ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp hs ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs c sv ∗
      csPts cs DFrac.discard (bootConfState vs sv) al }}

end spec

end AntHarness
end EtcdGrove
end Perennial
