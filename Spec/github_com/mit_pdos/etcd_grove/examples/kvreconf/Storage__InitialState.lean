/-
Lean-first (no Rocq counterpart).

# `(*Storage).InitialState` (kv.go)

```go
func (s *Storage) InitialState() (*pb.HardState, *pb.ConfState, error) {
	hs, _, err := s.MemoryStorage.InitialState()
	return hs, proto.Clone(s.boot).(*pb.ConfState), err
}
```

The embedded `MemoryStorage`'s hard state (its `InitialState`, before the storage's invariant is
allocated: `memStorMeta`, `memStorFresh`, given back), and a fresh owned clone of the bootstrap
conf state (`kvrStorBoot`); the error is `nil` (`MemoryStorage`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KvrStor GF]

/-- See the file header. -/
abbrev Storage.InitialState.spec : Prop :=
  ∀ (s ms bp : Loc) (γs : MemStorNames) (hs : HardStateM) (csm : ConfStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      kvrStorRec s ms γs ∗ kvrStorBoot s bp csm ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"InitialState")) (Val #()))
  {{ (hp cs : Loc), RET (PairV (PairV #hp #cs) #interface.nil);
      hsOpt hp hs ∗ memStorMeta ms γs hs ∗ memStorFresh ms γs ∗ ownCSM cs (DFrac.own 1) csm }}

end spec

end kvreconf
end EtcdGrove
end Perennial
