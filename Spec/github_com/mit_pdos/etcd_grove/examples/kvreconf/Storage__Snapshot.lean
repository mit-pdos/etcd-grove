/-
Lean-first (no Rocq counterpart).

# `(*Storage).Snapshot` (kv.go)

```go
func (s *Storage) Snapshot() (*pb.Snapshot, error) {
	if oneIn(4) {
		return nil, raft.ErrSnapshotTemporarilyUnavailable
	}
	return s.MemoryStorage.Snapshot()
}
```

`MemoryStorage.Snapshot.spec` at the wrapper (`kvrStorRec`): the embedded storage's answer, or
`ErrSnapshotTemporarilyUnavailable` (`esu`, read off the global, as the contract's `HSnapshot`
clause gives it), which `MemoryStorage`'s answer may be already.
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
abbrev Storage.Snapshot.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (c : Nat) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      kvrStorRec s ms γs ∗ memStorInvP ms γs J ∗ memCompacted γs c ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ⌜err = esu⌝ ∨
      ⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜c ≤ uint.nat sv.Metadata'.Index'⌝ ∗
        (⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')) }}

end spec

end kvreconf
end EtcdGrove
end Perennial
