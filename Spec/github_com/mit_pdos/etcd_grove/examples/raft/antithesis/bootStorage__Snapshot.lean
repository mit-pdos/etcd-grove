/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*bootStorage).Snapshot()`: its `MemoryStorage`'s (`MemoryStorage.Snapshot.spec` at the wrapper).
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
abbrev bootStorage.Snapshot.spec : Prop :=
  ∀ (s ms : Loc) (vs : List w64) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (c : Nat) (t : Option SnapshotM) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ bootStorRec s ms vs ∗ memStorAt ms γs J o emp ∗
      memCompacted γs c ∗ (match t with | some sv => memSnapNone γs sv | none => emp) ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      (match t with | some sv => memSnapNone γs sv | none => emp) ∗
      ⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapW snap (DFrac.own 1) sv ∗
         ⌜c ≤ uint.nat sv.Metadata'.Index' ∧ (∀ s0, t = some s0 → sv = s0)⌝ ∗
         (match o with
          | some (c0, sv0) => iprop(⌜sv = sv0⌝ ∗ memStorFresh ms γs c0 sv0)
          | none => iprop(⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index'))) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
