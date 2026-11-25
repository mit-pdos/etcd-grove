/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*bootStorage).Term(i)`: its `MemoryStorage`'s (`MemoryStorage.Term.spec` at the wrapper).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase

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
abbrev bootStorage.Term.spec : Prop :=
  ∀ (s ms : Loc) (vs : List w64) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (i0 : w64)
    (ec : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ bootStorRec s ms vs ∗ memStorLock ms γs ∗
      memLog γs k dq es ∗ ⌜k ≤ uint.nat i0 ∧ uint.nat i0 < k + es.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty @!! go!"Term")) (Val #i0))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      memLog γs k dq es ∗
      (⌜err = interface.nil ∧ (fun e : EntryM => e.Term') <$> es[uint.nat i0 - k]? = some t⌝ ∨
       (⌜err = ec⌝ ∗ memCompacted γs (uint.nat i0 + 1))) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
