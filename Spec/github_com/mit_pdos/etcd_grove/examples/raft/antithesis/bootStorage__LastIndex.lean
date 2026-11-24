/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*bootStorage).LastIndex()`: its `MemoryStorage`'s (`MemoryStorage.LastIndex.spec` at the
wrapper).
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
abbrev bootStorage.LastIndex.spec : Prop :=
  ∀ (s ms : Loc) (vs : List w64) (γs : MemStorNames) (e : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ bootStorRec s ms vs ∗ memStorLock ms γs ∗ memEnd γs e }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty @!! go!"LastIndex")) (Val #()))
  {{ (li : w64), RET (PairV #li #interface.nil); memEnd γs e ∗ ⌜uint.nat li + 1 = e⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
