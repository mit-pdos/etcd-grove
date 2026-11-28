/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*bootStorage).Entries(lo, hi, maxSize)`: its `MemoryStorage`'s (`MemoryStorage.Entries.spec` at
the wrapper, `bootStorRec`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries

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
abbrev bootStorage.Entries.spec : Prop :=
  ∀ (s ms : Loc) (vs : List w64) (γs : MemStorNames) (k : Nat) (dq1 dq2 : DFrac) (a b : List EntryM)
    (lo hi maxSize : w64) (ec : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ bootStorRec s ms vs ∗ memStorLock ms γs ∗
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ⌜k ≤ uint.nat lo ∧ uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ k + a.length + b.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec }}
    (App (App (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty @!! go!"Entries")) (Val #lo)) (Val #hi)) (Val #maxSize))
  {{ (sl : GoSlice) (es : List EntryM) (err : GoInterface), RET (PairV #sl #err);
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ((⌜err = ec⌝ ∗ memCompacted γs (uint.nat lo)) ∨
       (⌜err = interface.nil⌝ ∗
        (∃ (cs : List EntryC), entsPtsC γs.sz sl DFrac.discard cs ∗
          ⌜cs.map EntryC.model = es ∧
            (γs.sz = true → uint.nat maxSize ≤ entsCutMax → entsCut maxSize cs)⌝) ∗
        ⌜es ≠ [] ∧ sl.cap = sl.len ∧
          (es <+: ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo)) ∧
          (maxSize = W64 (-1) → es = ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo))⌝)) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
