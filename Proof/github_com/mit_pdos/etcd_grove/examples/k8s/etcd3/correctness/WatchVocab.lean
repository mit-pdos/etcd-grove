/-
Lean-first (no Rocq counterpart).

# Vocabulary of the specs of `correctness/watch.go` (k8s 7g step 5)

- `rangeRep p o`: the `*ResourceVersionRange` `p` is `nil` for no range (`o = none`), else a
  fresh range `[Min, Max)` (owned: `watchRevisionRange` raises its `Min`);
- `erefV r`: `toEventReference`'s `eventReference` of the reference `r` (`evRefL`'s key, type,
  resource version).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI


/-- **The `eventReference` of a reference** (see the file header). -/
def erefV [GooseExts] (r : GoString × GoString × w64) :
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventReference :=
  ⟨r.1, r.2.1, r.2.2⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*ResourceVersionRange` `p` is the range `o`** (see the file header). -/
def rangeRep (p : Loc) : Option (w64 × w64) → IProp GF
  | none => iprop(⌜p = null⌝)
  | some (mn, mx) =>
    iprop(p ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ResourceVersionRange.mk mn mx)

end defs

end k8s_correctness
end EtcdGrove
end Perennial
