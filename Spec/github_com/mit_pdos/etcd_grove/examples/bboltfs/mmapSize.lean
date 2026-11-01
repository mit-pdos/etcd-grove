/- Lean-first (no Rocq counterpart). `mmapSize(size)` (`examples/bboltfs/minibolt.go`): the smallest power of two from 32 KiB up that holds `size`, as the bounds its callers need: at least `size` and 32 KiB, at most `max 32768 (2 * size)`, a whole number of pages, and at most 1 GiB if `size` is. `size ≤ 2^40` keeps the doubling from overflowing. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev mmapSize.spec : Prop :=
  ∀ (size : w64),
    {{ (⌜sint.Z size ≤ 2 ^ 40⌝ : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.mmapSize)) (Val #size))
    {{ (n : w64), RET #n; ⌜sint.Z size ≤ sint.Z n ∧ 32768 ≤ sint.Z n ∧
        sint.Z n ≤ max 32768 (2 * sint.Z size) ∧ sint.Z n % 4096 = 0 ∧
        (sint.Z size ≤ 2 ^ 30 → sint.Z n ≤ 2 ^ 30)⌝ }}

end spec

end bboltfs
end EtcdGrove
end Perennial
