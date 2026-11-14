/- Lean-first (no Rocq counterpart).

`(*rnd).choose(n)` (`examples/etcd/wal/wal.go`): a number below `n` (0 if `n` is 0).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev rnd.choose.spec : Prop :=
  ∀ (r : Loc) (v : rnd) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ r ↦ v }}
    (App (Val (r @!! go.GoType.PointerType rnd.ty @!! go!"choose")) (Val #n))
  {{ (k : w64), RET #k; (∃ v' : rnd, r ↦ v') ∗
      ⌜if n = W64 0 then k = W64 0 else uint.nat k < uint.nat n⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
