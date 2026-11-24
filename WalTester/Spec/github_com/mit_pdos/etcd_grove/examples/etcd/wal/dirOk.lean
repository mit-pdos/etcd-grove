/- Lean-first (no Rocq counterpart).

`dirOk(p)` (`examples/etcd/wal/wal.go`): `true` only for a clean absolute directory `/s₁/…/sₙ`
(`n ≥ 1`) of segments of at most 255 bytes, shorter than 4000 bytes (`tDirOk`). Only soundness is
stated: `Main` returns on `false`, so a `false` on an acceptable path loses no safety.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.DirOk

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
abbrev dirOk.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.dirOk)) (Val #p))
  {{ (b : Bool), RET #b; ⌜b = true → tDirOk p⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
