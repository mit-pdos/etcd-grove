/- Lean-first (no Rocq counterpart).

`walMustSync(last, h, nents)` (`examples/etcd/wal/ref.go`): whether a `Save` of `h` and `nents`
entries syncs, against the last saved hard state (`tMustSync`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

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
abbrev walMustSync.spec : Prop :=
  ∀ (last h : THs) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.walMustSync)) (Val #last))
      (Val #h)) (Val #n))
  {{ RET #(tMustSync last h (sint.nat n)); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
