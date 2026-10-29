/- Lean-first (no Rocq counterpart).

`s.add(c)` (cluster.go): adds one to the counter `c` (`isCounter`, `Stats.lean`), from any
goroutine.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats

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

/-- See the file header. -/
abbrev Stats.add.spec : Prop :=
  ∀ (s c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      isCounter c }}
    (App (Val (s @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats.ty
      @!! go!"add")) (Val #c))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial
