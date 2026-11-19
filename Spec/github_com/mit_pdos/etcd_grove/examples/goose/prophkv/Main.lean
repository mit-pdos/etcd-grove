/- Lean-first (no Rocq counterpart).

`Main()` (`examples/goose/prophkv`): runs `Test` and panics unless its answer, `GetAny`'s, is
`"a"` or `"b"`, the two values written. Its triple says that it returns, so the panic is
unreachable: the program checks `GetAny`'s answer itself, and the closed theorem is that the
program never panics (`Results.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace goose_prophkv

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end goose_prophkv
end EtcdGrove
end Perennial
