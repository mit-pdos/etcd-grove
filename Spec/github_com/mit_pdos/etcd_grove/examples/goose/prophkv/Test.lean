/- Lean-first (no Rocq counterpart).

`Test()` (`examples/goose/prophkv`): a `Put` of `"k"` with `"a"`, then a goroutine's `Put` of `"b"`
concurrent with a `GetAny` of `"k"`, whose answer `Test` returns: `"a"` or `"b"`.
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
abbrev Test.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Test)) (Val #()))
  {{ (r : GoString), RET #r; ⌜goodVal r⌝ }}

end spec

end goose_prophkv
end EtcdGrove
end Perennial
