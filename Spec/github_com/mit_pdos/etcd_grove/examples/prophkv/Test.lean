/- Lean-first (no Rocq counterpart).

`Test()` (`examples/prophkv`): a `Put` of `"k"` with `"a"`, then a goroutine's `Put` of `"b"`
concurrent with a `GetAny` of `"k"`, whose answer `Test` returns: `"a"` or `"b"`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.prophkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- See the file header. -/
abbrev Test.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.prophkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.prophkv.Test)) (Val #()))
  {{ (r : GoString), RET #r; ⌜goodVal r⌝ }}

end spec

end prophkv
end EtcdGrove
end Perennial
