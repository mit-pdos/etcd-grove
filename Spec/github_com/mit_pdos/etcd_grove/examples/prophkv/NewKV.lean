/- Lean-first (no Rocq counterpart).

`NewKV()` (`examples/prophkv`): a new, empty map, with the client's half of its abstract state.
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
abbrev NewKV.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.prophkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.prophkv.NewKV)) (Val #()))
  {{ (kv : Loc) (γ : GName), RET #kv; isKV kv γ ∗ kvState γ ∅ }}

end spec

end prophkv
end EtcdGrove
end Perennial
