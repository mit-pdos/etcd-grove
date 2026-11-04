/- Lean-first (no Rocq counterpart).

`NewKV()` (`examples/goose/prophkv`): a new, empty map, with the client's half of its abstract state.
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
abbrev NewKV.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.goose.prophkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.goose.prophkv.NewKV)) (Val #()))
  {{ (kv : Loc) (γ : GName), RET #kv; isKV kv γ ∗ kvState γ ∅ }}

end spec

end goose_prophkv
end EtcdGrove
end Perennial
