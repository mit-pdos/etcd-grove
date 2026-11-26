/- Lean-first (no Rocq counterpart).
`EncOutput(x)` (`examples/etcd/dist/kvremote`): a new slice of an output's encoding (`outputBytes`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

/-- See the file header. -/
abbrev EncOutput.spec : Prop :=
  ∀ (x : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncOutput)) (Val #x))
  {{ (b : GoSlice), RET #b; b ↦* outputBytes x }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
