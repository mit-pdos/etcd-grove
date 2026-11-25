/- Lean-first (no Rocq counterpart).
`DecOutput(b)` (`examples/etcd/dist/kvremote`): decodes `b`; when it accepts (`ok`), `b`'s bytes were the
encoding (`outputBytes`) of the output it returns, and nothing else.
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
abbrev DecOutput.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗ b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecOutput)) (Val #b))
  {{ (x : Output) (ok : Bool), RET (PairV #x #ok); ⌜ok = true → bs = outputBytes x⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
