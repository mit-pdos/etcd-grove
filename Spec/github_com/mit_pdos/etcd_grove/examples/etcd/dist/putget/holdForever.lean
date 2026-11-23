/-
`holdForever()` (`examples/etcd/dist/putget/putget.go`): a `time.Sleep` loop that never ends, keeping the
member machine's process alive. Lean-first (no Rocq counterpart).

**The triple:** it never returns (the postcondition `False`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]

/-- See the file header. -/
abbrev holdForever.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.holdForever)) (Val #()))
  {{ RET #(); False }}

end spec

end etcd_putget_dist
end EtcdGrove
end Perennial
