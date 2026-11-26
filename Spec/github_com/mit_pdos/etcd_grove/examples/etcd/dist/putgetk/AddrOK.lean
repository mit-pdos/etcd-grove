/-
`AddrOK(a)` (`examples/etcd/dist/putgetk/putgetk.go`): whether `a` is a valid address (the net extension's
`addrOk`). Lean-first (no Rocq counterpart).

**The triple:** it returns; `false` for the empty string (what `Client` needs: its endpoint is `""` only
when the configuration has no client address, and then the start gives it no share). That it is `addrOk`
is tested (`TestAddrOK`), not claimed: no caller needs it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

/-- See the file header. -/
abbrev AddrOK.spec : Prop :=
  ∀ (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AddrOK)) (Val #a))
  {{ (b : Bool), RET #b; ⌜a = [] → b = false⌝ }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
