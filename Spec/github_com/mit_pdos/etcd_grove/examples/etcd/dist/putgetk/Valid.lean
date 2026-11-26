/-
`Valid(peers, clients)` (`examples/etcd/dist/putgetk/putgetk.go`): whether the configuration is one etcd
can run. Lean-first (no Rocq counterpart).

**The triple:** it returns `b`, and `b = true` only if the configuration is `cfgOk` (a member, the lists of
one length, the member ids' 16 low bits distinct and not `0`); the slices are only read. The converse (and
the addresses' checks) is tested (`TestValidSeeds`), not claimed: a caller needs only this direction.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs
public import Perennial.TrustedCode.crypto.fips140

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
abbrev Valid.spec : Prop :=
  ∀ (peersSl clientsSl : GoSlice) (peers clients : List GoString) (dq₁ dq₂ : DFrac),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk ∗ peersSl ↦*{dq₁} peers ∗ clientsSl ↦*{dq₂} clients }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Valid)) (Val #peersSl)) (Val #clientsSl))
  {{ (b : Bool), RET #b; ⌜b = true → cfgOk peers clients⌝ ∗ peersSl ↦*{dq₁} peers ∗
      clientsSl ↦*{dq₂} clients }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
