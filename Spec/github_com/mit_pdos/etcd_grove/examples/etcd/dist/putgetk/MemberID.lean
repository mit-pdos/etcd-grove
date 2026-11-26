/-
`MemberID(peer)` (`examples/etcd/dist/putgetk/putgetk.go`): etcd's id of the member whose one peer URL is
`http://peer` in the cluster `Token`. Lean-first (no Rocq counterpart).

**The triple:** it returns `memberIdOf peer` (`putgetk/Defs.lean`), when the `fips140` GODEBUG setting is
unset or `off` (`crypto/sha1.Sum`'s premise).
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
abbrev MemberID.spec : Prop :=
  ∀ (peer : GoString),
  crypto.fips140.GodebugFips140Off →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.MemberID)) (Val #peer))
  {{ RET #(memberIdOf peer); True }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
