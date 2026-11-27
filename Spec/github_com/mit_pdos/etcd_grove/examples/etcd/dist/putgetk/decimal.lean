/-
`decimal(s)` (`examples/etcd/dist/putgetk/putgetk.go`): `s` read as a decimal number with no leading zero
(at most 5 digits). Lean-first (no Rocq counterpart).

**The triple:** it returns (no claim on the values: `AddrOK`'s callers need none).
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
abbrev decimal.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.decimal)) (Val #s))
  {{ (n : w64) (ok : Bool), RET (PairV #n #ok); True }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
