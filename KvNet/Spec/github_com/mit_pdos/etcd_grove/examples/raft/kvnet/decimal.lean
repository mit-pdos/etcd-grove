/-
`decimal(s, max)` (addrs.go): `(n, true)` for the value `n` of `s` as a canonical decimal numeral
of at most five digits, at most `max` (`decimalM`); otherwise `false`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Addrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev decimal.spec : Prop :=
  ∀ (s : GoString) (mx : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.decimal)) (Val #s)) (Val #mx))
  {{ (n : w64) (ok : Bool), RET (PairV #n #ok);
      ⌜(if ok then some (uint.nat n) else none) = decimalM s (uint.nat mx)⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
