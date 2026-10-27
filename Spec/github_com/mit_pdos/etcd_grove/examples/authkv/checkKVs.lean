/-
`checkKVs(who, kvs)` (`examples/authkv/authkv.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `checkKVs(who, kvs)` returns (does not panic) when the key-values `kvs` holds (`txn.kvsIs`,
read-only, as a reply's) are all of keys `who` may read (`permittedK`). -/
abbrev checkKVs.spec : Prop :=
  ∀ (who : GoString) (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
  (∀ kv ∈ kvs, permittedK who kv.key) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      sl ↦*□ ps ∗ txn.kvsIs ps kvs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.checkKVs)) (Val #who))
      (Val #sl))
  {{ RET #(); True }}

end spec

end authkv
end EtcdGrove
end Perennial
