/-
`clientv3.WithPrevKV()` (`client/v3/op.go`, translated since k8s 7f-3a; the etcd3 watcher's watch
option): an option asking for the previous key-value of each event. Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

/-- `WithPrevKV()` -/
def withPrevKVM (o : OpFull) : OpFull := { o with base := { o.base with prevKV := true } }

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithPrevKV()`: an option asking for the previous key-values. -/
abbrev WithPrevKV.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithPrevKV)) (Val #()))
  {{ (f : GoFunc), RET #f; optSpec f withPrevKVM }}

end spec

end EtcdGrove
end Perennial
