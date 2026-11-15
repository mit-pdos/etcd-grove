/-
`pruneKVs(rr, isPrunable)` (`range.go`), internal (`filterRangeResults`): mirrors the code (an
in-place filter; the dropped key-values' ownership is lost). Old spec: same.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `pruneKVs(rr, f)`, `f` deciding `P` of each key-value with the resource `R`: the key-values `f`
rejects remain, in order. -/
def pruneKVs.spec : Prop :=
  ∀ (rr : Loc) (f : GoFunc) (kvs : List KV) (rev c : Nat) (P : KV → Bool) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ rrOwn rr kvs rev c ∗ R ∗
      (∀ (p : Loc) (kv : KV),
        {{ R ∗ keyValueOwn p (DFrac.own 1) (KeyValueM.ofKV kv) ∗ ⌜kvFits kv⌝ }}
          (App (Val #f) (Val #p))
        {{ (b : Bool), RET #b; R ∗ keyValueOwn p (DFrac.own 1) (KeyValueM.ofKV kv) ∗ ⌜b = P kv⌝ }}) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.pruneKVs)) (Val #rr)) (Val #f))
  {{ RET #(); R ∗ rrOwn rr (kvs.filter (fun kv => !P kv)) rev c }}

end spec
end Txn
end EtcdGrove
end Perennial
