/-
`clientErr`: what an error etcd's client returns is, as Go's `errors.As` needs it (moved from
`cache/v3/InvEtcdTxnOwn.lean` in unit C1, 2026-10-14, so that `rpctypes.Error`'s spec, which
imports less, can state that it keeps it). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.errors
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.api.v3

section clientErr
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- **An error etcd's client returns** (a gRPC status error, an `rpctypes.EtcdError`, a context
error): a leaf of an error tree, without `Unwrap` or `As` methods (`errors.isLeafError`), whose
value, if its dynamic type is `rpctypes.EtcdError`, is an `EtcdError` (Go's typing, which the model
lacks: `errors.AsTypeTyped`); and `rpctypes.EtcdError` implements `error` (its method set has
`Error() string`, `func (e EtcdError) Error() string`: `errors.AsTarget`, a method-set fact, which
the model also lacks, since method sets are uninterpreted). What `errors.As(err, &serverErr)`
needs (`leasingKV.acquire`, `errors.wp_As`: Go's `As` panics for a target whose element type is
neither an interface nor implements `error`). -/
def clientErr (err : GoInterface) : Prop :=
  errors.AsTarget v3rpc.rpctypes.EtcdError.ty ∧
  ∀ ii, err = GoInterface.ok ii → errors.isLeafError ii ∧
    errors.AsTypeTyped v3rpc.rpctypes.EtcdError v3rpc.rpctypes.EtcdError.ty ii

end clientErr

end EtcdGrove
end Perennial
