/-
`concurrency.NewSTM(c, apply, opts...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`NewSTM(c, apply, opts...)`**, for a client answering for the prefix `pfx`
(`isEtcdSTMClient`), a closure `apply` (`applySpec`: `nil` means its attempt satisfies `Q`), options
with transformers `os` giving a supported level and keys under `pfx` to prefetch, knowing etcd
has reached `lo`: an error, or `nil` with a committed attempt `st`, `Q st` and `stmOutcome` at the
options' level (`stmResult`). -/
abbrev NewSTM.spec : Prop :=
  ∀ (c : Loc) (pfx : GoString) (apply : GoFunc) (Q : STMSt → Prop) (sl : GoSlice)
    (os : List (STMOpts → STMOpts)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdSTMClient c pfx ∗ applySpec pfx apply Q ∗ stmOptsAt sl os ∗ etcdReached lo ∗
      ⌜isoValid (stmOptsFold os STMOpts.init).iso ∧
        ∀ k ∈ (stmOptsFold os STMOpts.init).prefetch, pfx <+: k⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSTM)) (Val #c)) (Val #apply))
      (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      stmResult pfx (stmOptsFold os STMOpts.init).iso lo Q resp err }}

end spec

end concurrency
end EtcdGrove
end Perennial
