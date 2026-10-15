/-
`concurrency.mkSTM(c, opts)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `mkSTM(c, opts)`, for a supported level: the STM of that level (a `*stmSerializable` for the
serializable levels, a `*stm` otherwise) with its client and the options' context, its methods'
triples, before its first `reset` (`stmStale`). -/
abbrev mkSTM.spec : Prop :=
  ∀ (c : Loc) (pfx : GoString) (op : Loc) (ov : stmOptions) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isEtcdSTMClient c pfx ∗ op ↦□ ov ∗ context.isContext ctx cs ∗
      ⌜ov.ctx' = GoInterface.ok ctx ∧ isoValid ov.iso'⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.mkSTM)) (Val #c)) (Val #op))
  {{ (s : GoInterface), RET #s; ∃ p : Loc, ⌜s = GoInterface.ok (stmIface ov.iso' p)⌝ ∗
      stmMethods ov.iso' pfx p ∗ stmStale ov.iso' pfx p }}

end spec

end concurrency
end EtcdGrove
end Perennial
