/-
`concurrency.stmSerializable.Rev(key)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.Rev(k)` (a `*stmSerializable`): `Get(k)`, then the embedded `stm`'s `Rev(k)` (`RevPost`). A
client error aborts it (`stmRet`). -/
abbrev stmSerializable.Rev.spec : Prop :=
  ∀ (lvl : w64) (p : Loc) (pfx : GoString) (st : STMSt) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmState lvl pfx p st ∗ ⌜isoSer lvl = true ∧ pfx <+: k⌝ }}
    (App (Val (p @!! go.GoType.PointerType stmSerializable.ty @!! go!"Rev")) (Val #k))
  {{ (r : val), RET r; stmRet r fun rev : w64 => iprop(
      ∃ st' : STMSt, stmState lvl pfx p st' ∗ ⌜RevPost k st rev st'⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
