/-
`concurrency.stmSerializable.gets()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.gets()`: the read keys (in the map's order) and, for each, the get `OpGet(k)`
(`keyOp k`). -/
abbrev stmSerializable.gets.spec : Prop :=
  ∀ (p : Loc) (pfx : GoString) (reads : GMap GoString ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmRsetOwn pfx (structFieldRef stmSerializable go!"stm" p) reads }}
    (App (Val (p @!! go.GoType.PointerType stmSerializable.ty @!! go!"gets")) (Val #()))
  {{ (ksl osl : GoSlice), RET (PairV #ksl #osl);
      stmRsetOwn pfx (structFieldRef stmSerializable go!"stm" p) reads ∗
      ∃ ks : List GoString, ksl ↦*□ ks ∗ opsAt osl (ks.map keyOp) ∗ ⌜MapKeysList reads ks⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
