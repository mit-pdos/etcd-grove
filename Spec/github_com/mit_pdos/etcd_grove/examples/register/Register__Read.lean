/- Lean-first (no Rocq counterpart).

`(*Register).Read()` (register.go:233), a linearizable read by read index (2026-10-13): for a
lower bound `L0` on the register's history at the call (`regLb`, `Defs.lean`; the history
now is one, `regLb_current`), it returns the value after a history `L` that extends `L0`
and is itself a lower bound, so a prefix of the history at the return: the value at a
point between the call and the return. Not logically atomic: which history the value is
of is known only after the fact (when the read state comes back, its read index is in the
past), so the spec is stated with lower bounds, as raft's `ReadState` is (`readOk`).

One operation credit (`Read` takes a sequence number, like an operation) and one read
credit (`rdCred`, what `Node.ReadIndex` takes); a configuration of more than one voter
(`Node.ReadIndex`'s). A request raft drops (no leader known) leaves `Read` waiting: partial
correctness.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Register.Read.spec : Prop :=
  ∀ (γr : RegNames) (γp : RepNames) (r : Loc) (L0 : List (List w8)),
  1 < GMap.size γr.raft.reCfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
      isRegister γr γp r ∗ opCred γp 1 ∗ rdCred γr.raft 1 ∗ regLb γr L0 }}
    (App (Val (r @!! go.GoType.PointerType rRegisterTy @!! go!"Read")) (Val #()))
  {{ (x : List w8), RET #x; ∃ L, regLb γr L ∗ ⌜L0 <+: L ∧ x = regFold L⌝ }}

end spec

end register
end EtcdGrove
end Perennial
