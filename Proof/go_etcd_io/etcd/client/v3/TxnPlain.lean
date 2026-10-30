/-
`Then` and `Else` at plain operations (`notes/txn-nested.md`, S1′): the specs until the nested
generalization (`txn.Then.specPlain`, `txn.Else.specPlain`), corollaries of the one proof of each
(`txn.Then.spec_plain`), and their linked instances (`v3.txn.wp_Then_plain`, `v3.txn.wp_Else_plain`)
for the callers whose operations are all plain. Not a linking file: it imports `Link` and no
`Link.lean` imports it, so the instances are not second proofs of `Then`/`Else`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `txn.Then.spec` at plain operations (the statement until the nested generalization;
`txn.Then.spec_plain`, `Proof/go_etcd_io/etcd/client/v3/TxnPlain.lean`). -/
abbrev txn.Then.specPlain : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.cthen = false ∧ b.celse = false⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then")) (Val #sl))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
      txnObjAt tp addr ci cd { b with model := { b.model with thenOps := b.model.thenOps ++ ops }, cthen := true } }}

/-- `txn.Else.spec` at plain operations (the statement until the nested generalization;
`txn.Else.spec_plain`, `Proof/go_etcd_io/etcd/client/v3/TxnPlain.lean`). -/
abbrev txn.Else.specPlain : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.celse = false⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Else")) (Val #sl))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
      txnObjAt tp addr ci cd { b with model := { b.model with elseOps := b.model.elseOps ++ ops }, celse := true } }}

/-- `Then` at plain operations, from its spec (by `opsAt_leaves`, `txnOps_leaves`). -/
theorem txn.Then.spec_plain (h : txn.Then.spec (GF := GF) (hG := hG)) :
    txn.Then.specPlain (GF := GF) (hG := hG) := by
  sorry -- txn-nested: prove after freeze

/-- `Else` at plain operations, from its spec (by `opsAt_leaves`, `txnOps_leaves`). -/
theorem txn.Else.spec_plain (h : txn.Else.spec (GF := GF) (hG := hG)) :
    txn.Else.specPlain (GF := GF) (hG := hG) := by
  sorry -- txn-nested: prove after freeze

end spec

namespace client

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `Then`'s linked result at plain operations. -/
theorem v3.txn.wp_Then_plain : EtcdGrove.txn.Then.specPlain (GF := GF) (hG := hG) :=
  EtcdGrove.txn.Then.spec_plain v3.txn.wp_Then

/-- `Else`'s linked result at plain operations. -/
theorem v3.txn.wp_Else_plain : EtcdGrove.txn.Else.specPlain (GF := GF) (hG := hG) :=
  EtcdGrove.txn.Else.spec_plain v3.txn.wp_Else

end links

end client

end EtcdGrove
end Perennial
