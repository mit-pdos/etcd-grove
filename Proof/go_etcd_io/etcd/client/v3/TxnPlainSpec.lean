/-
`Then` and `Else` at plain operations (`notes/txn-nested.md`, S1′): the specs until the nested
generalization (`txn.Then.specPlain`, `txn.Else.specPlain`) and their corollaries of the one proof of
each (`txn.Then.spec_plain`); `TxnPlain.lean` has their linked instances. (Split out of
`TxnPlain.lean` for the import tiers, 2026-11-18: a proof whose operations are all plain takes
`txn.Then.spec`/`txn.Else.spec` and applies `spec_plain`.) Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder
public import Spec.go_etcd_io.etcd.client.v3.txn__Then
public import Spec.go_etcd_io.etcd.client.v3.txn__Else

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

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
  intro tp addr ci cd b sl os ops
  iintro %Φ ⟨#Hpkg, Htx, #Hos, %Hb⟩ HΦ
  ihave #HosT := opsAt_leaves sl os ops Hb.1 $$ Hos
  iapply (h tp addr ci cd b sl (os.map OpT.leaf) ops) $$ [Htx] HΦ
  iframe #; iframe; ipureintro; exact ⟨txnOps_leaves os ops Hb.1, Hb.2.1, Hb.2.2⟩

/-- `Else` at plain operations, from its spec (by `opsAt_leaves`, `txnOps_leaves`). -/
theorem txn.Else.spec_plain (h : txn.Else.spec (GF := GF) (hG := hG)) :
    txn.Else.specPlain (GF := GF) (hG := hG) := by
  intro tp addr ci cd b sl os ops
  iintro %Φ ⟨#Hpkg, Htx, #Hos, %Hb⟩ HΦ
  ihave #HosT := opsAt_leaves sl os ops Hb.1 $$ Hos
  iapply (h tp addr ci cd b sl (os.map OpT.leaf) ops) $$ [Htx] HΦ
  iframe #; iframe; ipureintro; exact ⟨txnOps_leaves os ops Hb.1, Hb.2⟩

end spec

end EtcdGrove
end Perennial
