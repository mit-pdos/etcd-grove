/-
`c.do(kind, key, val)` (kvcheck.go): the operation `encodeOp n kind key val` of a fresh id `n`
(`fresh`: `issued γ false n`), proposed at random members over kvnet's wire protocol until one
answers. The caller's minting law turns the issued id into the operation's fact (`F.opOk`, what a
`ReqPropose`'s payload carries: kvnet's store layer mints the slot, kvdurable's `kd_mint`, after
decision B); the answer `v` comes with its fact (`F.ansOp`, kvdurable's `waitP`). Partial
correctness: an operation no replica ever answers keeps `do` looping.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Net raft_kvnet raft_kvreconf

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev checker.do.spec : Prop :=
  ∀ (F : KvFacts GF) (c : Loc) (γ : CheckerNames) (ls : List GoString) (kind : w8)
    (key val : GoString),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗
      isCheckerP F c γ ls ∗
      (∀ n : w64, issued γ false n ={⊤}=∗ F.opOk (encodeOp n kind key val)) }}
    (App (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty @!! go!"do"))
      (Val #kind)) (Val #key)) (Val #val))
  {{ (v : GoString), RET #v; ∃ n : w64, F.ansOp (encodeOp n kind key val) v }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
