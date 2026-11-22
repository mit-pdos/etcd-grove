/-
`c.read(key)` (kvcheck.go): reads of `key` at random members over kvnet's wire protocol, each with a
fresh sequence number (`fresh`: `issued γ true seq`), until one answers. The caller's minting law
(persistent: one use per attempt) turns the issued number, at the replica `id` the attempt asks, into
the read context's fact (`F.readOk id seq key`, what a `ReqRead`'s payload carries: kvnet's store layer
mints it, kvdurable's `kd_mint_next`, after decision B); the answer `v` comes with its fact
(`F.ansRead id seq key v`). Partial correctness: a read no replica ever answers keeps `read` looping.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Net raft_kvnet

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev checker.read.spec : Prop :=
  ∀ (F : KvFacts GF) (c : Loc) (γ : CheckerNames) (ls : List GoString) (key : GoString),
  (key.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗
      isCheckerP F c γ ls ∗
      □ (∀ (id seq : w64), ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ ls.length⌝ -∗
          (issued γ true seq ={⊤}=∗ F.readOk id seq key)) }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty @!! go!"read"))
      (Val #key))
  {{ (v : GoString), RET #v; ∃ id seq : w64, F.ansRead id seq key v }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
