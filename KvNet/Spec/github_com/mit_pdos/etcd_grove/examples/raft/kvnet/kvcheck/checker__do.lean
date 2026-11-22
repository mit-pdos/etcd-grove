/-
`c.do(kind, key, val)` (kvcheck.go), at kvnet's store (`kvFacts γ cf`, the checker's counters `kvCnt γ n`
with `n` its replicas: `StoreDefs.lean`): one operation, logically atomic (kvdurable's `Cluster.do`):
a fresh id from the checker (`nextOp` under `c.mu`, which mints the operation's datum at the store's op
counter, its slot holding the caller's atomic update: `kd_mint`), proposed at random members over kvnet's
wire protocol until one answers. The update takes effect when the datum's first entry commits; `do`
returns the key's value after it. Partial correctness: an operation no replica ever answers keeps `do`
looping.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.StoreDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open raft_kvreconf (KVMap kvNext)
open Iris Iris.BI Net raft_kvnet

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions] [go.IntoValInj GoString]
variable [kvnet_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev checker.do.spec : Prop :=
  ∀ (γ : KdNames) (cf : List w8 → Prop) (c : Loc) (ls : List GoString) (kind : w8)
    (key val : GoString) (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ∗
      isCheckerP (kvFacts γ cf) c (kvCnt γ ls.length) ls ∗ rkvInv γ ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γ x }> @ kdMask, ∅
        <{ rkvVal γ (kvNext kind key val x), COMM Φ (kvNext kind key val x key) }> }}
    (App (App (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker.ty @!! go!"do"))
      (Val #kind)) (Val #key)) (Val #val))
  {{ (v : GoString), RET #v; Φ v }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
