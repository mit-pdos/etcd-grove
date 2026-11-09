/- Lean-first (no Rocq counterpart).

`x.compact(m, o, lead)` (`examples/mvccfull/mvccfull.go`): the log's compaction `o` on member `m`
(as `txn`'s): at or below the member's compaction revision, `ErrCompacted` with a channel (received
from if `o.wait`); past its revision, `ErrFutureRev` and no channel; otherwise `cmpHi` raised first,
`Compact` succeeds (the hook ran under its batch lock: `hookPost`), `m.cmp` and `cmpLo` at the new
compaction revision, the leader records it in the history (`addComp`, `compactions`), and waits if
`o.wait`. Every check passes; afterwards the member is at the model after `v.ops + 1`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.compact.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS)
    (qw qk : Qp) (nw k : Nat) (p : Loc) (o : OpM) (lead : Bool) (a s : w64),
  ops[v.ops]? = some o → o.kind = kCompact → logOk ks ops → ops.length < 2 ^ 38 →
  a = W64 (v.ops + 1 : Int) → sint.Z s < sint.Z a →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ opIs p o ∗
      memCore ks γh ops i mp m f v qw qk nw k ∗ hookPre mp a s ∗ leadPre γh ks ops v.ops lead }}
    (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"compact") (Val #mp)) (Val #p)) (Val #lead))
  {{ RET #(); leadPost γh ks ops v.ops lead ∗ (hookPost mp a ∨ hookPre mp a s) ∗
      ∃ v' : MemS, ⌜MemS.sameInc v v' ∧ v'.ops = v.ops + 1⌝ ∗
        memCore ks γh ops i mp m f v' qw qk nw k }}

end spec

end mvccfull
end EtcdGrove
end Perennial
