/- Lean-first (no Rocq counterpart); the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`).

`withTimeout(d)` (cluster.go): `context.WithCancel(context.Background())`, with a timer
(`time.AfterFunc(d, cancel)`) that cancels it after `d`: kvdurable's `context.WithTimeout(
context.Background(), d)` without the deadline, which `WithTimeout` computes from `time.Now`.
Stated as `context.WithTimeoutBackground.spec` (`Spec/context/WithTimeoutBackground.lean`), which its
callers used: a context of some descriptor whose values are `Background()`'s, and its `cancel`,
callable from anywhere.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev withTimeout.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.withTimeout)) (Val #d))
  {{ (ctx' : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      context.isContext ctx' cd ∗ _root_.Perennial.context.ctxValueFrom context.backgroundCtxVal ctx' }}

end spec

end kvraft
end EtcdGrove
end Perennial
