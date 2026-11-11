/- Lean-first (no Rocq counterpart).

`x.readOne(m)` (`examples/mvccfull/mvccfull.go`): one read on member `m` (the `i`-th of the run's
members, `mp0` the leader, `mp1` the follower) concurrent with the writer, every check passing:
`Rev`, `FirstRev`, a read transaction (its revision, compaction revision, and one to three ranges),
a read-only transaction (likewise, one range, no changes), or the store's own `Range`
(`checkStoreRange`); each revision in `[revLo, revHi]` and each compaction revision in
`[cmpLo, cmpHi]` loaded around it, each range's result the history's (`checkRangeAt`).

**F1's scope**: the read mix `wr` (`x.cfg.Mix.Read`) meets `readMixOk`, so `pick` never chooses
the corruption checker's hashes (`x.hashes()`, alternative `5`: F2).

**The triple.** The reader goroutine's part of the epoch (`rdOwn`: a reader slot of the history;
for each member, its current incarnation's handles, one reader token, a share of the retirement
token and of the `kv` field; both members, since F2's hashes read both), the incarnations' handles,
and the run's read-only fields it reads (`runnerKeys`, `runnerH`, `runnerCfg`); all given back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

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

/-- See the file header. -/
abbrev runner.readOne.spec : Prop :=
  ∀ (x : Loc) (cfg : Config) (wr : List w64) (ks : List GoString) (h : Loc) (γ : FullNames)
    (mp0 mp1 : Loc) (e0 e1 : IncNames × GoInterface) (q : Qp) (i : Nat) (mp : Loc),
  readMixOk (wr.map sint.Z) → [mp0, mp1][i]? = some mp →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
      runnerKeys x ks ∗ runnerH x h ∗ runnerCfg x cfg wr ∗
      rdOwn ks h γ mp0 mp1 e0 e1 q }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"readOne") (Val #mp))
  {{ RET #(); rdOwn ks h γ mp0 mp1 e0 e1 q }}

end spec

end mvccfull
end EtcdGrove
end Perennial
