/-
Lean-first (no Rocq counterpart).

# The checker's watch requests (k8s 7g step 5)

`realCheck` gives the validator the driver's watch `x` as `WatchRequest{Key: in.WKey, Options:
watchOptions(in)}`:

- `wreqRep req x`: the request `req` is that one (its `SendInitialEvents` a frozen cell, `sendInitIs`;
  persistent);
- `wInPre x`: what `checkWatch` needs not to panic and to accept, and what the validator's range
  computation needs (B5's `hreq`): the key one `PrepareKey` takes, no limit (`checkWatch` panics on
  pagination; the driver's watches never set one), the resource version parsed below
  `2^63`, the match and initial-events options as the driver draws them (`WatchInOk`), a watch-list
  asking for bookmarks, any other watch either `SendInitialEvents = false` or from a positive revision
  (not the legacy initial events).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ReplayRep
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section pure
variable [GooseExts]

/-- **The driver's watch as `checkWatch` accepts it** (see the file header). -/
def wInPre (x : Input) : Prop :=
  (k8s.prepareKeyM [] x.WKey' x.Recursive').isSome ∧ x.Limit' = 0 ∧
  ∃ n, parseRVD x.MinRV' = some n ∧ uint.nat n < 2 ^ 63 ∧ WatchInOk x (uint.nat n) ∧
    (x.SendInit' = W64 2 → x.Bookmarks' = true) ∧
    (x.SendInit' ≠ W64 2 → x.SendInit' = W64 1 ∨ 0 < uint.nat n)

end pure

section vals
variable [GooseExts] [GoLocalContext] [GoSemanticsFunctions] [GoGlobalContext]

/-- **The validator `realCheck` builds** over the replay at `rp` (`NewWatchValidator(versioner{},
replay, keyFunc)`). -/
abbrev validatorV (rp : Loc) : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchValidator :=
  ⟨versionerV, functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyFunc [], rp⟩

end vals

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **The checker's request of the driver's watch `x`** (see the file header; persistent). -/
def wreqRep (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest)
    (x : Input) : IProp GF :=
  iprop(∃ p : Loc, ⌜req = ⟨x.WKey', watchOptsV x p⟩⌝ ∗ k8s.sendInitIs p (sieOfL x))

instance wreqRep_persistent
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest) (x : Input) :
    Persistent (wreqRep (GF := GF) req x) := by
  unfold wreqRep; infer_instance

end defs

end k8s_correctness
end EtcdGrove
end Perennial
