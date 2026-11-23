/-
Lean-first (no Rocq counterpart).

# Kubernetes' checker's `Replay` and `WatchValidator` in the heap (k8s 7g step 5)

The predicates the specs of `correctness/replay.go` and `correctness/watch.go` are written in, over
`RReplay.lean`'s pure functions:

- `opRep v op`: the `correctness.Operation` `v` is the driver's unary operation `op` (its request
  `realRequest(op.1)`, `reqRep`, and a response of view `op.2`, `respRep`; persistent);
- `changeVRep v c`: the `Change` value `v` has the view `c` (its key and resource version, its
  objects read-only);
- `replayAt rp R`: the `*Replay` `rp` holds `R`, frozen (`NewReplay` builds it and nothing writes it
  after): the driver's `NewFunc` and `Versioner`, the states by resource version (each a frozen
  `*Model`, `modelAt`, filed under its own resource version), the changes in order (each with an object or the one
  before it, `chgOk`);
- `listExpOk R x out`: the model's list at a list response's state answers a deep error;
- `opPre x out`, `stepPre x m out` and `ReplayPre init ops`: an operation's own premises, `Model.Step`'s
  at the state `m`, and `Model.Step`'s along `NewReplay`'s loop (every state the replay reaches, for the
  operation it steps).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.EvRep
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ErrViews
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ModelFit

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

/-- **An operation's own premises** (`Model.Step`'s, `Replay.Validate`'s, of the input and the
response only): the input fits, its resource version parses, a list's limit, the response's error
flat, its object a list (or nil) for a list and an object (or nil) for a get. -/
def opPre (x : Input) (out : RResp) : Prop :=
  inFits x ∧ (parseRVD x.MinRV').isSome ∧
  (x.Kind' = W64 4 → 0 ≤ sint.Z x.Limit' ∧ (0 < sint.Z x.Limit' → x.MinRV' ≠ go!"0")) ∧
  flatE out.err ∧ (x.Kind' = W64 4 → listOrNilD out.obj) ∧
  (isWriteL x = false → x.Kind' ≠ W64 4 → objOrNilD out.obj)

/-- **`Model.Step`'s premises** (`Model__Step.lean`) for the operation `(x, out)` at the state `m`:
the state has fewer than `2^62` items, the operation's, the state's items fit, and the model's own response is not `RErr.other`. -/
def stepPre (x : Input) (m : RM) (out : RResp) : Prop :=
  GMap.size m.items < 2 ^ 62 ∧ itemsFitL m ∧ (rexecL x m).1.err ≠ .other ∧ opPre x out

/-- **`Model.Step`'s premises along `NewReplay`'s loop**: each operation's, at the state the replay
of the operations before it reached. -/
def ReplayPre (init : RM) (ops : List (Input × RResp)) : Prop :=
  ∀ (i : Nat) (acc : RM × GMap w64 RM × List RChange) (op : Input × RResp),
    (ops.take i).foldl replayStepL (some (init, {[init.rv := init]}, [])) = some acc →
    ops[i]? = some op → stepPre op.1 acc.1 op.2

/-- **The model's list at the response's state answers a deep error** (`Replay.validateList`'s
premise: `equalListResponse` compares the expected response with `reflect.DeepEqual`, whose spec
covers deep errors only): for a list response at resource version `rv`, the model's own list on
the replay's state at `rv` is neither too large nor an internal error. -/
def listExpOk (R : RReplay) (x : Input) (out : RResp) : Prop :=
  ∀ items rv c r st, out.obj = .list items rv c r → R.states !! rv = some st →
    deepErrE (rlistL x st).err

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]

/-- **The `Operation` `v` is the driver's unary operation `op`** (persistent). -/
def opRep (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (op : Input × RResp) : IProp GF :=
  iprop(reqRep v.Request' op.1 ∗ respRep v.Response' op.2)

instance opRep_persistent (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (op : Input × RResp) : Persistent (opRep (GF := GF) v op) := by
  unfold opRep; infer_instance

/-- **The `Change` value `v` has the view `c`** (persistent). -/
def changeVRep (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change)
    (c : RChange) : IProp GF :=
  iprop(⌜v.Key' = c.key ∧ v.ResourceVersion' = c.rv⌝ ∗ deepRO v.Object' (optObjD c.obj) ∗
    deepRO v.PrevObject' (optObjD c.prev))

instance changeVRep_persistent (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change)
    (c : RChange) : Persistent (changeVRep (GF := GF) v c) := by
  unfold changeVRep; infer_instance

/-- **The `*Replay` `rp` holds `R`**, frozen (see the file header). -/
def replayAt (rp : Loc) (R : RReplay) : IProp GF :=
  iprop(isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
    ∃ (sm : Loc) (M : GMap w64 Loc) (csl : GoSlice)
      (cvs : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change),
    rp ↦□ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay.mk newFuncV versionerV
      sm csl ∗
    sm ↦${DFrac.discard} M ∗ ⌜∀ rv, (M !! rv).isSome = (R.states !! rv).isSome⌝ ∗
    ⌜∀ rv m, R.states !! rv = some m → m.rv = rv⌝ ∗ ⌜∀ c ∈ R.changes, chgOk c⌝ ∗
    ([∗map] rv ↦ mp ∈ M, ∃ m, ⌜R.states !! rv = some m⌝ ∗ modelAt mp m) ∗
    csl ↦*□ cvs ∗ [∗list] cv;c ∈ cvs;R.changes, changeVRep cv c)

instance replayAt_persistent (rp : Loc) (R : RReplay) : Persistent (replayAt (GF := GF) rp R) := by
  unfold replayAt; infer_instance

end defs

end k8s_correctness
end EtcdGrove
end Perennial
