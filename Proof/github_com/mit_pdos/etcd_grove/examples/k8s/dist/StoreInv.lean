/-
Lean-first (no Rocq counterpart).

# k8s-dist K8-3: the store's invariant over the shared KV (`kInvD`), started

`notes/k8s-dist-k8-scope.md` §1. The in-process store's invariant (`etcd3/Inv.lean`, `kInvBody`) holds etcd's
whole client half `etcdKV γk σ`; on the shared cluster the store owns only the prefix `/registry/`
(`KVPfxHist`'s share: half of the ghost variable at `pfxVH regP σ`), and other writers take revisions in
between. Here:

- `KOkD`: `KOk` with the model state closed under the semantic model's silent steps (`FClosed`, foreign
  revisions included, `SharedPend.lean`), and the workload's keys and values only under `/registry/`
  (`keysOkP`/`valsOkP`: other writers' keys are anything);
- `KHistID`/`revOwnD`: `KHistI`/`revOwn` with one change per revision **under `/registry/`** only;
- `kOkD_foreign.law`: the statement of the catch-up over foreign revisions (proof: next step);
- `kInvDBody`/`kInvD`: the owner's invariant, `KVPfxHist`'s `∃ v, ghostVar γs ½ v ∗ W v` with `W` =
  `kInvBody` at "the last state `σl` the store saw", `v = pfxVH regP σl`, and the lintest ghost over `pMF`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedPend
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Inv
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPfxHist

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s k8s_etcd3
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

/-- The prefix the store owns in the shared KV. -/
abbrev regP : GoString := go!"/registry/"

section pure
variable [GooseExts]

/-- **The workload's keys, under `/registry/`**: every key under it, at every revision, is a workload
key (`keysOk` restricted to the owned prefix). -/
def keysOkP (σ : KVState) : Prop :=
  ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, regP <+: v.key → v.key ∈ wkKeysL.map mkeyL

/-- **The workload's values, under `/registry/`** (`valsOk` restricted to the owned prefix). -/
def valsOkP (σ : KVState) : Prop :=
  ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, regP <+: v.key →
    ∀ d, driverCodec.dec v.value = some d → d.1.val.length ≤ 2 ^ 20

/-- One change per revision under `/registry/`. -/
def OneChangeP (σ : KVState) : Prop :=
  ∀ cs ∈ σ.changes, (cs.filter (fun ch => decide (regP <+: ch.key))).length ≤ 1

/-- **etcd's history facts the watches need, on the shared KV**: `KHistI` with one change per revision
under `/registry/` only. -/
def KHistID (γ : KNames) (σ : KVState) : Prop :=
  σ.compacted = 0 ∧ σ.base = γ.b0 ∧ OneChangeP σ ∧ 1 ≤ σ.rev

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The store's relation on the shared KV** (`KOk`'s fields; see the file header). -/
structure KOkD (c : StoreCfg GF DObj) (g0 : HSt) (S : linkv.PSet HSt Input) (σ : KVState)
    (M : GMap Nat Input) (nx : Nat) : Prop where
  closed : FClosed g0 S
  wf : kvWf c σ
  hwf : kvWfHist c σ
  keys : keysOkP σ
  vals : valsOkP σ
  fresh : ∀ n, nx ≤ n → M !! n = none
  ins : ∀ n i, M !! n = some i → InOk i ∧ isWriteL i = true ∧ i.Val'.length ≤ 2 ^ 20
  cfg : ∃ cf, S cf ∧ KRelH cf.st σ ∧ cf.st.hist.length = σ.rev ∧ (pendIns M).Perm cf.pend

/-- **The catch-up over foreign revisions** (the statement; K8-3's next proof): the store last saw `σl`,
the share's firing hands it `σ`, whose changes extend `σl`'s by revisions with no change under
`/registry/` (`pfxChs_same_ext` of equal `pfxVH regP`); `σ` is well formed for the store and leaves room
for one more revision. The relation holds at `σ`, the model state unchanged: the configuration related to
`σl` takes `σ.rev - σl.rev` foreign steps (`FClosed.foreign`), each appending the unchanged store. -/
abbrev kOkD_foreign.law (c : StoreCfg GF DObj) (g0 : HSt) : Prop :=
  ∀ (S : linkv.PSet HSt Input) (σl σ : KVState) (M : GMap Nat Input) (nx : Nat)
    (m : List (List mvcc.Change)),
    CfgD c → KOkD c g0 S σl M nx →
    σ.compacted = σl.compacted → σ.base = σl.base → σ.changes = σl.changes ++ m →
    (∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) →
    kvWf c σ → kvWfHist c σ → σ.rev + 1 < 2 ^ 63 →
    KOkD c g0 S σ M nx

/-- **The revisions' states on the shared KV** (`revOwn` with `KHistID`). -/
def revOwnD (γ : KNames) (σ : KVState) : IProp GF :=
  iprop(∃ Mr : GMap Nat KVState, ghostMapAuth γ.r 1 Mr ∗
    ghostMapElem γ.r σ.rev DFrac.discard σ ∗ ⌜RevOk Mr σ⌝ ∗
    monoListAuthOwn γ.ch 1 σ.changes ∗ ⌜KHistID γ σ⌝)

instance revOwnD_timeless (γ : KNames) (σ : KVState) : Timeless (revOwnD (GF := GF) γ σ) := by
  unfold revOwnD; infer_instance

/-- **The store's half of the invariant at the last state `σl` it saw** (`kInvBody` without etcd's client
half): the lintest ghost history `h` over `pMF`, the pending writes, the revisions' states, the store's
history, and the relation; `σl` extends the share's start `σ₀`. -/
def kInvDW (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (σ₀ σl : KVState) : IProp GF :=
  iprop(∃ (h : List OpV) (S : linkv.PSet HSt Input) (M : GMap Nat Input) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ ghostMapAuth γ.p 1 M ∗ revOwnD γ σl ∗ shistOwn c σl ∗
    ⌜etcd_dist.KVExt σ₀ σl ∧ run (pMF g0 decOp) (fInit g0) h = some S ∧ KOkD c g0 S σl M nx⌝)

/-- The invariant's contents: the prefix's ghost half `γs` at `pfxVH regP σl`, and the store's half at `σl`. -/
def kInvDBody (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γs : GName) (σ₀ : KVState) : IProp GF :=
  iprop(∃ σl : KVState, ghostVar γs (1 : Qp).half (etcd_dist.pfxVH regP σl) ∗ kInvDW γ c g0 σ₀ σl)

/-- The invariant's namespace. -/
def drvDInvN : Namespace := client.kvClientN .@ "k8s"

/-- **The store's invariant on the shared KV.** -/
def kInvD (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γs : GName) (σ₀ : KVState) : IProp GF :=
  iprop(inv drvDInvN (kInvDBody γ c g0 γs σ₀))

instance kInvD_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γs : GName) (σ₀ : KVState) :
    Persistent (kInvD (GF := GF) γ c g0 γs σ₀) := by
  unfold kInvD; infer_instance

end defs

end k8s_dist
end EtcdGrove
end Perennial
