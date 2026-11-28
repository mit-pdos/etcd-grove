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

/-! ### Foreign revisions keep the states under a prefix (`kOkD_foreign`'s pure part) -/

theorem runFrom_append' (r0 : Nat) (s : List EtcdKv) :
    ∀ (l m : List (List mvcc.Change)), runFrom r0 s (l ++ m) = runFrom (r0 + l.length) (runFrom r0 s l) m := by
  intro l
  induction l generalizing r0 s with
  | nil => intro m; rfl
  | cons cs l ih =>
    intro m
    simp only [List.cons_append, runFrom, ih, List.length_cons]
    congr 1
    omega

/-- Revisions whose changes are of keys not under `q` keep the key-values under `q`. -/
theorem filter_runFrom_other (q : GoString) :
    ∀ (l : List (List mvcc.Change)) (r0 : Nat) (s : List EtcdKv), (∀ cs ∈ l, ∀ c ∈ cs, ¬ q <+: c.key) →
      (runFrom r0 s l).filter (fun v => decide (q <+: v.key)) = s.filter (fun v => decide (q <+: v.key))
  | [], _, _, _ => rfl
  | cs :: l, r0, s, h => by
    simp only [runFrom]
    rw [filter_runFrom_other q l _ _ (fun cs' hc' => h cs' (List.mem_cons_of_mem _ hc')),
      etcd_dist.filter_applyChanges_other q _ cs (h cs List.mem_cons_self) s]

/-- The states at or below `σl`'s revision are `σl`'s, when `σ`'s changes extend `σl`'s. -/
theorem at_ext_below {σl σ : KVState} {m : List (List mvcc.Change)} (hc : σ.compacted = σl.compacted)
    (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m) (r : Nat) (hr : r ≤ σl.rev) :
    σ.at r = σl.at r := by
  unfold KVState.at
  rw [hc, hb, hm]
  split
  · rfl
  · unfold KVState.rev at hr
    rw [List.take_append_of_le_length (by omega)]

/-- **Above `σl`'s revision, `σ`'s states are `σl`'s current one under `q`**, when the revisions in between
change no key under `q`. -/
theorem at_ext_foreign {σl σ : KVState} {m : List (List mvcc.Change)} (q : GoString)
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ q <+: ch.key) (r : Nat) (hr : σl.rev ≤ r) :
    (σ.at r).kvs.filter (fun v => decide (q <+: v.key)) = σl.kvs.filter (fun v => decide (q <+: v.key)) := by
  have hle : σ.compacted ≤ r := by unfold KVState.rev at hr; omega
  rw [KVState.at_kvs σ r hle, KVState.kvs_eq σl, hc, hb, hm]
  unfold KVState.rev at hr
  rw [List.take_append, List.take_of_length_le (by omega), runFrom_append']
  exact filter_runFrom_other q _ _ _ (fun cs hcs => hf cs (List.mem_of_mem_take hcs))

/-- **A fact of every key-value under `/registry/` at every revision survives foreign revisions.** -/
theorem regAll_foreign (P : EtcdKv → Prop) {σl σ : KVState} {m : List (List mvcc.Change)}
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key)
    (hl : ∀ r ≤ σl.rev, ∀ v ∈ (σl.at r).kvs, regP <+: v.key → P v) :
    ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, regP <+: v.key → P v := by
  intro r _ v hv hp
  by_cases hr : r ≤ σl.rev
  · rw [at_ext_below hc hb hm r hr] at hv
    exact hl r hr v hv hp
  · have he := at_ext_foreign regP hc hb hm hf r (by omega)
    have hv' : v ∈ (σ.at r).kvs.filter (fun v => decide (regP <+: v.key)) :=
      List.mem_filter.2 ⟨hv, by simpa using hp⟩
    rw [he] at hv'
    exact hl σl.rev le_rfl v (List.mem_filter.1 hv').1 hp

theorem keysOkP_foreign {σl σ : KVState} {m : List (List mvcc.Change)}
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) (h : keysOkP σl) : keysOkP σ :=
  regAll_foreign (fun v => v.key ∈ wkKeysL.map mkeyL) hc hb hm hf h

theorem valsOkP_foreign {σl σ : KVState} {m : List (List mvcc.Change)}
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) (h : valsOkP σl) : valsOkP σ :=
  regAll_foreign (fun v => ∀ d, driverCodec.dec v.value = some d → d.1.val.length ≤ 2 ^ 20) hc hb hm hf h

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
