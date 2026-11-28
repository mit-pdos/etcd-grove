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
    exact hl σl.rev (Nat.le_refl _) v (List.mem_filter.1 hv').1 hp

theorem keysOkP_foreign {σl σ : KVState} {m : List (List mvcc.Change)}
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) (h : keysOkP σl) : keysOkP σ :=
  regAll_foreign (fun v => v.key ∈ wkKeysL.map mkeyL) hc hb hm hf h

theorem valsOkP_foreign {σl σ : KVState} {m : List (List mvcc.Change)}
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) (h : valsOkP σl) : valsOkP σ :=
  regAll_foreign (fun v => ∀ d, driverCodec.dec v.value = some d → d.1.val.length ≤ 2 ^ 20) hc hb hm hf h


/-! ### `KRelH` at foreign revisions -/

theorem regP_kpfxD : regP <+: kpfxD := ⟨go!"objs", rfl⟩

theorem regP_mkeyL (n : GoString) : regP <+: mkeyL n :=
  regP_kpfxD.trans ⟨go!"/" ++ n, rfl⟩

theorem findKey_filter_of (p : EtcdKv → Bool) (k : GoString) (h : ∀ v : EtcdKv, v.key = k → p v = true) :
    ∀ s : List EtcdKv, mvcc.findKey k (s.filter p) = mvcc.findKey k s
  | [] => rfl
  | v :: s => by
    have ih := findKey_filter_of p k h s
    unfold mvcc.findKey at ih ⊢
    by_cases hv : v.key = k
    · rw [List.filter_cons_of_pos (h v hv)]; simp [hv]
    · by_cases hp : p v = true
      · rw [List.filter_cons_of_pos hp]; simp [hv, ih]
      · rw [List.filter_cons_of_neg hp]; simp [hv, ih]

/-- **`KRelS` reads only the key-values under `/registry/`**: a store with the same ones is related to
the same items, at any revision. -/
theorem krelS_foreign {s s' : KVStore} {r : Nat} {g : GSt} (r' : Nat) (h : KRelS s r g)
    (he : s'.kvs.filter (fun v => decide (regP <+: v.key)) = s.kvs.filter (fun v => decide (regP <+: v.key))) :
    KRelS s' r' ⟨g.items, W64 (r' : Int)⟩ := by
  refine ⟨h.1, rfl, fun n => ?_⟩
  have hk : ∀ t : KVStore, mvcc.findKey (mkeyL n) t.kvs =
      mvcc.findKey (mkeyL n) (t.kvs.filter (fun v => decide (regP <+: v.key))) := fun t =>
    (findKey_filter_of _ _ (fun v hv => by rw [hv]; simpa using regP_mkeyL n) t.kvs).symm
  have := h.2.2 n
  rw [absK_mkeyL] at this ⊢
  rw [hk s', he, ← hk s]
  exact this

/-- Two states with the same compaction, base and changes have the same revisions. -/
theorem at_congr {σ σ' : KVState} (hc : σ'.compacted = σ.compacted) (hb : σ'.base = σ.base)
    (hch : σ'.changes = σ.changes) : σ'.rev = σ.rev ∧ ∀ r, σ'.at r = σ.at r := by
  refine ⟨by unfold KVState.rev; rw [hc, hch], fun r => ?_⟩
  unfold KVState.at; rw [hc, hb, hch]

theorem krelH_congr {h : HSt} {σ σ' : KVState} (hc : σ'.compacted = σ.compacted) (hb : σ'.base = σ.base)
    (hch : σ'.changes = σ.changes) (H : KRelH h σ) : KRelH h σ' := by
  obtain ⟨er, ea⟩ := at_congr hc hb hch
  simpa only [KRelH, KVState.store, er, ea] using H

/-- One more revision: its rev and current key-values. -/
theorem kvs_snoc {σa σb : KVState} {cs : List mvcc.Change} (hc : σb.compacted = σa.compacted)
    (hb : σb.base = σa.base) (hm : σb.changes = σa.changes ++ [cs]) :
    σb.rev = σa.rev + 1 ∧ σb.kvs = mvcc.applyChanges (W64 ((σa.rev + 1 : Nat) : Int)) σa.kvs cs := by
  refine ⟨by unfold KVState.rev; rw [hc, hm, List.length_append]; simp; omega, ?_⟩
  rw [KVState.kvs_eq, KVState.kvs_eq σa, hc, hb, hm, runFrom_append]
  rfl

/-- **One foreign revision**: the configuration's foreign step keeps the relation. -/
theorem krelH_foreign1 {h : HSt} {σa σb : KVState} {cs : List mvcc.Change} (hrel : KRelH h σa)
    (hlen : h.hist.length = σa.rev) (hc : σb.compacted = σa.compacted) (hb : σb.base = σa.base)
    (hm : σb.changes = σa.changes ++ [cs]) (hf : ∀ ch ∈ cs, ¬ regP <+: ch.key) (hr : σb.rev < 2 ^ 63) :
    KRelH (foreignL h) σb ∧ (foreignL h).hist.length = σb.rev := by
  obtain ⟨-, hcur, hhist, hmod⟩ := hrel
  have hf' : ∀ cs' ∈ [cs], ∀ ch ∈ cs', ¬ regP <+: ch.key := by simpa using hf
  obtain ⟨hrb, hkb⟩ := kvs_snoc hc hb hm
  have hrv0 : W64 (σa.rev : Int) = h.st.rv := hcur.2.1
  have hst : (foreignL h).st = ⟨h.st.items, W64 (σb.rev : Int)⟩ := by
    simp only [foreignL]; rw [← hrv0, hrb]; congr 1; push_cast; word
  have hS : KRelS σb.store σb.rev (foreignL h).st := by
    rw [hst]
    exact krelS_foreign σb.rev hcur (at_ext_foreign regP hc hb hm hf' σb.rev (by omega))
  have hhs : (foreignL h).hist = h.hist ++ [(foreignL h).st] := rfl
  refine ⟨⟨hr, hS, fun r h1 h2 => ?_, fun r hr' v hv => ?_⟩, by rw [hhs]; simp [hlen, hrb]⟩
  · have hrw : uint.nat (W64 (r : Int)) = r := by
      simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
    by_cases hle : r ≤ σa.rev
    · rw [at_ext_below hc hb hm r hle, hhs, histAtL_snoc_le _ _ _ (by rw [hrw, hlen]; exact hle)]
      exact hhist r h1 hle
    · have hre : r = σb.rev := by omega
      rw [hhs, histAtL_snoc_gt _ _ _ (by rw [hrw, hlen]; omega), hre]
      exact hS
  · by_cases hle : r ≤ σa.rev
    · rw [at_ext_below hc hb hm r hle] at hv
      exact hmod r hle v hv
    · have hre : r = σb.rev := by omega
      rw [hre] at hv
      have hv' : v ∈ σb.kvs := hv
      rw [hkb] at hv'
      by_cases hmr : v.modRev = W64 ((σa.rev + 1 : Nat) : Int)
      · rw [hmr]; simp only [W64, uint.Z] at *; word
      · exact hmod σa.rev (Nat.le_refl _) v (txn.mem_applyChanges_modRev cs σa.kvs v hv' hmr)

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
for one more revision (`kvWf`/`kvWfHist` of `σ` follow: `kvWfHist_foreign1`, `kvWf_of_hist`). The relation holds at `σ`, the model state unchanged: the configuration related to
`σl` takes `σ.rev - σl.rev` foreign steps (`FClosed.foreign`), each appending the unchanged store. -/
abbrev kOkD_foreign.law (c : StoreCfg GF DObj) (g0 : HSt) : Prop :=
  ∀ (S : linkv.PSet HSt Input) (σl σ : KVState) (M : GMap Nat Input) (nx : Nat)
    (m : List (List mvcc.Change)),
    CfgD c → KOkD c g0 S σl M nx →
    σ.compacted = σl.compacted → σ.base = σl.base → σ.changes = σl.changes ++ m →
    (∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) → σ.rev + 1 < 2 ^ 63 →
    KOkD c g0 S σ M nx

/-- **A foreign revision keeps `kvWfHist`**: its key-values under the store's prefix are the last
revision's, and its mod revisions are the old ones or its own. -/
theorem kvWfHist_foreign1 (c : StoreCfg GF DObj) (hcd : CfgD c) {σa σb : KVState} {cs : List mvcc.Change}
    (hw : kvWfHist c σa) (hc : σb.compacted = σa.compacted) (hb : σb.base = σa.base)
    (hm : σb.changes = σa.changes ++ [cs]) (hf : ∀ ch ∈ cs, ¬ regP <+: ch.key) (hr : σb.rev < 2 ^ 63) :
    kvWfHist c σb := by
  have hf' : ∀ cs' ∈ [cs], ∀ ch ∈ cs', ¬ regP <+: ch.key := by simpa using hf
  obtain ⟨hrb, hkb⟩ := kvs_snoc hc hb hm
  intro r hr' v hv
  by_cases hle : r ≤ σa.rev
  · rw [at_ext_below hc hb hm r hle] at hv
    exact hw r hle v hv
  have hre : r = σb.rev := by omega
  subst hre
  have hv' : v ∈ σb.kvs := hv
  refine ⟨fun hp => ?_, ?_⟩
  · have hpr : regP <+: v.key := regP_kpfxD.trans (hcd.2 ▸ hp)
    have he := at_ext_foreign regP hc hb hm hf' σb.rev (by omega)
    have hmem : v ∈ (σb.at σb.rev).kvs.filter (fun v => decide (regP <+: v.key)) :=
      List.mem_filter.2 ⟨hv, by simpa using hpr⟩
    rw [he] at hmem
    exact (hw σa.rev (Nat.le_refl _) v (List.mem_filter.1 hmem).1).1 hp
  · rw [hkb] at hv'
    by_cases hmr : v.modRev = W64 ((σa.rev + 1 : Nat) : Int)
    · rw [hmr]; simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
    · have := (hw σa.rev (Nat.le_refl _) v (txn.mem_applyChanges_modRev cs σa.kvs v hv' hmr)).2
      omega

theorem kvWfHist_congr (c : StoreCfg GF DObj) {σ σ' : KVState} (hc : σ'.compacted = σ.compacted)
    (hb : σ'.base = σ.base) (hch : σ'.changes = σ.changes) (H : kvWfHist c σ) : kvWfHist c σ' := by
  obtain ⟨er, ea⟩ := at_congr hc hb hch
  simpa only [kvWfHist, er, ea] using H

/-- **`kvWf` of `kvWfHist`** (at the current revision) and the revision's bound. -/
theorem kvWf_of_hist (c : StoreCfg GF DObj) (σ : KVState) (hh : kvWfHist c σ) (hr : σ.rev + 1 < 2 ^ 63) :
    kvWf c σ := by
  have hmem : ∀ k x, (linkv.absSt σ).kv k = some x →
      ∃ v ∈ σ.kvs, v.key = k ∧ x = linkv.absVR v := by
    intro k x hx
    simp only [linkv.absSt, linkv.absM, Option.map_eq_some_iff] at hx
    obtain ⟨v, hf, rfl⟩ := hx
    exact ⟨v, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, rfl⟩
  refine ⟨KVStore.kvs_sorted _, fun k x hp hx => ?_, fun k x hx => ?_, hr⟩
  · obtain ⟨v, hv, rfl, rfl⟩ := hmem k x hx
    exact Option.isSome_iff_ne_none.2 ((hh σ.rev (Nat.le_refl _) v hv).1 hp)
  · obtain ⟨v, hv, rfl, rfl⟩ := hmem k x hx
    exact (hh σ.rev (Nat.le_refl _) v hv).2

/-- The foreign revisions `m`, one at a time (`FClosed.foreign`). -/
theorem kOkD_foreign_aux (c : StoreCfg GF DObj) (hcd : CfgD c) {g0 : HSt} {S : linkv.PSet HSt Input}
    (hcl : FClosed g0 S) {σl : KVState} {cf : GCfg} (hS : S cf) (hrel : KRelH cf.st σl)
    (hlen : cf.st.hist.length = σl.rev) (hw : kvWfHist c σl) :
    ∀ (m : List (List mvcc.Change)) (σ : KVState), σ.compacted = σl.compacted → σ.base = σl.base →
      σ.changes = σl.changes ++ m → (∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) → σ.rev < 2 ^ 63 →
      ∃ cf', S cf' ∧ KRelH cf'.st σ ∧ cf'.st.hist.length = σ.rev ∧ cf'.pend = cf.pend ∧ kvWfHist c σ := by
  intro m
  rw [← List.reverse_reverse m]
  induction m.reverse with
  | nil =>
    intro σ hc hb hm _ _
    rw [List.reverse_nil, List.append_nil] at hm
    obtain ⟨er, -⟩ := at_congr hc hb hm
    exact ⟨cf, hS, krelH_congr hc hb hm hrel, by rw [er]; exact hlen, rfl, kvWfHist_congr c hc hb hm hw⟩
  | cons cs l ih =>
    intro σ hc hb hm hf hr
    rw [List.reverse_cons] at hm hf
    let m' := l.reverse
    let σ' : KVState := { σ with changes := σl.changes ++ m' }
    have hm' : σ.changes = σ'.changes ++ [cs] := by rw [hm, List.append_assoc]
    have hr' : σ'.rev < 2 ^ 63 := by
      have := (kvs_snoc (σa := σ') (σb := σ) rfl rfl hm').1; omega
    obtain ⟨cf', hS', hrel', hlen', hpend, hw'⟩ :=
      ih σ' hc hb rfl (fun cs' h => hf cs' (List.mem_append_left _ h)) hr'
    have hcs : ∀ ch ∈ cs, ¬ regP <+: ch.key := hf cs (List.mem_append_right _ List.mem_cons_self)
    have hnw : NoWrap cf' := by
      have e := hrel'.2.1.2.1
      unfold NoWrap; rw [← e]; simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
    obtain ⟨hk, hl⟩ := krelH_foreign1 (σa := σ') (σb := σ) hrel' hlen' rfl rfl hm' hcs hr
    exact ⟨⟨foreignL cf'.st, cf'.pend⟩, hcl.foreign hS' hnw, hk, hl, hpend,
      kvWfHist_foreign1 c hcd (σa := σ') (σb := σ) hw' rfl rfl hm' hcs hr⟩

/-- **The catch-up over foreign revisions.** -/
theorem kOkD_foreign (c : StoreCfg GF DObj) (g0 : HSt) : kOkD_foreign.law c g0 := by
  intro S σl σ M nx m hcd H hc hb hm hf hr
  obtain ⟨cf, hS, hrel, hlen, hperm⟩ := H.cfg
  obtain ⟨cf', hS', hrel', hlen', hpend, hwh⟩ :=
    kOkD_foreign_aux c hcd H.closed hS hrel hlen H.hwf m σ hc hb hm hf (by omega)
  exact { closed := H.closed, wf := kvWf_of_hist c σ hwh hr, hwf := hwh,
          keys := keysOkP_foreign hc hb hm hf H.keys, vals := valsOkP_foreign hc hb hm hf H.vals,
          fresh := H.fresh, ins := H.ins, cfg := ⟨cf', hS', hrel', hlen', hpend ▸ hperm⟩ }

/-! ### `KOk`'s steps on `KOkD` (`Inv.lean`'s `kOk_*`, over `pSeqF` and prefix-only keys and values) -/

theorem nowrap_of_krelH {cf : GCfg} {σ : KVState} (h : KRelH cf.st σ) : NoWrap cf := by
  have e := h.2.1.2.1
  unfold NoWrap; rw [← e]; simp only [W64, uint.nat, BitVec.toNat_ofInt]; have := h.1; omega

/-- **The keys under `/registry/` stay the workload's** (`keysOk_step`, prefix-only). -/
theorem keysOkP_step (c : StoreCfg GF DObj) (σ σ' : KVState)
    (h : keysOkP σ) (hw' : kvWf c σ') (hn : k8s.KvNext σ σ') (hki : k8s.KeysIn c.pfx σ σ')
    (K : GoString) (hKw : K ∈ wkKeysL.map mkeyL)
    (hK : ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k) : keysOkP σ' := by
  intro r hr v hv hpv
  by_cases hle : r ≤ σ.rev
  · rw [kvNext_at hn r hle] at hv
    exact h r hle v hv hpv
  have hr' : r = σ'.rev := by rcases kvNext_rev hn with e | e <;> omega
  subst hr'
  have hv' : v ∈ σ'.kvs := hv
  have hold : ∀ w ∈ σ.kvs, w.key = v.key → v.key ∈ wkKeysL.map mkeyL := fun w hw e =>
    e ▸ h σ.rev (Nat.le_refl _) w hw (e ▸ hpv)
  rcases hki v hv' with ⟨w, hw, e⟩ | hp
  · exact hold w hw e
  · by_cases hex : ∃ w ∈ σ.kvs, w.key = v.key
    · obtain ⟨w, hw, e⟩ := hex; exact hold w hw e
    · have := newKey_eq c σ σ' hw' K hK v hv' hp (fun w hw e => hex ⟨w, hw, e⟩)
      rw [this]; exact hKw

/-- The store's model of a state whose values under `/registry/` are short has short objects. -/
theorem absValsP (c : StoreCfg GF DObj) (hc : CfgD c) (σ : KVState) (hw : kvWf c σ) (h : valsOkP σ) :
    ∀ k it, (c.abs σ).items k = some it → it.obj.val.length ≤ 2 ^ 20 := by
  intro k it hit
  by_cases hpk : c.pfx <+: k
  · cases hf : mvcc.findKey k σ.kvs with
    | none => rw [c.abs_none σ _ hf] at hit; cases hit
    | some w =>
      obtain ⟨o, b, hob⟩ := c.dec_of_wf σ hw k hpk w hf
      rw [c.abs_some σ k hpk w hf o b hob] at hit
      cases hit
      have hpw : regP <+: w.key := by rw [mvcc.findKey_key hf]; exact regP_kpfxD.trans (hc.2 ▸ hpk)
      exact h σ.rev (Nat.le_refl _) w (mvcc.findKey_mem hf) hpw (o, b) (by rw [← hc.1]; exact hob)
  · simp [StoreCfg.abs, absK, hpk] at hit

/-- **The values under `/registry/` stay short** (`valsOk_step`, prefix-only). -/
theorem valsOkP_step (c : StoreCfg GF DObj) (hc : CfgD c) (σ σ' : KVState)
    (h : valsOkP σ) (hw' : kvWf c σ') (hn : k8s.KvNext σ σ') (hk' : keysOkP σ')
    (hv : ∀ k it, (c.abs σ').items k = some it → it.obj.val.length ≤ 2 ^ 20) : valsOkP σ' := by
  intro r hr v hvm hpv d hd
  by_cases hle : r ≤ σ.rev
  · rw [kvNext_at hn r hle] at hvm
    exact h r hle v hvm hpv d hd
  have hr' : r = σ'.rev := by rcases kvNext_rev hn with e | e <;> omega
  subst hr'
  have hv' : v ∈ σ'.kvs := hvm
  have hf' := txn.findKey_of_mem_sorted hw'.1 hv'
  have hp : c.pfx <+: v.key := by
    rw [hc.2]
    obtain ⟨k, -, e⟩ := List.mem_map.1 (hk' σ'.rev (Nat.le_refl _) v hvm hpv)
    rw [← e]; exact kpfxD_mkeyL k
  obtain ⟨o, b⟩ := d
  have hd' : c.S.dec v.value = some (o, b) := by rw [hc.1]; exact hd
  exact hv _ _ (c.abs_some σ' v.key hp v hf' o b hd')

section port
variable {c : StoreCfg GF DObj} {g0 : HSt}

/-- The relation at the start: the model's initial state, nothing pending. -/
theorem kOkD_init (σ : KVState) (hw : kvWf c σ) (hwh : kvWfHist c σ) (hk : keysOkP σ)
    (hv : valsOkP σ) (he : KRelH g0 σ) (hl : g0.hist.length = σ.rev) :
    KOkD c g0 (fInit g0) σ (∅ : GMap Nat Input) 0 := by
  refine ⟨fInit_closed g0, hw, hwh, hk, hv, fun _ _ => rfl, (fun _ _ h => by cases h),
    ⟨⟨g0, []⟩, .refl _, he, hl, ?_⟩⟩
  simp [pendIns]

/-- **An operation answered at the real configuration** (not a list; `kOk_ok`). -/
theorem kOkD_ok (hc : CfgD c) {S : linkv.PSet HSt Input} {σ σ' : KVState} {M : GMap Nat Input}
    {nx : Nat} (H : KOkD c g0 S σ M nx) (eD eU : GoInterface) (x : Input) (hx : InOk x)
    (hval : x.Val'.length ≤ 2 ^ 20) (hk4 : x.Kind' ≠ W64 4) (h5 : x.Kind' ≠ W64 5)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) (hw' : kvWf c σ') (hn : k8s.KvNext σ σ')
    (hki : k8s.KeysIn c.pfx σ σ') (hr : σ.rev + 2 < 2 ^ 63) :
    ∃ S', (pSeqF g0).step S (x, .ok (kStep eD eU x (c.abs σ)).2) = some S' ∧
      KOkD c g0 S' σ' M nx := by
  obtain ⟨cf, hcf, hrel, hlen, hp⟩ := H.cfg
  have hwh' := kvWfHist_step c σ σ' H.hwf hw' hn
  obtain ⟨hrel', hlen', hout⟩ := cfg_step hc eD eU x hx hk4 cf.st σ σ' hrel hlen habs hn hwh' hr
  obtain ⟨S', hS', hc'⟩ := pSeqF_step_of hcf (.refl _) (nowrap_of_krelH hrel)
    (linkv.PStep.ok cf x (decide_eq_false h5)) (.refl _)
  have hKw : mkeyL x.Key' ∈ wkKeysL.map mkeyL := List.mem_map_of_mem hx.1
  have hkeys := keysOkP_step c σ σ' H.keys hw' hn hki _ hKw
    (fun k hk => by rw [habs]; exact kStep_items eD eU x _ k hk)
  have hvals := valsOkP_step c hc σ σ' H.vals hw' hn hkeys
    (by rw [habs]; exact kStep_vals eD eU x _ (absValsP c hc σ H.wf H.vals) hval)
  refine ⟨S', ?_, ⟨pSeqF_step_closed hS', hw', hwh', hkeys, hvals, H.fresh, H.ins,
    ⟨_, hc', hrel', hlen', hp⟩⟩⟩
  rw [hout]; exact hS'

/-- **A list answered at the real configuration** (`kOk_list`). -/
theorem kOkD_list {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOkD c g0 S σ M nx) (x : Input) (hx : InOk x) (hk4 : x.Kind' = W64 4) :
    ∃ S', (pSeqF g0).step S (x, .ok (lOut x σ)) = some S' ∧ KOkD c g0 S' σ M nx := by
  obtain ⟨cf, hcf, hrel, hlen, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := pSeqF_step_of hcf (.refl _) (nowrap_of_krelH hrel)
    (linkv.PStep.ok cf x (decide_eq_false (by rw [hk4]; decide))) (.refl _)
  have hst : kstepL x cf.st = (cf.st, mlistL x cf.st) := by unfold kstepL; rw [if_pos hk4]
  rw [show (kSpec g0).step x cf.st = (cf.st, mlistL x cf.st) from hst] at hS' hc'
  refine ⟨S', ?_, ⟨pSeqF_step_closed hS', H.wf, H.hwf, H.keys, H.vals, H.fresh, H.ins,
    ⟨_, hc', hrel, hlen, hp⟩⟩⟩
  rw [refine_lOut x cf.st σ hrel hx hk4]; exact hS'

/-- A write committed as pending, its token minted at `nx` (`kOk_errW`). -/
theorem kOkD_errW {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOkD c g0 S σ M nx) (x : Input) (hw : isWriteL x = true) (hx : InOk x)
    (hval : x.Val'.length ≤ 2 ^ 20) :
    ∃ S', (pSeqF g0).step S (x, .err) = some S' ∧
      KOkD c g0 S' σ (GMap.insert nx x M) (nx + 1) := by
  obtain ⟨cf, hc, hst, hlen, hp⟩ := H.cfg
  have h5 : x.Kind' ≠ W64 5 := by
    intro e; simp [isWriteL, e] at hw
  obtain ⟨S', hS', hc'⟩ := pSeqF_step_of hc (.refl _) (nowrap_of_krelH hst)
    (linkv.PStep.errW cf x hw (decide_eq_false h5)) (.refl _)
  refine ⟨S', hS', ⟨pSeqF_step_closed hS', H.wf, H.hwf, H.keys, H.vals, ?_, ?_,
    ⟨_, hc', hst, hlen, ?_⟩⟩⟩
  · intro n hn
    show (GMap.insert nx x M) !! n = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact H.fresh n (by omega)
  · intro n j hn
    by_cases e : nx = n
    · subst e
      have : (GMap.insert nx x M) !! nx = some x := GMap.lookup_insert _ _ _
      rw [this] at hn
      cases hn
      exact ⟨hx, hw, hval⟩
    · have : (GMap.insert nx x M) !! n = M !! n := GMap.lookup_insert_ne _ _ e
      rw [this] at hn
      exact H.ins n j hn
  · exact (pendIns_insert M nx x (H.fresh nx (Nat.le_refl _))).trans (hp.cons _)

/-- A read that failed (`kOk_errR`). -/
theorem kOkD_errR {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOkD c g0 S σ M nx) (x : Input) (hw : isWriteL x = false) (h5 : x.Kind' ≠ W64 5) :
    ∃ S', (pSeqF g0).step S (x, .err) = some S' ∧ KOkD c g0 S' σ M nx := by
  obtain ⟨cf, hc, hst, hlen, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := pSeqF_step_of hc (.refl _) (nowrap_of_krelH hst)
    (linkv.PStep.errR cf x hw (decide_eq_false h5)) (.refl _)
  exact ⟨S', hS', ⟨pSeqF_step_closed hS', H.wf, H.hwf, H.keys, H.vals, H.fresh, H.ins,
    ⟨cf, hc', hst, hlen, hp⟩⟩⟩

/-- A watch whose answer every configuration related at `σ` allows (`kOk_obs`). -/
theorem kOkD_obs {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOkD c g0 S σ M nx) (x : Input) (y : Output) (hk5 : x.Kind' = W64 5)
    (hw : ∀ cf : linkv.PCfg HSt Input, S cf → KRelH cf.st σ → cf.st.hist.length = σ.rev →
      watchOkL x y cf.st = true) :
    ∃ S', (pSeqF g0).step S (x, .ok y) = some S' ∧ KOkD c g0 S' σ M nx := by
  obtain ⟨cf, hc, hst, hlen, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := pSeqF_step_of hc (.refl _) (nowrap_of_krelH hst)
    (linkv.PStep.obs cf x y (decide_eq_true hk5) (hw cf hc hst hlen)) (.refl _)
  exact ⟨S', hS', ⟨pSeqF_step_closed hS', H.wf, H.hwf, H.keys, H.vals, H.fresh, H.ins,
    ⟨cf, hc', hst, hlen, hp⟩⟩⟩

/-- **A late effect**: the pending write `n ↦ x` takes effect, the model state unchanged (`kOk_pend`). -/
theorem kOkD_pend (hc : CfgD c) {S : linkv.PSet HSt Input} {σ σ' : KVState} {M : GMap Nat Input}
    {nx : Nat} (H : KOkD c g0 S σ M nx) (eD eU : GoInterface) (n : Nat) (x : Input)
    (hn : M !! n = some x)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) (hw' : kvWf c σ') (hnx : k8s.KvNext σ σ')
    (hki : k8s.KeysIn c.pfx σ σ') (hr : σ.rev + 2 < 2 ^ 63) :
    KOkD c g0 S σ' (GMap.delete n M) nx := by
  obtain ⟨cf, hcf, hst, hlen, hp⟩ := H.cfg
  obtain ⟨hx, hwx, hval⟩ := H.ins n x hn
  have hd := pendIns_delete M n x hn
  have hmem : x ∈ cf.pend := hp.subset (hd.symm.subset List.mem_cons_self)
  have hwh' := kvWfHist_step c σ σ' H.hwf hw' hnx
  obtain ⟨hrel', hlen', -⟩ :=
    cfg_step hc eD eU x hx (isWriteL_ne4 x hwx) cf.st σ σ' hst hlen habs hnx hwh' hr
  have hKw : mkeyL x.Key' ∈ wkKeysL.map mkeyL := List.mem_map_of_mem hx.1
  have hkeys := keysOkP_step c σ σ' H.keys hw' hnx hki _ hKw
    (fun k hk => by rw [habs]; exact kStep_items eD eU x _ k hk)
  have hvals := valsOkP_step c hc σ σ' H.vals hw' hnx hkeys
    (by rw [habs]; exact kStep_vals eD eU x _ (absValsP c hc σ H.wf H.vals) hval)
  refine ⟨H.closed, hw', hwh', hkeys, hvals, ?_, ?_,
    ⟨_, H.closed.pend hcf (nowrap_of_krelH hst) (.apply cf x hmem), hrel', hlen', ?_⟩⟩
  · intro m hm
    show (GMap.delete n M) !! m = none
    by_cases e : n = m
    · subst e; exact GMap.lookup_delete _ _
    · rw [GMap.lookup_delete_ne _ e]; exact H.fresh m hm
  · intro m j hm
    by_cases e : n = m
    · subst e
      have : (GMap.delete n M) !! n = none := GMap.lookup_delete _ _
      rw [this] at hm; cases hm
    · have : (GMap.delete n M) !! m = M !! m := GMap.lookup_delete_ne _ e
      rw [this] at hm
      exact H.ins m j hm
  · refine List.Perm.cons_inv ((hd.symm.trans hp).trans ?_)
    exact List.perm_cons_erase hmem

/-- A firing that leaves etcd's state as it was. -/
theorem kOkD_same {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOkD c g0 S σ M nx) : KOkD c g0 S σ M nx := H

end port

/-- **The revisions' states on the shared KV** (`revOwn` with `KHistID`). -/
def revOwnD (γ : KNames) (σ : KVState) : IProp GF :=
  iprop(∃ Mr : GMap Nat KVState, ghostMapAuth γ.r 1 Mr ∗
    ghostMapElem γ.r σ.rev DFrac.discard σ ∗ ⌜RevOk Mr σ⌝ ∗
    monoListAuthOwn γ.ch 1 σ.changes ∗ ⌜KHistID γ σ⌝)

instance revOwnD_timeless (γ : KNames) (σ : KVState) : Timeless (revOwnD (GF := GF) γ σ) := by
  unfold revOwnD; infer_instance

/-- `KHistID` over foreign revisions: their changes are not under `/registry/`. -/
theorem khistID_foreign (γ : KNames) {σl σ : KVState} {m : List (List mvcc.Change)} (h : KHistID γ σl)
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) : KHistID γ σ := by
  obtain ⟨h0, hb0, ho, h1⟩ := h
  refine ⟨hc ▸ h0, hb ▸ hb0, fun cs hcs => ?_, ?_⟩
  · rw [hm] at hcs
    rcases List.mem_append.1 hcs with h' | h'
    · exact ho cs h'
    · rw [List.filter_eq_nil_iff.2 (fun ch hch => by simpa using hf cs h' ch hch)]; simp
  · unfold KVState.rev at h1 ⊢; rw [hc, hm, List.length_append]; omega

/-- **The revisions' map catches up over foreign revisions** (at least one: the new current state
gets its own entry). -/
theorem revOwnD_catchup (γ : KNames) {σl σ : KVState} {m : List (List mvcc.Change)}
    (hc : σ.compacted = σl.compacted) (hb : σ.base = σl.base) (hm : σ.changes = σl.changes ++ m)
    (hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) (hne : m ≠ []) :
    revOwnD (GF := GF) γ σl ⊢ |==> revOwnD γ σ := by
  have hlt : σl.rev < σ.rev := by
    unfold KVState.rev; rw [hc, hm, List.length_append]
    have := List.length_pos_iff.2 hne; omega
  have hext : k8s.KvExt σl σ := ⟨hc.symm, hb.symm, ⟨m, hm.symm⟩⟩
  iintro H
  iunfold revOwnD at H
  icases H with ⟨%Mr, HA, -, %Hok, Hch, %Hkh⟩
  have hfresh : Mr !! σ.rev = none := Hok.2.1 _ hlt
  imod ghost_map_insert_persist σ.rev σ hfresh $$ HA with ⟨HA, #He⟩
  ihave Hch := monoListAuthOwn_update σ.changes hext.2.2 $$ Hch
  imod Hch with ⟨Hch, -⟩
  imodintro
  iunfold revOwnD
  iexists _
  iframe He HA Hch
  ipureintro
  refine ⟨⟨GMap.lookup_insert _ _ _, fun n hn => ?_, fun n s hs => ?_⟩,
    khistID_foreign γ Hkh hc hb hm hf⟩
  · rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact Hok.2.1 n (by omega)
  · by_cases e : σ.rev = n
    · subst e
      rw [GMap.lookup_insert] at hs
      cases hs; exact ⟨rfl, rfl, List.prefix_refl _⟩
    · rw [GMap.lookup_insert_ne _ _ e] at hs
      have h1 := Hok.2.2 n s hs; exact ⟨h1.1.trans hext.1, h1.2.1.trans hext.2.1, h1.2.2.trans hext.2.2⟩

/-- **A foreign revision's entry changes no key under the store's prefix**. -/
theorem chgOf_foreign_pfx (q : GoString) (hq : regP <+: q) {σa σb : KVState}
    (he : σb.kvs.filter (fun v => decide (regP <+: v.key)) = σa.kvs.filter (fun v => decide (regP <+: v.key))) :
    ((chgOf σa σb).map Prod.fst).filter (fun k => decide (q <+: k)) = [] := by
  have hmem : ∀ v, regP <+: v.key → (v ∈ σb.kvs ↔ v ∈ σa.kvs) := fun v hv => by
    have := congrArg (v ∈ ·) he
    simpa [List.mem_filter, hv] using this
  rw [List.filter_eq_nil_iff]
  intro k hk hpk
  have hpk' : regP <+: k := hq.trans (by simpa using hpk)
  unfold chgOf at hk
  simp only [List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_filter,
    Function.comp_def, decide_eq_true_eq] at hk
  rcases hk with ⟨v, ⟨hv, hn⟩, rfl⟩ | ⟨v, ⟨hv, hn⟩, rfl⟩
  · exact hn ((hmem v hpk').1 hv)
  · exact hn v ((hmem v hpk').2 hv) rfl

/-- `histAuth_next` with only what its proof uses of the step (the revision and the new key-values'
mod revisions), for foreign revisions, which may change several keys (to move to `History.lean`). -/
theorem histAuth_step (γh : GName) (σ σ' : KVState) (hrev : σ'.rev = σ.rev + 1)
    (hnew : ∀ v ∈ σ'.kvs, v ∈ σ.kvs ∨ v.modRev = W64 ((σ'.rev : Nat) : Int)) (hr : σ'.rev < 2 ^ 64) :
    histAuth (GF := GF) γh σ ⊢ |==> (histAuth γh σ' ∗ revSeen γh σ σ') := by
  have hs0 := KVStore.kvs_sorted σ.store
  have hs := KVStore.kvs_sorted σ'.store
  iintro H
  iunfold histAuth at H
  icases H with ⟨%H, HA, %Hok, #Hs⟩
  have hR : uint.nat (W64 ((σ'.rev : Nat) : Int)) = σ'.rev := by
    simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
  have hfr : H !! W64 ((σ'.rev : Nat) : Int) = none := by
    cases h : H !! W64 ((σ'.rev : Nat) : Int) with
    | none => rfl
    | some x =>
      have := Hok _ _ h
      omega
  have hnd := chgOf_nodup σ σ' hs0 hs
  imod ghost_map_insert_persist (W64 ((σ'.rev : Nat) : Int)) (chgOf σ σ') hfr $$ HA
    with ⟨HA, #He⟩
  imodintro
  isplitl [HA]
  · iunfold histAuth
    iexists (H.insert (W64 ((σ'.rev : Nat) : Int)) (chgOf σ σ'))
    iframe HA
    isplitr
    · ipureintro
      intro r ch hv
      by_cases e : W64 ((σ'.rev : Nat) : Int) = r
      · subst e; omega
      · rw [GMap.lookup_insert_ne _ _ e] at hv
        have := Hok _ _ hv; omega
    iunfold kvSeen
    imodintro
    iintro %v %hv
    by_cases hin : v ∈ σ.kvs
    · iunfold kvSeen at Hs
      iapply Hs
      ipureintro; exact hin
    · have hm : v.modRev = W64 ((σ'.rev : Nat) : Int) := by
        rcases hnew v hv with h | h
        · exact absurd h hin
        · exact h
      iexists (chgOf σ σ')
      rw [hm]
      iframe He
      ipureintro
      exact ⟨chgOf_new σ σ' v hv hin, hnd⟩
  · iunfold revSeen
    imodintro
    iintro %-
    iexact He

/-- **The store's history over one foreign revision**: its entry changes no key under the prefix. -/
theorem shistOwn_foreign1 (c : StoreCfg GF DObj) (hcd : CfgD c) {σa σb : KVState} {cs : List mvcc.Change}
    (hc : σb.compacted = σa.compacted) (hb : σb.base = σa.base) (hm : σb.changes = σa.changes ++ [cs])
    (hf : ∀ ch ∈ cs, ¬ regP <+: ch.key) (hr : σb.rev < 2 ^ 63) :
    shistOwn (GF := GF) c σa ⊢ |==> shistOwn c σb := by
  have hf' : ∀ cs' ∈ [cs], ∀ ch ∈ cs', ¬ regP <+: ch.key := by simpa using hf
  obtain ⟨hrb, hkb⟩ := kvs_snoc hc hb hm
  have hnew : ∀ v ∈ σb.kvs, v ∈ σa.kvs ∨ v.modRev = W64 ((σb.rev : Nat) : Int) := by
    intro v hv
    rw [hkb] at hv
    by_cases hmr : v.modRev = W64 ((σa.rev + 1 : Nat) : Int)
    · right; rw [hmr, hrb]
    · left; exact txn.mem_applyChanges_modRev cs σa.kvs v hv hmr
  have he := at_ext_foreign regP hc hb hm hf' σb.rev (by omega)
  have h0 := chgOf_foreign_pfx c.pfx (hcd.2 ▸ regP_kpfxD) (σa := σa) (σb := σb) he
  iintro H
  iunfold shistOwn at H
  icases H with ⟨Hh, #Ho⟩
  imod (histAuth_step c.γh σa σb hrb hnew (by omega)) $$ Hh with ⟨Hh, #Hs⟩
  imodintro
  iunfold shistOwn
  iframe Hh
  iunfold oneKeyRevs
  imodintro
  iintro %r %hr'
  by_cases hlast : r = σb.rev
  · subst hlast
    iunfold revSeen at Hs
    ihave He := Hs $$ %hrb
    iexists (chgOf σa σb)
    isplit
    · iexact He
    · ipureintro; rw [h0]; simp
  · iunfold oneKeyRevs at Ho
    iapply Ho
    ipureintro; omega

/-- **The store's history catches up over foreign revisions** (at least one). -/
theorem shistOwn_catchup (c : StoreCfg GF DObj) (hcd : CfgD c) (σl : KVState) :
    ∀ (m : List (List mvcc.Change)) (σ : KVState), m ≠ [] → σ.compacted = σl.compacted →
      σ.base = σl.base → σ.changes = σl.changes ++ m → (∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key) →
      σ.rev < 2 ^ 63 → shistOwn (GF := GF) c σl ⊢ |==> shistOwn c σ := by
  intro m
  rw [← List.reverse_reverse m]
  induction m.reverse with
  | nil => intro σ hne; exact absurd rfl hne
  | cons cs l ih =>
    intro σ _ hc hb hm hf hr
    rw [List.reverse_cons] at hm hf
    have hcs : ∀ ch ∈ cs, ¬ regP <+: ch.key := hf cs (List.mem_append_right _ List.mem_cons_self)
    by_cases hl : l = []
    · subst hl
      rw [List.reverse_nil, List.nil_append] at hm
      exact shistOwn_foreign1 c hcd hc hb hm hcs hr
    · let σ' : KVState := { σ with changes := σl.changes ++ l.reverse }
      have hm' : σ.changes = σ'.changes ++ [cs] := by rw [hm, List.append_assoc]
      have hr' : σ'.rev < 2 ^ 63 := by
        have := (kvs_snoc (σa := σ') (σb := σ) rfl rfl hm').1; omega
      have h1 := ih σ' (by simpa using hl) hc hb rfl
        (fun cs' h => hf cs' (List.mem_append_left _ h)) hr'
      iintro H
      imod h1 $$ H with H
      iapply (shistOwn_foreign1 c hcd (σa := σ') (σb := σ) rfl rfl hm' hcs hr)
      iexact H

/-- **The store's half of the invariant at the last state `σl` it saw** (`kInvBody` without etcd's client
half): the lintest ghost history `h` over `pMF`, the pending writes, the revisions' states, the store's
history, and the relation; `σl` extends the share's start `σ₀`. -/
def kInvDW (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (σ₀ σl : KVState) : IProp GF :=
  iprop(∃ (h : List OpV) (S : linkv.PSet HSt Input) (M : GMap Nat Input) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ ghostMapAuth γ.p 1 M ∗ revOwnD γ σl ∗ shistOwn c σl ∗
    ⌜etcd_dist.KVExt σ₀ σl ∧ run (pMF g0 decOp) (fInit g0) h = some S ∧ KOkD c g0 S σl M nx⌝)

/-- **The store's value of the share's ghost variable** (`KVPfxHist`'s `W`): `v` is `pfxVH regP σl` at the
last state `σl` the store saw, with a lower bound of `σl`'s changes in the share's history `γsh` (K8-8: the
firings' authority over the history then says `σl`'s changes are a prefix of the current state's), and the
store's half at `σl`. -/
def kInvDV (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γsh : GName) (σ₀ : KVState)
    (v : etcd_dist.PfxV) : IProp GF :=
  iprop(∃ σl : KVState, ⌜v = etcd_dist.pfxVH regP σl⌝ ∗ monoListLbOwn γsh σl.changes ∗ kInvDW γ c g0 σ₀ σl)

/-- The invariant's contents (`KVPfxHist`'s client invariant): the prefix's ghost half `γs` and the store's
value of it. -/
def kInvDBody (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γs γsh : GName) (σ₀ : KVState) : IProp GF :=
  iprop(∃ v, ghostVar γs (1 : Qp).half v ∗ kInvDV γ c g0 γsh σ₀ v)

/-- The invariant's namespace. -/
def drvDInvN : Namespace := client.kvClientN .@ "k8s"

/-- **The store's invariant on the shared KV.** -/
def kInvD (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γs γsh : GName) (σ₀ : KVState) : IProp GF :=
  iprop(inv drvDInvN (kInvDBody γ c g0 γs γsh σ₀))

instance kInvD_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γs γsh : GName) (σ₀ : KVState) :
    Persistent (kInvD (GF := GF) γ c g0 γs γsh σ₀) := by
  unfold kInvD; infer_instance

/-! ### The catch-up of `kInvDW` (K8-8; decisions of Handoff K8-7) -/

/-- **The bound on the share's revision the catch-up needs** (decision 3): one more revision fits in
etcd's revisions. A named premise of the catch-up and of the firings, never assumed elsewhere; K10
discharges it by the client law from time receipts (`srvLogCert`'s `⧖`, as K9's revision bound). -/
def RevBoundD (σ : KVState) : Prop := σ.rev + 1 < 2 ^ 63

/-- **Two states equal up to the lessor's table** (decision 2): what a foreign lease grant, which moves no
revision, changes. -/
def SameL (σc σ : KVState) : Prop :=
  σc.compacted = σ.compacted ∧ σc.base = σ.base ∧ σc.changes = σ.changes

theorem SameL.refl (σ : KVState) : SameL σ σ := ⟨rfl, rfl, rfl⟩

/-- **No new revision, the same changes** (decision 2): two states extending the start, the first's
changes a prefix of the second's, at the same revision have the same changes. -/
theorem sameL_of_rev {σ₀ σl σ : KVState} (hl : etcd_dist.KVExt σ₀ σl) (he : etcd_dist.KVExt σ₀ σ)
    (hp : σl.changes <+: σ.changes) (hr : σ.rev = σl.rev) : SameL σl σ := by
  refine ⟨hl.1.trans he.1.symm, hl.2.1.trans he.2.1.symm, ?_⟩
  have hlen : σ.changes.length = σl.changes.length := by
    unfold KVState.rev at hr; rw [he.1, hl.1] at hr; omega
  exact hp.eq_of_length hlen.symm

/-- **A lease-only difference is invisible to the prefix** (decision 2): the key-values under `p` (at every
revision) and the history of `p` are the same. -/
theorem pfxVH_sameL (p : GoString) {σc σ : KVState} (hs : SameL σc σ) :
    etcd_dist.pfxVH p σ = etcd_dist.pfxVH p σc := by
  obtain ⟨er, ea⟩ := at_congr hs.1 hs.2.1 hs.2.2
  simp only [etcd_dist.pfxVH, etcd_dist.pfxView, etcd_dist.pfxChs, KVState.kvs, KVState.store, er, ea,
    hs.1, hs.2.2]

/-- **The store's steps read a state only up to its leases** (decision 2): a step from `σ` that moves is a
step from a state equal to `σ` up to its leases. -/
theorem kvNext_sameL {σc σ σ' : KVState} (hs : SameL σc σ) (hn : KvNext σ σ') (hne : σ' ≠ σ) :
    KvNext σc σ' := by
  rcases hn with h | ⟨h1, h2, h3, h4⟩
  · exact absurd h hne
  obtain ⟨er, ea⟩ := at_congr hs.1 hs.2.1 hs.2.2
  have hk : σc.kvs = σ.kvs := by unfold KVState.kvs KVState.store; rw [er, ea]
  right
  refine ⟨by rw [er]; exact h1, by rw [hk]; exact h2, ?_, ?_⟩
  · obtain ⟨a, b, d⟩ := h3; exact ⟨hs.1.trans a, hs.2.1.trans b, hs.2.2 ▸ d⟩
  · unfold KvOne at h4 ⊢; rw [hs.2.2]; exact h4

/-- **The store's half catches up with the share's state** (up to its leases): the store last saw `σl`;
the share is at `σ`, extending `σl` with the same `pfxVH regP`, so the revisions in between have no change
under `/registry/` (`pfxChs_same_ext`). With none, the half stays at `σl` (decision 2: `σ` is `σl` up to its
leases); otherwise `kOkD_foreign` and the ghost catch-ups take it to `σ`, the lintest ghost and the pending
writes unchanged. -/
theorem kInvDW_catchup (γ : KNames) (c : StoreCfg GF DObj) (hcd : CfgD c) (g0 : HSt) {σ₀ σl σ : KVState}
    (he : etcd_dist.KVExt σ₀ σ) (hv : etcd_dist.pfxVH regP σ = etcd_dist.pfxVH regP σl)
    (hp : σl.changes <+: σ.changes) (hrb : RevBoundD σ) :
    kInvDW γ c g0 σ₀ σl ⊢ |==> ∃ σc, ⌜SameL σc σ⌝ ∗ kInvDW γ c g0 σ₀ σc := by
  obtain ⟨m, hm⟩ := hp
  iintro H
  iunfold kInvDW at H
  icases H with ⟨%h, %S, %M, %nx, Hh, Hp, Hr, Hs, %Hpure⟩
  obtain ⟨hel, hrun, hok⟩ := Hpure
  have hc : σ.compacted = σl.compacted := he.1.trans hel.1.symm
  have hb : σ.base = σl.base := he.2.1.trans hel.2.1.symm
  have hf : ∀ cs ∈ m, ∀ ch ∈ cs, ¬ regP <+: ch.key := by
    have := etcd_dist.pfxChs_same_ext hel he ⟨m, hm⟩ (congrArg Prod.snd hv)
    rw [← hm, List.drop_left] at this; exact this
  by_cases hne : m = []
  · subst hne
    imodintro
    iexists σl
    isplit
    · ipureintro; exact ⟨hc.symm, hb.symm, by simpa using hm⟩
    iunfold kInvDW
    iexists h, S, M, nx
    iframe Hh Hp Hr Hs
    ipureintro; exact ⟨hel, hrun, hok⟩
  · have hm' : σ.changes = σl.changes ++ m := hm.symm
    have hok' := kOkD_foreign c g0 S σl σ M nx m hcd hok hc hb hm' hf hrb
    imod (revOwnD_catchup γ hc hb hm' hf hne) $$ Hr with Hr
    imod (shistOwn_catchup c hcd σl m σ hne hc hb hm' hf (by unfold RevBoundD at hrb; omega)) $$ Hs
      with Hs
    imodintro
    iexists σ
    isplit
    · ipureintro; exact SameL.refl σ
    iunfold kInvDW
    iexists h, S, M, nx
    iframe Hh Hp Hr Hs
    ipureintro; exact ⟨he, hrun, hok'⟩

/-- **The catch-up inside a firing** (`kvPfxP_au1H`/`kvPfxP_readAuH`'s step, which holds the share's
history): the store's value of the ghost variable at the share's `σ` gives its half at a state equal to `σ`
up to its leases. -/
theorem kInvDV_catchup (γ : KNames) (c : StoreCfg GF DObj) (hcd : CfgD c) (g0 : HSt) (γsh : GName)
    {σ₀ σ : KVState} (he : etcd_dist.KVExt σ₀ σ) (hrb : RevBoundD σ) :
    monoListAuthOwn γsh 1 σ.changes ∗ kInvDV γ c g0 γsh σ₀ (etcd_dist.pfxVH regP σ) ⊢
      |==> (monoListAuthOwn γsh 1 σ.changes ∗ ∃ σc, ⌜SameL σc σ⌝ ∗ kInvDW γ c g0 σ₀ σc) := by
  iintro ⟨Ha, H⟩
  iunfold kInvDV at H
  icases H with ⟨%σl, %hv, #Hlb, H⟩
  ihave %Hp := mono_list_auth_lb_valid (GF := GF) γsh 1 σ.changes σl.changes $$ Ha Hlb
  imod (kInvDW_catchup (GF := GF) γ c hcd g0 he hv Hp.2 hrb) $$ H with H
  imodintro
  iframe Ha
  iexact H

/-- **The store's value back at a state equal to the share's up to its leases** (the end of a read's
firing: `σc` is the share's state but for its leases). -/
theorem kInvDV_of_sameL (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γsh : GName) {σ₀ σc σ : KVState}
    (q : Qp) (hs : SameL σc σ) :
    monoListAuthOwn γsh q σ.changes ∗ kInvDW γ c g0 σ₀ σc ⊢
      monoListAuthOwn γsh q σ.changes ∗ kInvDV γ c g0 γsh σ₀ (etcd_dist.pfxVH regP σ) := by
  iintro ⟨Ha, H⟩
  ihave #Hlb := monoListLbOwn_get γsh q σ.changes $$ Ha
  iframe Ha
  iunfold kInvDV
  iexists σc
  rw [← hs.2.2]
  iframe H Hlb
  ipureintro; exact pfxVH_sameL regP hs

end defs

end k8s_dist
end EtcdGrove
end Perennial
