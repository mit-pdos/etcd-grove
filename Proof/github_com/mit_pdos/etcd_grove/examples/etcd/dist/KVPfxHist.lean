/- Lean-first (no Rocq counterpart).

# The shared KV with each prefix's history in its ghost variable (k8s-dist K8-2)

`KVPfxDist`'s share keeps, for each owned prefix `p`, half of a ghost variable at `pfxView p σ`, the
state's key-values under `p`. Its owner learns that nobody else changed them, but not that nobody else
changed a key under `p` and changed it back (a put then a delete leaves the view equal), which an owner that
accounts for every revision (the k8s store: `notes/k8s-dist-k8-scope.md` §1, `kInvD`'s catch-up over
foreign revisions) needs. Here the ghost variable holds `pfxVH p σ`: the view and `pfxChs p σ`, the
revisions with a change of a key under `p` and those changes. Another owner's update (`PfxLocal q`, `q`
apart from `p`) appends no such change, so it keeps `pfxChs p`; equal `pfxChs` at two states, one's changes
extending the other's, means no change under `p` in between (`pfxChs_same`).

The invariant `kvPfxInvP`, the owner's fact `kvPfxHP`, the laws `kvPfxP_au1H`/`kvPfxP_readAuH`/
`kvPfxP_alloc`/`kvPfxP_seen` are `KVPfxDist`'s (`kvPfxInv`, `kvPfxH`, ...) at the ghost value `pfxVH`
instead of `pfxView`, proofs unchanged but `viewsP_local` (`pfxVH_local`) and the allocation's start
value (`pfxVH_init`). A deployment allocates one of the two shares. Kept beside `KVPfxDist`, not in it, so
that its users (putget, durable, compact) do not change; once the k8s start uses this one, `KVPfxDist`'s
laws can become corollaries (the view is `pfxVH`'s first component).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPfxDist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The changes of `cs` of a key under `p`. -/
def pfxOf (p : GoString) (cs : List mvcc.Change) : List mvcc.Change :=
  cs.filter (fun c => decide (p <+: c.key))

/-- **The revisions of `l` with a change under `p`**, the first of `l` revision `n + 1`: each such
revision with its changes under `p`. -/
def chsFrom (p : GoString) : Nat → List (List mvcc.Change) → List (Nat × List mvcc.Change)
  | _, [] => []
  | n, cs :: l => (if pfxOf p cs = [] then [] else [(n + 1, pfxOf p cs)]) ++ chsFrom p (n + 1) l

/-- **The prefix's history**: the state's revisions with a change of a key under `p`, with those changes. -/
def pfxChs (p : GoString) (σ : KVState) : List (Nat × List mvcc.Change) :=
  chsFrom p σ.compacted σ.changes

/-- A prefix's ghost value: its key-values and its history. -/
abbrev PfxV : Type := List EtcdKv × List (Nat × List mvcc.Change)

/-- The ghost value of a prefix with no key-value and no change. -/
def pfxV0 : PfxV := ([], [])

/-- **The prefix's view with its history.** -/
def pfxVH (p : GoString) (σ : KVState) : PfxV := (pfxView p σ, pfxChs p σ)

theorem chsFrom_append (p : GoString) :
    ∀ (n : Nat) (l m : List (List mvcc.Change)),
      chsFrom p n (l ++ m) = chsFrom p n l ++ chsFrom p (n + l.length) m
  | n, [], m => by simp [chsFrom]
  | n, cs :: l, m => by
    simp only [List.cons_append, chsFrom, chsFrom_append p (n + 1) l m, List.append_assoc,
      List.length_cons]
    rw [show n + 1 + l.length = n + (l.length + 1) by omega]

/-- No change under `p`: no revision in the history. -/
theorem chsFrom_nil (p : GoString) :
    ∀ (n : Nat) (l : List (List mvcc.Change)), (∀ cs ∈ l, ∀ c ∈ cs, ¬ p <+: c.key) → chsFrom p n l = []
  | _, [], _ => rfl
  | n, cs :: l, h => by
    have h1 : pfxOf p cs = [] :=
      List.filter_eq_nil_iff.2 (fun c hc => by simpa using h cs List.mem_cons_self c hc)
    simp only [chsFrom, h1, ite_true, List.nil_append]
    exact chsFrom_nil p (n + 1) l (fun cs' hcs' => h cs' (List.mem_cons_of_mem _ hcs'))

/-- No revision in the history: no change under `p`. -/
theorem chsFrom_eq_nil (p : GoString) :
    ∀ (n : Nat) (l : List (List mvcc.Change)), chsFrom p n l = [] → ∀ cs ∈ l, ∀ c ∈ cs, ¬ p <+: c.key
  | _, [], _ => by simp
  | n, cs :: l, h => by
    intro cs' hcs' c hc hpc
    simp only [chsFrom] at h
    split at h
    · rename_i h1
      rcases List.mem_cons.1 hcs' with rfl | hcs'
      · exact (List.filter_eq_nil_iff.1 h1 c hc) (by simpa using hpc)
      · exact chsFrom_eq_nil p (n + 1) l (by simpa using h) cs' hcs' c hc hpc
    · simp at h

/-- **An update local to `p` keeps the view and the history of every prefix apart from `p`.** -/
theorem pfxVH_local {p : GoString} {f : KVState → KVState} (hf : PfxLocal p f) (σ : KVState)
    (q : GoString) (hqp : ¬ q <+: p) (hpq : ¬ p <+: q) : pfxVH q (f σ) = pfxVH q σ := by
  obtain ⟨hc, _, new, hnew, hloc⟩ := hf.2 σ
  have hn : chsFrom q (σ.compacted + σ.changes.length) new = [] := by
    apply chsFrom_nil
    intro cs hcs c hc' hqc
    rcases List.prefix_or_prefix_of_prefix hqc (hloc cs hcs c hc') with h | h
    · exact hqp h
    · exact hpq h
  unfold pfxVH pfxChs
  rw [hf.1 σ q hqp hpq, hc, hnew, chsFrom_append, hn, List.append_nil]

/-- The start's value: no key-value, no change. -/
theorem pfxVH_init {σ₀ : KVState} (h0 : σ₀.kvs = []) (hc0 : ∀ cs ∈ σ₀.changes, cs = [])
    (p : GoString) : pfxVH p σ₀ = pfxV0 := by
  have hn : chsFrom p σ₀.compacted σ₀.changes = [] := by
    apply chsFrom_nil
    intro cs hcs c hc
    rw [hc0 cs hcs] at hc
    simp at hc
  unfold pfxVH pfxV0 pfxChs pfxView
  rw [h0, hn]
  rfl

/-- **Equal histories, no change under `p` in between**: at two states with the same compaction
revision, the second's changes the first's followed by `m`, equal `pfxChs p` means no change of `m` is of
a key under `p` (a put then a delete under `p` would add two revisions to the history). -/
theorem pfxChs_same {p : GoString} {σl σ : KVState} (hc : σl.compacted = σ.compacted)
    {m : List (List mvcc.Change)} (hm : σ.changes = σl.changes ++ m)
    (h : pfxChs p σ = pfxChs p σl) : ∀ cs ∈ m, ∀ c ∈ cs, ¬ p <+: c.key := by
  unfold pfxChs at h
  rw [hm, chsFrom_append, ← hc] at h
  exact chsFrom_eq_nil p _ m (by simpa using congrArg List.length h)

/-- `pfxChs_same` for two states extending the start's, the first's changes a prefix of the second's. -/
theorem pfxChs_same_ext {p : GoString} {σ₀ σl σ : KVState} (hl : KVExt σ₀ σl) (h2 : KVExt σ₀ σ)
    (hp : σl.changes <+: σ.changes) (h : pfxChs p σ = pfxChs p σl) :
    ∀ cs ∈ σ.changes.drop σl.changes.length, ∀ c ∈ cs, ¬ p <+: c.key := by
  obtain ⟨m, hm⟩ := hp
  apply pfxChs_same (hl.1.trans h2.1.symm) (m := σ.changes.drop σl.changes.length) _ h
  conv => lhs; rw [← hm]
  rw [← hm, List.drop_left]

/-! ### Updates local to a prefix: commits of changes under it -/

/-- A change of a key not under `q` keeps the key-values under `q`. -/
theorem filter_applyChange_other (q : GoString) (r : w64) (s : List EtcdKv) (c : mvcc.Change)
    (hc : ¬ q <+: c.key) :
    (mvcc.applyChange r s c).filter (fun v => decide (q <+: v.key)) =
      s.filter (fun v => decide (q <+: v.key)) := by
  cases c with
  | put k val l =>
    apply filter_putKv_other
    intro v hv hvk
    simp only [decide_eq_true_eq] at hv
    rw [hvk] at hv
    exact hc hv
  | del k =>
    simp only [mvcc.applyChange]
    rw [List.filter_filter]
    apply List.filter_congr
    intro v _
    by_cases hv : q <+: v.key
    · have hk : v.key ≠ k := fun h => hc (by rw [← h]; exact hv)
      simp [hv, hk]
    · simp [hv]

/-- Changes of keys not under `q` keep the key-values under `q`. -/
theorem filter_applyChanges_other (q : GoString) (r : w64) (cs : List mvcc.Change)
    (hc : ∀ c ∈ cs, ¬ q <+: c.key) : ∀ s : List EtcdKv,
    (mvcc.applyChanges r s cs).filter (fun v => decide (q <+: v.key)) =
      s.filter (fun v => decide (q <+: v.key)) := by
  induction cs with
  | nil => intro s; rfl
  | cons c cs ih =>
    intro s
    simp only [mvcc.applyChanges, List.foldl_cons] at ih ⊢
    rw [ih (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')),
      filter_applyChange_other q r s c (hc c List.mem_cons_self)]

/-- A commit of changes of keys not under `q` keeps the view of `q`. -/
theorem pfxView_commit_other (q : GoString) (σ : KVState) (cs : List mvcc.Change)
    (hc : ∀ c ∈ cs, ¬ q <+: c.key) : pfxView q (σ.commit cs) = pfxView q σ := by
  by_cases h : cs = []
  · rw [h, KVState.commit_nil]
  · unfold pfxView
    rw [KVState.commit_kvs σ cs h]
    exact filter_applyChanges_other q _ cs hc σ.kvs

/-- A commit keeps the compaction revision and the base, and appends its changes (if any). -/
theorem commit_hist (σ : KVState) (cs : List mvcc.Change) :
    (σ.commit cs).compacted = σ.compacted ∧ (σ.commit cs).base = σ.base ∧
      ∃ new : List (List mvcc.Change), (σ.commit cs).changes = σ.changes ++ new ∧ ∀ x ∈ new, x = cs := by
  unfold KVState.commit
  split
  · exact ⟨rfl, rfl, [], by simp, by simp⟩
  · exact ⟨rfl, rfl, [cs], rfl, by simp⟩

/-- **An update that commits changes of keys under `p` (or does nothing) is local to `p`** (the k8s
store's compare-put, compare-delete and else-get Txns under `/registry/`: `pfxLocal_txn`). -/
theorem pfxLocal_commit (p : GoString) (f : KVState → KVState)
    (hf : ∀ σ, f σ = σ ∨ ∃ cs, f σ = σ.commit cs ∧ ∀ c ∈ cs, p <+: c.key) : PfxLocal p f := by
  have hoth : ∀ (cs : List mvcc.Change), (∀ c ∈ cs, p <+: c.key) → ∀ q : GoString, ¬ q <+: p →
      ¬ p <+: q → ∀ c ∈ cs, ¬ q <+: c.key := by
    intro cs hcs q hqp hpq c hc hqc
    rcases List.prefix_or_prefix_of_prefix hqc (hcs c hc) with h | h
    · exact hqp h
    · exact hpq h
  refine ⟨fun σ q hqp hpq => ?_, fun σ => ?_⟩
  · rcases hf σ with h | ⟨cs, h, hcs⟩
    · rw [h]
    · rw [h]; exact pfxView_commit_other q σ cs (hoth cs hcs q hqp hpq)
  · rcases hf σ with h | ⟨cs, h, hcs⟩
    · rw [h]; exact ⟨rfl, rfl, [], by simp, by simp⟩
    · obtain ⟨h1, h2, new, h3, h4⟩ := commit_hist σ cs
      rw [h]
      refine ⟨h1, h2, new, h3, fun x hx c hc => ?_⟩
      rw [h4 x hx] at hc
      exact hcs c hc

/-- **A Txn whose changes are all of keys under `p`, whatever the state, is local to `p`.** -/
theorem pfxLocal_txn (p : GoString) {t}
    (ht : ∀ (σ : KVState) (c : mvcc.Change),
      c ∈ (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1 → p <+: c.key) :
    PfxLocal p (kvOpStep (.txn t)) := by
  apply pfxLocal_commit
  intro σ
  simp only [kvOpStep]
  split
  · exact Or.inr ⟨_, rfl, ht σ⟩
  · exact Or.inl rfl

/-- **A delete whose changes are all of keys under `p`, in every state, is local to `p`** (a delete of
one key under `p`). -/
theorem pfxLocal_deleteRange (p : GoString) {o}
    (ho : ∀ (s : List EtcdKv) (c : mvcc.Change), c ∈ txn.delChanges s o → p <+: c.key) :
    PfxLocal p (kvOpStep (.deleteRange o)) := by
  apply pfxLocal_commit
  intro σ
  exact Or.inr ⟨_, rfl, ho σ.kvs⟩

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The cluster's client KV, shared by the prefixes `ps`** (see the file header): the state's half, each
prefix's view's half, the list of its changes (`γh`, append-only: every change of the KV is an owner's update
firing in this invariant), the state extending the start's `σ₀` (`KVExt`: every update keeps the compaction
revision and base and appends changes), and each
prefix's discipline over its history (`ok`, F5). -/
def kvPfxInvP (γk : KVNames) (ps : List (GoString × GName)) (ok : GoString → mvcc.Change → Prop)
    (γh : GName) (σ₀ : KVState) : IProp GF :=
  inv kvShareN iprop(∃ σ : KVState, etcdKV γk σ ∗
    ([∗list] _k ↦ e ∈ ps, ghostVar e.2 (1 : Qp).half (pfxVH e.1 σ)) ∗
    monoListAuthOwn γh 1 σ.changes ∗
    ⌜KVExt σ₀ σ ∧ ∀ e ∈ ps, PfxChOk e.1 (ok e.1) σ.changes⌝)

/-- **The prefix `p` is owned at `γ` in the shared KV of `γk`, under the discipline `okp`, its history
at `γh` from the start `σ₀`** (persistent; F5: what an owner that reads the history holds). -/
def kvPfxHP (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) : IProp GF :=
  iprop(∃ (ps : List (GoString × GName)) (i : Nat) (ok : GoString → mvcc.Change → Prop),
    ⌜PfxsApart ps ∧ ps[i]? = some (p, γ) ∧ ∀ c, ok p c ↔ okp c⌝ ∗ kvPfxInvP γk ps ok γh σ₀)

instance kvPfxInvP_persistent (γk : KVNames) (ps : List (GoString × GName))
    (ok : GoString → mvcc.Change → Prop) (γh : GName) (σ₀ : KVState) :
    Persistent (kvPfxInvP (GF := GF) γk ps ok γh σ₀) := by
  unfold kvPfxInvP; infer_instance

instance kvPfxHP_persistent (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop)
    (γh : GName) (σ₀ : KVState) : Persistent (kvPfxHP (GF := GF) γk p γ okp γh σ₀) := by
  unfold kvPfxHP; infer_instance

/-- The owned prefix's item of the views, and the others'. -/
theorem viewsP_acc (ps : List (GoString × GName)) (i : Nat) (p : GoString) (γ : GName)
    (hi : ps[i]? = some (p, γ)) (σ : KVState) :
    ([∗list] k ↦ e ∈ ps, ghostVar (GF := GF) e.2 (1 : Qp).half (pfxVH e.1 σ)) ⊣⊢
      ghostVar γ (1 : Qp).half (pfxVH p σ) ∗
        [∗list] k ↦ e ∈ ps, if k = i then emp else ghostVar e.2 (1 : Qp).half (pfxVH e.1 σ) :=
  BigSepL.bigSepL_delete_cond hi

/-- The other prefixes' items, at a state whose views of them are the same. -/
theorem viewsP_frame (ps : List (GoString × GName)) (i : Nat) (σ σ' : KVState)
    (h : ∀ (k : Nat) (e : GoString × GName), k ≠ i → ps[k]? = some e →
      pfxVH e.1 σ' = pfxVH e.1 σ) :
    ([∗list] k ↦ e ∈ ps, if k = i then emp else ghostVar (GF := GF) e.2 (1 : Qp).half (pfxVH e.1 σ)) ⊢
      [∗list] k ↦ e ∈ ps, if k = i then emp else ghostVar e.2 (1 : Qp).half (pfxVH e.1 σ') := by
  apply BigSepL.bigSepL_mono
  intro k e hk
  by_cases hki : k = i
  · rw [if_pos hki, if_pos hki]
  · rw [if_neg hki, if_neg hki, h k e hki hk]

/-- An update local to the owned prefix leaves the others' views. -/
theorem viewsP_local {ps : List (GoString × GName)} {i : Nat} {p : GoString} {γ : GName}
    (hap : PfxsApart ps) (hi : ps[i]? = some (p, γ)) {f : KVState → KVState} (hf : PfxLocal p f)
    (σ : KVState) :
    ∀ (k : Nat) (e : GoString × GName), k ≠ i → ps[k]? = some e → pfxVH e.1 (f σ) = pfxVH e.1 σ := by
  intro k e hk he
  exact pfxVH_local hf σ e.1 (hap k i e (p, γ) hk he hi) (hap i k (p, γ) e (Ne.symm hk) hi he)

/-- **An owner's update of the KV, fired at most once, reading the history** (`KVPfxDist.kvPfx_au1H`'s,
at the ghost value `pfxVH`, and from a lower bound `l0` of the changes, e.g. the owner's last update's): the
step learns that the changes extend `l0`; with its `W` recording `pfxVH p` at `l0`'s state, `pfxChs_same_ext`
then says no change after `l0` is under `p`. -/
theorem kvPfxP_au1H (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (s : String) (hs : s ≠ "share")
    (W : PfxV → IProp GF) [hW : ∀ v, Timeless (W v)] (l0 : List (List mvcc.Change))
    (f : KVState → KVState) (hf : PfxLocal p f)
    (hok : ∀ σ new, (f σ).changes = σ.changes ++ new → ∀ cs ∈ new, ∀ c ∈ cs, okp c)
    (Q : KVState → IProp GF) :
    kvPfxHP γk p γ okp γh σ₀ ∗
      inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ W v) ∗
      monoListLbOwn γh l0 ∗
      (∀ σ, ⌜l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk p okp σ.changes⌝ -∗
        monoListLbOwn γh (f σ).changes -∗ W (pfxVH p σ) ==∗ W (pfxVH p (f σ)) ∗ Q σ) ⊢
    AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
      <{ etcdKV γk (f σ) ∗ ⌜kvRoom σ⌝, COMM Q σ }> := by
  have Hm := client.kvClientN_mask
  have Hm2 := kvShareN_mask s hs
  iintro ⟨#Hpfx, #Hinv, #Hl0, Hstep⟩
  iunfold kvPfxHP at Hpfx
  icases Hpfx with ⟨%ps, %i, %ok, %Hps, #Hsh⟩
  obtain ⟨Hap, Hi, Hok⟩ := Hps
  iunfold kvPfxInvP at Hsh
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hw Hclosew
  icases Hw with ⟨%v, Hhalf, HW⟩
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hcloses $$ [Hσ Hviews Hh] with -
    · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists v; iframe Hhalf HW
    imodintro
    itrivial
  · iintro ⟨Hσ, %Hroom⟩
    imod Hmask with -
    obtain ⟨hc, hb, new, hnew, hloc⟩ := hf.2 σ
    icases (viewsP_acc ps i p γ Hi σ).1 $$ Hviews with ⟨Hown, Hrest⟩
    ihave %Hv := ghostVar_agree γ v _ (pfxVH p σ) _ $$ Hhalf Hown
    subst Hv
    imod (ghostVar_update_halves (pfxVH p (f σ)) γ (pfxVH p σ) (pfxVH p σ)) $$ Hhalf Hown
      with ⟨Hhalf, Hown⟩
    ihave %Hp := mono_list_auth_lb_valid (GF := GF) γh 1 σ.changes l0 $$ Hh Hl0
    have hpre : σ.changes <+: (f σ).changes := by rw [hnew]; exact List.prefix_append _ _
    imod (monoListAuthOwn_update (f σ).changes hpre) $$ Hh with ⟨Hh, #Hlb⟩
    have hpre' : l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk p okp σ.changes :=
      ⟨Hp.2, Hσok.1, fun cs hcs c hc hpc =>
        (Hok c).1 (Hσok.2 (p, γ) (List.mem_of_getElem? Hi) cs hcs c hc hpc)⟩
    imod Hstep $$ %σ %hpre' Hlb HW with ⟨HW, HQ⟩
    ihave Hrest := viewsP_frame ps i σ (f σ) (viewsP_local Hap Hi hf σ) $$ Hrest
    have hnext : KVExt σ₀ (f σ) ∧ ∀ e ∈ ps, PfxChOk e.1 (ok e.1) (f σ).changes := by
      refine ⟨⟨by rw [hc]; exact Hσok.1.1, by rw [hb]; exact Hσok.1.2.1,
        Hσok.1.2.2.trans hpre⟩, ?_⟩
      rw [hnew]
      exact pfxChOk_step ps ok i p γ Hap Hi σ.changes new hloc
        (fun cs hcs c hc' => (Hok c).2 (hok σ new hnew cs hcs c hc')) Hσok.2
    imod Hcloses $$ [Hσ Hown Hrest Hh] with -
    · inext; iexists (f σ); iframe Hσ Hh
      isplitl [Hown Hrest]
      · iapply (viewsP_acc ps i p γ Hi (f σ)).2
        iframe Hown Hrest
      ipureintro; exact hnext
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists (pfxVH p (f σ)); iframe Hhalf HW
    imodintro
    iexact HQ

/-- **An owner's persistent read update of the KV, reading the history** (F5): `kvPfx_readAu`'s, the step
also learning that the state's changes extend `l0` (a lower bound the caller has), its compaction revision
and base, that its changes keep the owner's discipline, and their lower bound. -/
theorem kvPfxP_readAuH (γk : KVNames) (p : GoString) (γ : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (s : String) (hs : s ≠ "share")
    (W : PfxV → IProp GF) [hW : ∀ v, Timeless (W v)] (l0 : List (List mvcc.Change))
    (Q : KVState → IProp GF) :
    kvPfxHP γk p γ okp γh σ₀ ∗
      inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ (1 : Qp).half v ∗ W v) ∗
      monoListLbOwn γh l0 ∗
      □ (∀ σ, ⌜l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk p okp σ.changes⌝ -∗
        monoListLbOwn γh σ.changes -∗ W (pfxVH p σ) ==∗ W (pfxVH p σ) ∗ □ Q σ) ⊢
    kvReadAu γk Q := by
  have Hm := client.kvClientN_mask
  have Hm2 := kvShareN_mask s hs
  iintro ⟨#Hpfx, #Hinv, #Hl0, #Hstep⟩
  iunfold kvPfxHP at Hpfx
  icases Hpfx with ⟨%ps, %i, %ok, %Hps, #Hsh⟩
  obtain ⟨Hap, Hi, Hok⟩ := Hps
  iunfold kvPfxInvP at Hsh
  iunfold kvReadAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hw Hclosew
  icases Hw with ⟨%v, Hhalf, HW⟩
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hcloses $$ [Hσ Hviews Hh] with -
    · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists v; iframe Hhalf HW
    imodintro
    itrivial
  · iintro ⟨Hσ, %Hroom⟩
    imod Hmask with -
    ihave %Hp := mono_list_auth_lb_valid (GF := GF) γh 1 σ.changes l0 $$ Hh Hl0
    ihave #Hlb := monoListLbOwn_get γh 1 σ.changes $$ Hh
    icases (viewsP_acc ps i p γ Hi σ).1 $$ Hviews with ⟨Hown, Hrest⟩
    ihave %Hv := ghostVar_agree γ v _ (pfxVH p σ) _ $$ Hhalf Hown
    subst Hv
    have hpre' : l0 <+: σ.changes ∧ KVExt σ₀ σ ∧ PfxChOk p okp σ.changes :=
      ⟨Hp.2, Hσok.1, fun cs hcs c hc hpc =>
        (Hok c).1 (Hσok.2 (p, γ) (List.mem_of_getElem? Hi) cs hcs c hc hpc)⟩
    imod Hstep $$ %σ %hpre' Hlb HW with ⟨HW, #HQ⟩
    imod Hcloses $$ [Hσ Hown Hrest Hh] with -
    · inext; iexists σ; iframe Hσ Hh
      isplitl [Hown Hrest]
      · iapply (viewsP_acc ps i p γ Hi σ).2
        iframe Hown Hrest
      ipureintro; exact Hσok
    imod Hclosew $$ [Hhalf HW] with -
    · inext; iexists (pfxVH p σ); iframe Hhalf HW
    imodintro
    iintro !>
    iexact HQ

/-- `n` ghost variables at `[]`, each whole. -/
theorem ghostVarsP_alloc (n : Nat) :
    ⊢ |==> ∃ γs : List GName, ⌜γs.length = n⌝ ∗
      [∗list] γ ∈ γs, ghostVar (GF := GF) γ 1 pfxV0 := by
  induction n with
  | zero =>
    imodintro
    iexists []
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.2
      itrivial
  | succ n ih =>
    ihave H := ih
    imod H with ⟨%γs, %hl, Hs⟩
    imod (ghostVar_alloc (GF := GF) pfxV0) with Hγ
    icases Hγ with ⟨%γ, Hγ⟩
    imodintro
    iexists γ :: γs
    isplitr
    · ipureintro; simp [hl]
    · iapply BigSepL.bigSepL_cons.2
      iframe Hγ Hs

/-- **The start's allocation of the shared KV** (see the file header): from the cluster's client half at
a state with no key-value and no change, for prefixes `pfxs` none a prefix of another and each prefix's
discipline `ok` (F5), the shared invariant, the history's name `γh` with a lower bound of the start's
changes, and, for each prefix, its name `γ` (`kvPfxHP`, at the start's compaction revision and base) and the
owner's half at `[]`. -/
theorem kvPfxP_alloc (γk : KVNames) (σ₀ : KVState) (h0 : σ₀.kvs = [])
    (hc0 : ∀ cs ∈ σ₀.changes, cs = []) (pfxs : List GoString)
    (hap : ∀ (i j : Nat) (a b : GoString), i ≠ j → pfxs[i]? = some a → pfxs[j]? = some b → ¬ a <+: b)
    (ok : GoString → mvcc.Change → Prop) (E : CoPset) :
    etcdKV (GF := GF) γk σ₀ ={E}=∗ ∃ (γh : GName) (γs : List GName), ⌜γs.length = pfxs.length⌝ ∗
      monoListLbOwn γh σ₀.changes ∗
      [∗list] e ∈ pfxs.zip γs, kvPfxHP γk e.1 e.2 (ok e.1) γh σ₀ ∗
        ghostVar e.2 (1 : Qp).half pfxV0 := by
  iintro Hσ
  ihave H := ghostVarsP_alloc (GF := GF) pfxs.length
  imod H with ⟨%γs, %hl, Hs⟩
  imod (mono_list_own_alloc (GF := GF) σ₀.changes) with ⟨%γh, Hh, #Hlb⟩
  have hv : ∀ p : GoString, pfxVH p σ₀ = pfxV0 := pfxVH_init h0 hc0
  -- each whole variable as two halves: the invariant's and the owner's
  have hz : (pfxs.zip γs).map Prod.snd = γs := by
    rw [List.map_snd_zip]; omega
  have hconv : ([∗list] γ ∈ γs, ghostVar (GF := GF) γ 1 pfxV0) ⊢
      [∗list] e ∈ pfxs.zip γs, ghostVar (GF := GF) e.2 (1 : Qp).half (pfxVH e.1 σ₀) ∗
        ghostVar e.2 (1 : Qp).half pfxV0 := by
    conv => lhs; rw [← hz]
    rw [BigSepL.bigSepL_map]
    apply BigSepL.bigSepL_mono
    intro k e _
    rw [hv]
    exact (ghostVar_split_half (GF := GF) e.2 1 pfxV0).1
  ihave Hs2 := hconv $$ Hs
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hs2 with ⟨Hinvs, Hown⟩
  have hap' : PfxsApart (pfxs.zip γs) := by
    intro i j a b hij ha hb
    have ha' := List.getElem?_zip_eq_some.1 ha
    have hb' := List.getElem?_zip_eq_some.1 hb
    exact hap i j a.1 b.1 hij ha'.1 hb'.1
  have hok0 : KVExt σ₀ σ₀ ∧ ∀ e ∈ pfxs.zip γs, PfxChOk e.1 (ok e.1) σ₀.changes :=
    ⟨⟨rfl, rfl, List.prefix_refl _⟩, fun _ _ cs hcs c hc _ => by rw [hc0 cs hcs] at hc; simp at hc⟩
  imod (inv_alloc kvShareN E iprop(∃ σ : KVState, etcdKV (GF := GF) γk σ ∗
      ([∗list] _k ↦ e ∈ pfxs.zip γs, ghostVar e.2 (1 : Qp).half (pfxVH e.1 σ)) ∗
      monoListAuthOwn γh 1 σ.changes ∗
      ⌜KVExt σ₀ σ ∧ ∀ e ∈ pfxs.zip γs, PfxChOk e.1 (ok e.1) σ.changes⌝)) $$ [Hσ Hinvs Hh] with #Hinv
  · inext; iexists σ₀; iframe Hσ Hinvs Hh; ipureintro; exact hok0
  have hall : □ kvPfxInvP (GF := GF) γk (pfxs.zip γs) ok γh σ₀ ⊢
      [∗list] e ∈ pfxs.zip γs, kvPfxHP (GF := GF) γk e.1 e.2 (ok e.1) γh σ₀ := by
    apply BigSepL.bigSepL_intro
    intro k e he
    iintro #Hinv'
    iunfold kvPfxHP
    iexists (pfxs.zip γs), k, ok
    isplitr
    · ipureintro
      exact ⟨hap', by rw [he], fun _ => Iff.rfl⟩
    iexact Hinv'
  ihave #HinvP : kvPfxInvP (GF := GF) γk (pfxs.zip γs) ok γh σ₀ $$ []
  · iunfold kvPfxInvP
    iexact Hinv
  ihave Hall := hall $$ HinvP
  imodintro
  iexists γh, γs
  isplitr
  · ipureintro; exact hl
  iframe Hlb
  iapply (BigSepL.bigSepL_sep_eqv).2
  isplitl [Hall]
  · iexact Hall
  · iexact Hown
end ghost

section seen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A revision the cluster's KV has reached is at most the shared state's** (F5; `kv_revLbZ_le` over the
shared invariant, outside every update): with the KV invariant, a reached revision `n` (`kvRevLbZ`) gives a
lower bound of the state's changes whose revision (the start's compaction revision plus their number) is at least `n`, so every read that
fires later (`kvPfxP_readAuH` at that bound) reads at a revision at least `n`. -/
theorem kvPfxP_seen [go_etcd_io.raft.v3.Assumptions] (γk : KVNames) (p : GoString) (γ : GName)
    (okp : mvcc.Change → Prop) (γh : GName) (σ₀ : KVState) (γr : ServerRaftNames)
    (n : Int) :
    ⊢ kvPfxHP (GF := GF) (Gg := hG.goose_globalGS) γk p γ okp γh σ₀ -∗ kvInv γr γk -∗ kvRevLbZ γk n ={⊤}=∗
      ∃ l : List (List mvcc.Change), monoListLbOwn γh l ∗
        ⌜n ≤ ((σ₀.compacted + l.length : Nat) : Int)⌝ := by
  iintro #Hpfx #Hkv #Hlb
  iunfold kvPfxHP at Hpfx
  icases Hpfx with ⟨%ps, %i, %ok, -, #Hsh⟩
  iunfold kvPfxInvP at Hsh
  iinv Hsh with >Hs Hcloses
  icases Hs with ⟨%σ, Hσ, Hviews, Hh, %Hσok⟩
  have hE : (↑kvN : CoPset) ⊆ ⊤ \ ↑kvShareN := by
    intro x hx
    rw [Std.LawfulSet.mem_diff]
    refine ⟨CoPset.mem_full, fun h => ?_⟩
    have h2 := client.kvClientN_mask x (nclose_subseteq client.kvClientN "share" x h)
    rw [Std.LawfulSet.mem_diff] at h2
    exact h2.2 hx
  imod (kv_revLbZ_le γr γk (⊤ \ ↑kvShareN) hE n σ) $$ Hkv Hlb Hσ with ⟨Hσ, %Hn⟩
  ihave #Hl := monoListLbOwn_get γh 1 σ.changes $$ Hh
  imod Hcloses $$ [Hσ Hviews Hh] with -
  · inext; iexists σ; iframe Hσ Hviews Hh; ipureintro; exact Hσok
  imodintro
  iexists σ.changes
  iframe Hl
  ipureintro
  rw [← Hσok.1.rev_eq]; exact Hn

end seen
end etcd_dist
end EtcdGrove
end Perennial

end
