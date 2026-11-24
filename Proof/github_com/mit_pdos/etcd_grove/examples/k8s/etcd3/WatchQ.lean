/-
Lean-first (no Rocq counterpart).

# A watch's read update (stage E of 7f-6, plan §3 step 4; Draft D3)

`watchQ γ c lb σ`: what each firing of a watch's read update gives at etcd's state `σ`, read from
the instance's invariant: `σ` past the lower bound `lb`, fit for the store (`kvWf`, `kvWfHist`,
short keys, every put under the prefix decoding, `kvWritesDec`), with room, and etcd's history
facts (`KHistI`: no compaction, the base store, one change per revision, past revision `1`), with
a lower bound of its changes in the invariant's mono list. Its laws are `runWatch.spec`'s premises
on `Q` (`watchQ_pure`; `watchQ_same`: two firings are of one history, by the mono list). Its
producers (`watch_read_au`, `watch_readAus`): the invariant, with a lower bound `l` of the changes,
gives each member's read update at any `lb ≤ l.length` (`[]` for the first firing; an earlier
firing's changes for the next, so the next one is not older).

(k8s 7g step 5) `run_hist_ge`: the configurations the model reaches have histories at least the seeded
one's; `kInv_lb_seed`: a lower bound of etcd's changes past the seeded revision (a watch's read updates
fire past it, so the store's watch starts after the seeds: B5's `WatchFromL`); `watch_commit` also
returns a pure fact every configuration related to the commit state gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.InvSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatchBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatchFrom
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Every put under the prefix decodes** (`kvWritesDec`), from the states' (`kvWfHist`) when
each revision changes one key at most and nothing is compacted: a revision's one put is in its
state. -/
theorem writesDec_of (c : StoreCfg GF DObj) (σ : KVState) (hw : kvWfHist c σ) (ho : OneChange σ)
    (hc0 : σ.compacted = 0) : kvWritesDec c σ := by
  intro r hr ch hch k v l hput hpfx
  subst hput
  unfold KVState.changesAt at hch
  rw [hc0] at hch
  split at hch
  · simp at hch
  rename_i hr0
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hrev : σ.rev = σ.changes.length := by unfold KVState.rev; rw [hc0, Nat.zero_add]
  have hr1 : r' < σ.changes.length := by omega
  simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getElem?_eq_getElem hr1, Option.getD_some]
    at hch
  have hlen : σ.changes[r'].length ≤ 1 := ho _ (List.getElem_mem _)
  have hcs : σ.changes[r'] = [mvcc.Change.put k v l] := by
    match h : σ.changes[r'], hlen, hch with
    | [], _, hm => simp [h] at hm
    | [a], _, hm => simp only [h, List.mem_singleton] at hm; rw [hm]
    | _ :: _ :: _, hl, _ => simp [h] at hl
  have hat := KVState.at_kvs σ (r' + 1) (by omega)
  have htake : σ.changes.take (r' + 1 - σ.compacted) = σ.changes.take r' ++ [σ.changes[r']] := by
    rw [hc0, Nat.sub_zero, List.take_add_one, List.getElem?_eq_getElem hr1]
    simp
  rw [htake, runFrom_append, hcs] at hat
  have hsort := runFrom_sorted σ.compacted (σ.changes.take r') (KVStore.kvs_sorted σ.base)
  obtain ⟨nv, hf, hk, hv⟩ := client.findKey_putKv_value _ hsort
    (W64 ((σ.compacted + (σ.changes.take r').length + 1 : Nat) : Int)) k v l
  have hmem : nv ∈ (σ.at (r' + 1)).kvs := by
    rw [hat]
    simp only [mvcc.applyChanges, List.foldl_cons, List.foldl_nil, mvcc.applyChange]
    exact List.mem_of_find?_eq_some hf
  have := (hw (r' + 1) hr nv hmem).1 (hk ▸ hpfx)
  rwa [hv] at this

end pure

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **etcd's history as the watch check's bridge needs it** (`KHistW`), from the invariant's facts
(`kvWfHist` at the driver's store, `KHistI`). -/
theorem khistW_of (c : StoreCfg GF DObj) (hc : CfgD c) (γ : KNames) (σ : KVState)
    (hw : kvWfHist c σ) (hk : KHistI γ σ) : KHistW σ := by
  refine ⟨hk.1, fun r hr v hv => ?_, fun r hr => ?_⟩
  · have := hw r hr v hv
    rw [hc.1, hc.2] at this
    exact this
  · refine Nat.le_trans (List.length_filter_le _ _) ?_
    unfold KVState.changesAt
    split
    · simp
    · cases h : σ.changes[r - σ.compacted - 1]? with
      | none => simp
      | some cs => simpa using hk.2.2.1 cs (List.mem_of_getElem? h)

/-- **A watch's read update's result** at a firing at `σ` (see the file header). -/
def watchQ (γ : KNames) (c : StoreCfg GF DObj) (lb : Nat) (σ : KVState) : IProp GF :=
  iprop(⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
      kvRevFits σ.rev ∧ KHistI γ σ⌝ ∗ monoListLbOwn γ.ch σ.changes)

instance watchQ_persistent (γ : KNames) (c : StoreCfg GF DObj) (lb : Nat) (σ : KVState) :
    Persistent (watchQ γ c lb σ) := by
  unfold watchQ; infer_instance

/-- `runWatch.spec`'s first premise on `Q`. -/
theorem watchQ_pure (γ : KNames) (c : StoreCfg GF DObj) (lb : Nat) (σ : KVState) :
    watchQ γ c lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ ∧ kvWritesDec c σ ∧
      kvRevFits σ.rev⌝ := by
  unfold watchQ
  iintro ⟨%H, -⟩
  ipureintro; exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1⟩

/-- `runWatch.spec`'s second premise on `Q`: two firings are of one history. -/
theorem watchQ_same (γ : KNames) (c : StoreCfg GF DObj) (lb lb' : Nat) (σ σ' : KVState) :
    watchQ γ c lb σ ∗ watchQ γ c lb' σ' ⊢ ⌜kvSameHist σ σ'⌝ := by
  unfold watchQ
  iintro ⟨⟨%H, #Hl⟩, ⟨%H', #Hl'⟩⟩
  ihave %Hp := mono_list_lb_valid γ.ch σ.changes σ'.changes $$ Hl Hl'
  ipureintro
  obtain ⟨hc, hb, -⟩ := H.2.2.2.2.2.2
  obtain ⟨hc', hb', -⟩ := H'.2.2.2.2.2.2
  exact ⟨hc.trans hc'.symm, hb.trans hb'.symm, Hp⟩

/-- **A member's watch read update** (see the file header): the invariant and a lower bound `l` of
etcd's changes give the read update at `lb ≤ l.length`. -/
theorem watch_read_au (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames)
    (l : List (List mvcc.Change)) (lb : Nat) (hlb : lb ≤ l.length) :
    kInv γ c g0 γk ∗ monoListLbOwn γ.ch l ⊢ kvReadAu γk (watchQ γ c lb) := by
  have Hm := drvInvN_mask'
  iintro ⟨#Hinv, #Hl⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hrv, %Hpre⟩ := revOwn_lb γ σ l $$ [Hrv Hl]
  · iframe Hrv Hl
  imod revOwn_hist γ σ $$ Hrv with ⟨Hrv, %Hkh, #Hlbσ⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro ⟨Hσ, %hroom⟩
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    imodintro
    iunfold watchQ
    iframe Hlbσ
    ipureintro
    have hrev : σ.rev = σ.changes.length := by unfold KVState.rev; rw [Hkh.1, Nat.zero_add]
    refine ⟨?_, Hok.wf, Hok.hwf, keysOk_short σ Hok.keys, writesDec_of c σ Hok.hwf Hkh.2.2.1 Hkh.1,
      ?_, Hkh⟩
    · have := Hpre.length_le; omega
    · unfold kvRevFits; unfold kvRoom at hroom; omega

/-- **One change per revision, read** (the watch condition's source, `srvOnce_of_plan`): the
invariant gives the read update whose result is `OneChange` of the state. -/
theorem one_read_au (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames) :
    kInv γ c g0 γk ⊢ kvReadAu γk (fun σ => iprop(⌜OneChange σ⌝)) := by
  have Hm := drvInvN_mask'
  iintro #Hinv
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  imod revOwn_hist γ σ $$ Hrv with ⟨Hrv, %Hkh, -⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro ⟨Hσ, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    imodintro
    ipureintro; exact Hkh.2.2.1

/-- **Every member's watch read update** (`readAus`): `watch_read_au` at the cluster's KV names and
at each member's (`kInv_same`). -/
theorem watch_readAus (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames)
    (l : List (List mvcc.Change)) (lb : Nat) (hlb : lb ≤ l.length) :
    kInv γ c g0 γk ∗ ([∗list] sv ∈ c.ms, kInv γ c g0 sv.γr.kv) ∗ monoListLbOwn γ.ch l ⊢
      readAus c γk (watchQ γ c lb) := by
  iintro ⟨#Hinv, #Hinvs, #Hl⟩
  unfold readAus
  isplitr
  · iapply watch_read_au γ c g0 γk l lb hlb
    iframe #
  iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ Hinvs
  iintro !> %i %sv %_ #Hi
  iapply watch_read_au γ c g0 sv.γr.kv l lb hlb
  iframe #

/-- **A watch's commit** (stage E of 7f-6, plan §3 step 5): `lintest`'s update commits the watch's
answer `y` as the model's observation, at etcd's state `σe` at the commit, when every
configuration related to it accepts `y` (`hw`: given the commit state's history past the lower
bound `l` of the changes, its facts and the configuration's relation). -/
theorem watch_commit (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames)
    (x : Input) (y : Output) (hk5 : x.Kind' = W64 5) (hE : y.Err' ≠ W64 4)
    (l : List (List mvcc.Change)) (Φ : val → IProp GF) (P : Prop)
    (hw : ∀ (σe : KVState) (cf : linkv.PCfg HSt Input), l <+: σe.changes → KHistI γ σe →
      kvWfHist c σe → KRelH cf.st σe → cf.st.hist.length = σe.rev → watchOkL x y cf.st = true)
    (hP : ∀ (σe : KVState) (cf : linkv.PCfg HSt Input), l <+: σe.changes → KHistI γ σe →
      kvWfHist c σe → KRelH cf.st σe → cf.st.hist.length = σe.rev → P) :
    kInv γ c g0 γk ∗ linU γ g0 (boxIn x) Φ ∗ monoListLbOwn γ.ch l ⊢
      |={⊤}=> contAt g0 x y Φ ∗ ⌜P⌝ := by
  have HE := drvE_mask_top
  iintro ⟨#Hinv, HU, #Hl⟩
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hrv, %Hpre⟩ := revOwn_lb γ σ l $$ [Hrv Hl]
  · iframe Hrv Hl
  imod revOwn_hist γ σ $$ Hrv with ⟨Hrv, %Hkh, -⟩
  have HPp : P := by
    obtain ⟨cf, -, hst, hlen, -⟩ := Hok.cfg
    exact hP σ cf Hpre Hkh Hok.hwf hst hlen
  obtain ⟨S', HS', Hok'⟩ := kOk_obs Hok x (plainOut y) hk5
    (fun cf _ hst hlen => hw σ cf Hpre Hkh Hok.hwf hst hlen)
  have Hst : (k8setcd3S (GF := GF) g0).M.step S (boxIn x, boxOut y) = some S' := by
    rw [step_box]
    have e : ansOf (plainOut y) = .ok (plainOut y) := by
      unfold ansOf; rw [if_neg (show ¬ (plainOut y).Err' = W64 4 from hE)]
    rw [e]; exact HS'
  imod (fupd_mask_subseteq HE) with Hclose3
  imod (linU_commit γ g0 x _ Φ h S S' Hr Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
  · iframe
  imod Hclose3 with -
  imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
  · inext
    iunfold kInvBody
    iexists _, S', σ, M, nx
    iframe
    ipureintro; exact ⟨run_snoc g0 h S S' _ Hr Hst, Hok'⟩
  imodintro
  iframe HΦ
  ipureintro; exact HPp

/-- **The configurations the model reaches have histories at least the seeded one's** (a step keeps
the history or appends to it). -/
theorem run_hist_ge (g0 : HSt) (h : List github_com.anishathalye.porcupine.OpV)
    (S : linkv.PSet HSt Input)
    (hr : github_com.anishathalye.porcupine.Theory.run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S)
    (cf : linkv.PCfg HSt Input) (hc : S cf) : g0.hist.length ≤ cf.st.hist.length := by
  refine run_inv (kSpec g0) decOp (fun st => g0.hist.length ≤ st.hist.length) ?_ h _ S ?_ hr cf hc
  · intro i st hst
    show g0.hist.length ≤ (kstepL i st).1.hist.length
    have : st.hist.length ≤ (kstepL i st).1.hist.length := by
      unfold kstepL
      split
      · simp
      · unfold advanceL
        split <;> simp_all
    omega
  · intro c' hc'
    simp only [linkv.pInit] at hc'
    subst hc'
    exact Nat.le_refl _

/-- **A lower bound of etcd's changes past the seeded revision** (see the file header): the
invariant's state is related to a configuration the model reached, whose history is at least the
seeded one's. -/
theorem kInv_lb_seed (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames)
    (hg : uint.nat g0.st.rv ≤ g0.hist.length) :
    kInv γ c g0 γk ⊢ |={⊤}=> ∃ l : List (List mvcc.Change), monoListLbOwn γ.ch l ∗
      ⌜uint.nat g0.st.rv ≤ l.length⌝ := by
  have HE := drvE_mask_top
  iintro #Hinv
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  imod revOwn_hist γ σ $$ Hrv with ⟨Hrv, %Hkh, #Hlbσ⟩
  have hrev : σ.rev = σ.changes.length := by unfold KVState.rev; rw [Hkh.1, Nat.zero_add]
  obtain ⟨cf, hcf, -, hlen, -⟩ := Hok.cfg
  have hge := run_hist_ge g0 h S Hr cf hcf
  imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
  · inext
    iunfold kInvBody
    iexists h, S, σ, M, nx
    iframe
    ipureintro; exact ⟨Hr, Hok⟩
  imodintro
  iexists σ.changes
  iframe Hlbσ
  ipureintro; omega

end proofs

end k8s_etcd3
end EtcdGrove
end Perennial
