/-
**M2, the apply side: the server's KV model and invariant with compaction (Draft)**
(`notes/m2-apply-plan.md`). Imported by nothing but the apply side's spec Draft; no `axiom`, no
`sorry`; nothing switched. Each `…D` drafts the unsuffixed statement it names (to replace it in
place at the switch: the user's Q6 (a), 2026-10-30); `cmp` stands for the field `KVNames.cmp` the
switch adds (the cluster's compaction mode, one for every member: `srvKVInvs` and `srvReqFieldsAt`
tie each member's `E.cmp` to it). A definition that only carries a redefined one (`entryOk`,
`srvC`, `clusterWorkloadOk`, `isServerReq`, `isServerRead`, `srvBuilt`, the apply-loop specs)
keeps its text and is read under the redefinitions; the Draft copies one only where its own
statements need the new reading (`rqShape`, `entryShapeD`, `logShapeD`, `kvWorkD`: the texts of
`rqShape`, ..., `kvWork` read under item 1's `dispatchOkD`).

- **One KV invariant** (`kvInvD`, M2's round-1 decision "one family"; the user's 2026-10-28 "mode
  as a fact"): the committed entries plain or, in the cluster's compaction mode, compactions in
  M2's scope (`plainLogM`, `compactPropOk`: at a revision `≥ 1`, Q7 (a); no side-effect-free or
  admin field beside it, so `Apply` neither skips nor rejects it); each committed compaction's
  claims at the model of the entries before it (`cmpLogOk`: in M2's scope, its revision one of the
  model's). No `NoDelPutAt` (review round 1's F-5: stated in the fork fix's form; mvcc's specs
  dropped it with item 18, 2026-10-31). At `cmp = false` it means today's `kvInv` (`kvInvD_off`:
a plain log has no compaction, so the shapes read as today's, `logShapeD_plain`).
- **The compaction revision of the committed log** (`crevOf`, Q5 (a): logical across a restore):
  `kvEntry`'s twin (`kvCrevEntry`, `apply.dispatchCrev` per normal entry above the start's
  consistent index), from `-1`; monotone (`crevOf_mono`: the `c ≤ c'` the snapshot track's #8
  needs), `-1` on a plain log, `-1` or at least `1` (`crevOf_pos`: with `recsPos_crev`, #8's corner
  closed, Q7 (a)), and the apply thread's step (`crevOf_step`).
- **The proposal's form** (`reqPropOkD`): today's forms; or, in compaction mode, a compaction in
  M2's scope with a reached revision (`cmpReach`: a KV certificate of a longer log, which
  `kvCertInv` makes a committed model log).
- **The entry's facts at the apply thread** (`cmpEntryOk`, from `cmpLogOk` of a committed log:
  `cmpLogOk_snoc_entry`) give the apply package's `cmpAdmit` (`cmpAdmit_of_entry`) and the scope
  `crevOf_step` needs (`compactPropOk_of_entry`, review round 1's F-4).
- **The shapes under item 1** (`rqShape`, `entryShapeD`, `logShapeD`, `kvWorkD`; review rounds
  2-3's N-1/R3-1): their texts over `apply.dispatchOkD` (a compaction admitted everywhere; the gate
  is `plainLogM`/`cmpEntryOk`); for a plain entry today's (`entryShapeD_plain`, `logShapeD_plain`).
- **The ties of the mode** (`srvReqFieldsAtD`, `srvKVInvsD`; review rounds 1-3's F-3/N-2/R3-2): the
  texts of the request path's and the apply side's KV invariants at the switch, each the KV
  invariant in the server's mode (stood in for by `kvInvD … E.cmp`; at the switch `kvInv ∗
  ⌜γk.cmp = E.cmp⌝`); off, today's (`srvReqFieldsAtD_off`, `srvKVInvsD_off`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactMode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-! ## The requests and entries admitted -/

/- (Stage 4b of the switch, 2026-10-31: in place, `compactPropOk` with M2's scope, `plainEntryM`,
`plainLogM` and their laws (`KVModelDefs.lean`); the shapes' texts are today's, `dispatchOk` being
item 1's since stage 3, so `rqShape`, `entryShapeD`, `logShapeD` and their off laws went.) -/

/-! ## The compaction revision of the committed log -/

/-- **An entry's effect on the compaction revision**, from the consistent index `c₀` with the
chain `ch` (`kvEntry`'s twin): a normal entry with data that decodes is dispatched (`v3` iff above
`c₀`): `apply.dispatchCrev`. -/
def kvCrevEntry (c₀ : w64) (ch : apply.Chain) (crev : Int) (m : EntryModel) : Int :=
  if m.typ = W32 0 then
    if m.data = [] then crev
    else match apply.irrDecode m.data with
      | some rq => apply.dispatchCrev ch rq (decide (uint.Z c₀ < uint.Z m.index)) crev
      | none => crev
  else crev

/-- The compaction revision after the raft log `A`, from `crev₀`. -/
def kvCrevOf (c₀ : w64) (ch : apply.Chain) (crev₀ : Int) (A : List EntryModel) : Int :=
  A.foldl (kvCrevEntry c₀ ch) crev₀

/-- **The compaction revision of the committed log `A`** (Q5 (a): the apply side models it; the
cluster's start store never compacted, `-1`). -/
def crevOf (γk : KVNames) (A : List EntryModel) : Int := kvCrevOf γk.c0 γk.ch0 (-1) A

theorem kvCrevEntry_ge (c₀ : w64) (ch : apply.Chain) (crev : Int) (m : EntryModel) :
    crev ≤ kvCrevEntry c₀ ch crev m := by
  unfold kvCrevEntry
  split
  · split
    · exact Int.le_refl _
    · split
      · exact apply.dispatchCrev_ge _ _ _ _
      · exact Int.le_refl _
  · exact Int.le_refl _

theorem kvCrevOf_ge (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) :
    ∀ crev₀ : Int, crev₀ ≤ kvCrevOf c₀ ch crev₀ A := by
  induction A with
  | nil => intro crev₀; exact Int.le_refl _
  | cons m A ih =>
    intro crev₀
    exact Int.le_trans (kvCrevEntry_ge c₀ ch crev₀ m) (ih (kvCrevEntry c₀ ch crev₀ m))

theorem crevOf_snoc (γk : KVNames) (A : List EntryModel) (m : EntryModel) :
    crevOf γk (A ++ [m]) = kvCrevEntry γk.c0 γk.ch0 (crevOf γk A) m := by
  unfold crevOf kvCrevOf
  rw [List.foldl_append]
  rfl

/-- **The compaction revision never goes down along the committed log** (what the snapshot
track's #8 needs for `Restore.specM`'s `c ≤ c'`: the installer's applied log is a prefix of the
image's). -/
theorem crevOf_mono (γk : KVNames) (A B : List EntryModel) (h : A <+: B) :
    crevOf γk A ≤ crevOf γk B := by
  obtain ⟨C, rfl⟩ := h
  unfold crevOf kvCrevOf
  rw [List.foldl_append]
  exact kvCrevOf_ge _ _ C _

theorem crevOf_ge (γk : KVNames) (A : List EntryModel) : -1 ≤ crevOf γk A :=
  kvCrevOf_ge _ _ A (-1)

/-- A plain entry leaves the compaction revision as it is. -/
theorem kvCrevEntry_plain (c₀ : w64) (ch : apply.Chain) (crev : Int) (m : EntryModel)
    (h : plainEntry m) : kvCrevEntry c₀ ch crev m = crev := by
  unfold kvCrevEntry
  split
  · split
    · rfl
    · rename_i ht hd
      split
      · rename_i rq hrq
        exact apply.dispatchCrev_nonCmp _ _ _ _ (plainReq_nonCmp rq (h ht hd rq hrq))
      · rfl
  · rfl

/-- **A plain log never compacts** (the compaction-off servers' logs: the revision stays `-1`). -/
theorem crevOf_plain (γk : KVNames) (A : List EntryModel) (h : plainLog A) : crevOf γk A = -1 := by
  unfold crevOf kvCrevOf
  generalize hc : (-1 : Int) = c₀
  have key : ∀ (B : List EntryModel), plainLog B → ∀ c, B.foldl (kvCrevEntry γk.c0 γk.ch0) c = c := by
    intro B
    induction B with
    | nil => intro _ c; rfl
    | cons m B ih =>
      intro hB c
      simp only [List.foldl_cons]
      rw [kvCrevEntry_plain _ _ _ _ (hB m (List.mem_cons_self))]
      exact ih (fun m' hm' => hB m' (List.mem_cons_of_mem _ hm')) c
  exact key A h c₀

/-- An admitted entry leaves the compaction revision at `-1` or at least `1` (a compaction in M2's
scope is at a revision `≥ 1`). -/
theorem kvCrevEntry_pos (c₀ : w64) (ch : apply.Chain) (cmp : Bool) (crev : Int) (m : EntryModel)
    (hm : plainEntryM cmp m) (hc : crev = -1 ∨ 1 ≤ crev) :
    kvCrevEntry c₀ ch crev m = -1 ∨ 1 ≤ kvCrevEntry c₀ ch crev m := by
  unfold kvCrevEntry
  split
  · split
    · exact hc
    · rename_i ht hd
      split
      · rename_i rq hrq
        rcases hm ht hd rq hrq with hp | ⟨-, ⟨⟨-, r, hr, h1⟩, -, -⟩⟩
        · rw [apply.dispatchCrev_nonCmp _ _ _ _ (plainReq_nonCmp rq hp)]; exact hc
        · unfold apply.dispatchCrev
          split
          · rw [hr]
            simp only
            unfold apply.cmpRevAfter
            split
            · right; exact h1
            · exact hc
          · exact hc
      · exact hc
  · exact hc

/-- **The compaction revision of an admitted log is `-1` or at least `1`** (Q7 (a)'s scope limit, at
the model: with `mvcc.recsPos_crev` of the image, #8's `c ≤ c'` has no `Compact(0)` corner). -/
theorem crevOf_pos (γk : KVNames) (cmp : Bool) (A : List EntryModel) (h : plainLogM cmp A) :
    crevOf γk A = -1 ∨ 1 ≤ crevOf γk A := by
  unfold crevOf kvCrevOf
  have key : ∀ (B : List EntryModel), plainLogM cmp B → ∀ c : Int, (c = -1 ∨ 1 ≤ c) →
      B.foldl (kvCrevEntry γk.c0 γk.ch0) c = -1 ∨ 1 ≤ B.foldl (kvCrevEntry γk.c0 γk.ch0) c := by
    intro B
    induction B with
    | nil => intro _ c hc; exact hc
    | cons m B ih =>
      intro hB c hc
      simp only [List.foldl_cons]
      exact ih (fun m' hm' => hB m' (List.mem_cons_of_mem _ hm')) _
        (kvCrevEntry_pos _ _ cmp c m (hB m (List.mem_cons_self)) hc)
  exact key A h (-1) (Or.inl rfl)

/-- **The apply thread's step of the compaction revision** (the glue of `applyEntryNormal`'s
compaction arm under the drafted `applyStep`, whose `x'.crev` is `apply.applyCrev`): for a
decoded entry applied by `Apply` with `v3` the model's, at the start's chain, the revision after
`Apply` is the model's after the entry. A compaction is neither skipped nor rejected
(`compactPropOk`); any other kind leaves it. -/
theorem crevOf_step (γk : KVNames) (A : List EntryModel) (m : EntryModel) (rq : apply.IRRModel)
    (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut)
    (hch : x.chain = γk.ch0) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv3 : v3 = decide (uint.Z γk.c0 < uint.Z m.index))
    (hst : apply.applyStep rq v3 x x' out)
    (hok : apply.dispatchKind rq = .compaction → compactPropOk rq) :
    apply.applyCrev rq v3 x.chain (crevOf γk A) out = crevOf γk (A ++ [m]) := by
  rw [crevOf_snoc]
  unfold kvCrevEntry
  simp only [ht, hd, hdec, ↓reduceIte]
  rw [← hv3]
  cases out with
  | dispatched o skip => unfold apply.applyCrev; rw [hch]
  | skipped =>
    unfold apply.applyCrev
    by_cases hk : apply.dispatchKind rq = .compaction
    · have h1 := (hok hk).2.1
      have h2 := hst.1
      rw [h1] at h2; cases h2
    · exact (apply.dispatchCrev_nonCmp _ _ _ _ hk).symm
  | rejected =>
    unfold apply.applyCrev
    by_cases hk : apply.dispatchKind rq = .compaction
    · have h1 := (hok hk).2.2
      have h2 := hst.1
      rw [h1] at h2; cases h2
    · exact (apply.dispatchCrev_nonCmp _ _ _ _ hk).symm

end pure

/-! ## The committed compactions' claims -/

section claims
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- (Stage 4b: `cmpEntryOk`, `cmpLogOk` and their laws in place, `InvRequest.lean`.) -/

/-- **The apply package's `cmpAdmit` from the entry's claims** (the glue at `applyEntryNormal`):
the apply thread's log the model's of the applied log `A` (`kvApplied`), the store compacting in
the cluster's compaction mode (`srvEnvOkD`'s `d.cm = E.cmp`, `envAgree`). -/
theorem cmpAdmit_of_entry (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (kb : Option mvcc.KBReal) (log : mvcc.Log) (hl : log = kvModel γk A)
    (hkb : cmp = true → mvcc.kbCmpM kb) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (h : cmpEntryOk γk cmp A m) :
    apply.cmpAdmit kb log rq := by
  intro hk r hr
  obtain ⟨hc, -, hrl⟩ := h ht hd rq hdec hk
  subst hl
  exact ⟨hkb hc, hrl r hr⟩

/-- **The scope `crevOf_step` needs, from the entry's claims** (review round 1's F-4: its `hok`). -/
theorem compactPropOk_of_entry (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (h : cmpEntryOk γk cmp A m) :
    apply.dispatchKind rq = .compaction → compactPropOk rq :=
  fun hk => (h ht hd rq hdec hk).2.1

/-! ## The KV invariant

(Stage 4b: `kvInv γ γk` is the draft's `kvInvD γ γk γk.cmp` in place, `InvRequest.lean`; `kvWorkD`
is today's `kvWork`, and the off law is `kv_log_plain_off`.) -/

/-! ## The proposal's form -/

/-- **A compaction's revision reached** (persistent): a KV certificate (`kvCert`: the model of a
committed raft log, by `kvCertInv`; or one of the start's two revisions) of a log longer than it.
What `reqPropOkD`'s compaction form carries to the commit, where the KV invariant records the
revision as one of the model before the entry (`cmpLogOk`). The proposer's source (G2, review
round 1's S-2): `srvRevLb E.γ r` (an `idxCert` of the proposer's store) is no `kvCert`; the
closable form is mvcc's "the store's current committed log is `certOk`" (`revMuBody` already
holds `certOk γ log` of its committed log beside the log's authority), exported as a law
`idxCert γ l ⊢ ∃ l', certOk γ l' ∗ ⌜l <+: l'⌝` under the store's invariant: the Probe's (or
round 2's S-2', `store.Read`'s `certOk`). At the commit (review rounds 5-6, item 6): read through
`kvCertInv` (`kv_cert_read`), turned into a lower bound of the server's log
(`srvReqLogLb_of_rlogLb`) before the atomic update, compared inside it by `srvReqLogLb_prefix`. -/
def cmpReach (γk : KVNames) (r : w64) : IProp GF :=
  iprop(∃ l : mvcc.Log, kvCert γk l ∗ ⌜sint.Z r < l.length⌝)

instance cmpReach_persistent (γk : KVNames) (r : w64) : Persistent (cmpReach (GF := GF) γk r) := by
  unfold cmpReach; infer_instance

/-- **G2, the proposer's reach** (Q3's (a'), the user's, 2026-10-31): a revision the server's store has
reached (`srvRevLb`, the compactor's `RevLb` and `EtcdServer.Compact.spec`'s premise) is a
compaction's revision reached (`cmpReach`): the log's `certOk` is a KV certificate, the store's free
one (`0 ↦ []`) excluded by the certificates' invariant (no model log is empty), as in
`kv_cert_read`. -/
theorem cmpReach_of_srvRevLb (γ : ServerRaftNames) (γk : KVNames) (γs : mvcc.StoreNames)
    (hγ : γs.cok = γk.cok) (E : CoPset) (hE : ↑kvcN ⊆ E) (r : w64) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ srvRevLb γs (sint.Z r) ={E}=∗ cmpReach γk r := by
  iintro #Hinv #Hlb
  iunfold srvRevLb at Hlb
  icases Hlb with ⟨%l, -, #Hok, %Hl⟩
  iunfold mvcc.certOk at Hok
  rw [hγ] at *
  icases Hok with (%h | #He | #He)
  · imodintro
    iunfold cmpReach
    iexists l
    isplitr
    · iunfold kvCert; ileft; ipureintro; exact h
    ipureintro; exact Hl
  · imodintro
    iunfold cmpReach
    iexists l
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; exact Hl
  · iunfold kvCertInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hm := ghost_map_lookup $$ HC He
    obtain ⟨-, -, -, A, -, hm⟩ := Hok.1 _ _ Hm
    have h0 := kvRaftOf_extends γk.c0 γk.ch0 γk.log0 A
    unfold kvModel at hm
    rw [hm] at h0
    have := h0.length_le
    simp only [List.length_nil] at this
    omega

/-- **Draft of `reqPropOk`** (`InvRequest.lean`), in the cluster's compaction mode `cmp`: today's
forms (no `irrNoDelPut`: review round 1's F-5, the fork fix's form); or, in compaction mode, a
compaction in M2's scope at a reached revision, its result trivial. -/
def reqPropOkD (γk : KVNames) (cmp : Bool) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop(reqPropOk γk rq Qr ∨
    (⌜cmp = true ∧ compactPropOk rq ∧ rqShape rq ∧ irrNoZeroEnd rq ∧
        Qr = fun _ => iprop(True)⌝ ∗
      ∃ r : w64, ⌜rq.compaction = some r⌝ ∗ cmpReach γk r))

/-- At the mode off, today's. -/
theorem reqPropOkD_off (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    reqPropOkD (GF := GF) γk false rq Qr ⊣⊢ reqPropOk γk rq Qr := by
  unfold reqPropOkD
  constructor
  · iintro (H | ⟨%h, -⟩)
    · iexact H
    · exact absurd h.1 (by decide)
  · iintro H
    ileft
    iexact H

/-! ## The request path's mode

(Stage 4a of the switch, 2026-10-31: the ties are in place, `srvReqFieldsAt`'s `⌜ρ.kv.cmp = E.cmp⌝ ∗
kvCertInv`, `srvReqFieldsAtM`'s `kvTieM`/`kvCertInvM` (`ReqOn.lean`), `srvKVInvs`' `⌜γr.kv.cmp =
E.cmp⌝`; the drafts `srvReqFieldsAtD`, `srvKVInvsD`, `kvTieM` and their off laws went. Their KV
invariant becomes the mode's when `kvInv` is redefined, stage 4b.) -/

end claims

end EtcdGrove
end Perennial
