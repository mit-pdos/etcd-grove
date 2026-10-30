/-
**M2, the apply side: the server's KV model and invariant with compaction (Draft)**
(`notes/m2-apply-plan.md`). Imported by nothing but the apply side's spec Draft; no `axiom`, no
`sorry`; nothing switched. Each `…D` drafts the unsuffixed statement it names (to replace it in
place at the switch: the user's Q6 (a), 2026-10-30); `cmp` stands for the field `KVNames.cmp` the
switch adds (the cluster's compaction mode, one for every member: `srvKVInvs` and `srvReqFieldsAt`
tie each member's `E.cmp` to it). A definition that only carries a redefined one (`entryOk`,
`srvC`, `clusterWorkloadOk`, `isServerReq`, `isServerRead`, `srvBuilt`, the apply-loop specs)
keeps its text and is read under the redefinitions; the Draft copies one only where its own
statements need the new reading (`rqShapeD`, `entryShapeD`, `logShapeD`, `kvWorkD`: the texts of
`rqShape`, ..., `kvWork` read under item 1's `dispatchOkD`).

- **One KV invariant** (`kvInvD`, M2's round-1 decision "one family"; the user's 2026-10-28 "mode
  as a fact"): the committed entries plain or, in the cluster's compaction mode, compactions in
  M2's scope (`plainLogM`, `compactPropOkD`: at a revision `≥ 1`, Q7 (a); no side-effect-free or
  admin field beside it, so `Apply` neither skips nor rejects it); each committed compaction's
  claims at the model of the entries before it (`cmpLogOk`: in M2's scope, its revision one of the
  model's). No `NoDelPutAt` (review round 1's F-5: stated in the fork fix's form; the switch waits
  for mvcc's specs to drop the premise). At `cmp = false` it means today's `kvInv` (`kvInvD_off`:
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
  `crevOf_step` needs (`compactPropOkD_of_entry`, review round 1's F-4).
- **The shapes under item 1** (`rqShapeD`, `entryShapeD`, `logShapeD`, `kvWorkD`; review rounds
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

/-- **A compaction in M2's scope, as the model takes it**: `compactPropOk` (the kind, a revision
`≥ 1`), with no side-effect-free field (`Apply` would skip it without a waiter) and no admin field
(the auth layer's admin check would reject it) beside it: so `Apply` dispatches it on every member,
and the model's `kvCrevEntry` (which ignores skipping, as `kvEntry` does) is exact. `Compact`'s
request has nothing else set. -/
def compactPropOkD (rq : apply.IRRModel) : Prop :=
  compactPropOk rq ∧ apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false

theorem compactPropOkD_irrCompaction (rev : w64) (h : 1 ≤ sint.Z rev) :
    compactPropOkD (irrCompaction rev) :=
  ⟨compactPropOk_irrCompaction rev h, by rfl, by rfl⟩

/-- **A plain entry in the mode `cmp`** (draft of `plainEntry`, by the cluster's mode): a plain
request, or, in compaction mode, a compaction in M2's scope. -/
def plainEntryM (cmp : Bool) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    plainReq rq ∨ (cmp = true ∧ compactPropOkD rq)

def plainLogM (cmp : Bool) (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntryM cmp m

theorem plainEntryM_false (m : EntryModel) : plainEntryM false m ↔ plainEntry m := by
  unfold plainEntryM plainEntry
  simp

theorem plainLogM_false (A : List EntryModel) : plainLogM false A ↔ plainLog A := by
  unfold plainLogM plainLog
  simp only [plainEntryM_false]

/-- A plain request is no compaction. -/
theorem plainReq_nonCmp (rq : apply.IRRModel) (h : plainReq rq) :
    apply.dispatchKind rq ≠ .compaction := by
  intro hk
  have := h.2
  rw [hk] at this
  simp [putgetKind] at this

/-- **`rqShape` under item 1** (its text over `apply.dispatchOkD`: a compaction admitted; `rqOk`
of a compaction is `True`). -/
def rqShapeD (rq : apply.IRRModel) : Prop :=
  (∀ on, apply.dispatchOkD on rq) ∧ ∀ log, rqSmall log rq → apply.rqOk log rq

theorem rqShapeD_of (rq : apply.IRRModel) (h : rqShape rq) : rqShapeD rq :=
  ⟨fun on => apply.dispatchOkD_of on rq (h.1 on), h.2⟩

/-- For a request that is no compaction, today's. -/
theorem rqShapeD_iff (rq : apply.IRRModel) (h : apply.dispatchKind rq ≠ .compaction) :
    rqShapeD rq ↔ rqShape rq := by
  unfold rqShapeD rqShape
  simp only [apply.dispatchOkD_iff _ rq h]

/-- **`entryShape` under item 1.** -/
def entryShapeD (m : EntryModel) : Prop :=
  (m.typ = W32 0 → m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧
      (∃ id, apply.irrId rq = some id) ∧ rqShapeD rq) ∧
    (m.typ ≠ W32 0 → ccIdOf m.data = W64 0)

/-- **For a plain entry, today's** (the off law). -/
theorem entryShapeD_plain (m : EntryModel) (hp : plainEntry m) : entryShapeD m ↔ entryShape m := by
  unfold entryShapeD entryShape
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun ht => ?_, h2⟩
    rcases h1 ht with hd | ⟨rq, hdec, hid, hs⟩
    · exact Or.inl hd
    · by_cases hd : m.data = []
      · exact Or.inl hd
      · exact Or.inr ⟨rq, hdec, hid,
          (rqShapeD_iff rq (plainReq_nonCmp rq (hp ht hd rq hdec))).1 hs⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun ht => ?_, h2⟩
    rcases h1 ht with hd | ⟨rq, hdec, hid, hs⟩
    · exact Or.inl hd
    · exact Or.inr ⟨rq, hdec, hid, rqShapeD_of rq hs⟩

/-- **`logShape` under item 1.** -/
def logShapeD (L : List EntryModel) : Prop := ∀ m ∈ L, entryShapeD m

theorem logShapeD_plain (L : List EntryModel) (hp : plainLog L) : logShapeD L ↔ logShape L := by
  unfold logShapeD logShape
  exact ⟨fun h m hm => (entryShapeD_plain m (hp m hm)).1 (h m hm),
    fun h m hm => (entryShapeD_plain m (hp m hm)).2 (h m hm)⟩

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
(`compactPropOkD`); any other kind leaves it. -/
theorem crevOf_step (γk : KVNames) (A : List EntryModel) (m : EntryModel) (rq : apply.IRRModel)
    (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut)
    (hch : x.chain = γk.ch0) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv3 : v3 = decide (uint.Z γk.c0 < uint.Z m.index))
    (hst : apply.applyStep rq v3 x x' out)
    (hok : apply.dispatchKind rq = .compaction → compactPropOkD rq) :
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

/-- **What a committed compaction entry `m` after the log `A` claims** (pure): in the cluster's
compaction mode only, in M2's scope (`compactPropOkD`: neither skipped nor rejected by `Apply`, so
the apply thread's revision is the model's, `crevOf_step`; review round 1's F-4), at a revision of
the model of `A` (no `ErrFutureRev`). No `NoDelPutAt` (F-5: the fork fix's form). -/
def cmpEntryOk (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    apply.dispatchKind rq = .compaction → cmp = true ∧ compactPropOkD rq ∧
      ∀ r, rq.compaction = some r → sint.Z r < (kvModel γk A).length

/-- **Every compaction of `L` claims at the model before it.** -/
def cmpLogOk (γk : KVNames) (cmp : Bool) (L : List EntryModel) : Prop :=
  ∀ (i : Nat) (m : EntryModel), L[i]? = some m → cmpEntryOk γk cmp (L.take i) m

theorem cmpLogOk_snoc_entry (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel)
    (h : cmpLogOk γk cmp (A ++ [m])) : cmpEntryOk γk cmp A m := by
  have := h A.length m (by simp)
  simpa using this

theorem cmpLogOk_prefix (γk : KVNames) (cmp : Bool) (A L : List EntryModel)
    (h : cmpLogOk γk cmp L) (hp : A <+: L) : cmpLogOk γk cmp A := by
  obtain ⟨C, rfl⟩ := hp
  intro i m hi
  have hlt : i < A.length := by
    rcases (List.getElem?_eq_some_iff.1 hi) with ⟨hl, -⟩; exact hl
  have := h i m (by rw [List.getElem?_append_left hlt]; exact hi)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at this

/-- A plain log has no compaction, so its claims hold in either mode. -/
theorem cmpLogOk_plain (γk : KVNames) (cmp : Bool) (L : List EntryModel) (h : plainLog L) :
    cmpLogOk γk cmp L := by
  intro i m hi ht hd rq hrq hk
  exact absurd hk (plainReq_nonCmp rq (h m (List.mem_of_getElem? hi) ht hd rq hrq))

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
theorem compactPropOkD_of_entry (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (h : cmpEntryOk γk cmp A m) :
    apply.dispatchKind rq = .compaction → compactPropOkD rq :=
  fun hk => (h ht hd rq hdec hk).2.1

/-! ## The KV invariant -/

/-- **`kvWork` under item 1** (over `logShapeD`, so a compaction entry has a shape). -/
def kvWorkD (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) : IProp GF :=
  iprop(⌜logShapeD L ∧ ccLogOk cfg L⌝ ∗ [∗list] m ∈ L, entryClaim γk.ids m)

instance kvWorkD_persistent (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) :
    Persistent (kvWorkD (GF := GF) cfg γk L) := by
  unfold kvWorkD; infer_instance

/-- **Draft of `kvInv`** (`InvRequest.lean`), in the cluster's compaction mode `cmp`: today's, its
log plain in the mode (`plainLogM`), its compactions' claims (`cmpLogOk`), its work by the mode
(`kvWork` under item 1, `kvWorkD`). -/
def kvInvD (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗ ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
    ⌜plainLogM cmp L ∧ srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ [] ∧ cmpLogOk γk cmp L⌝ ∗
      kvWorkD γ.raft γk L)

instance kvInvD_persistent (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool) :
    Persistent (kvInvD (GF := GF) γ γk cmp) := by
  unfold kvInvD; infer_instance

/-- (The claims last, review round 4: the proofs that read today's conjuncts by position keep
their indices.) -/
theorem kvInvD_off_pure (γk : KVNames) (L : List EntryModel) (A B C D : Prop) :
    (plainLogM false L ∧ A ∧ B ∧ C ∧ D ∧ cmpLogOk γk false L) ↔ (plainLog L ∧ A ∧ B ∧ C ∧ D) := by
  rw [plainLogM_false]
  constructor
  · rintro ⟨h1, ha, hb, hc, hd, -⟩; exact ⟨h1, ha, hb, hc, hd⟩
  · rintro ⟨h1, ha, hb, hc, hd⟩
    exact ⟨h1, ha, hb, hc, hd, cmpLogOk_plain γk false L h1⟩

/-- **At the mode off it is today's** (the off law: a plain log has no compaction, so its shapes
read as today's; every compaction-off statement over it means what it meant). -/
theorem kvInvD_off (γ : ServerRaftNames) (γk : KVNames) :
    kvInvD (GF := GF) γ γk false ⊣⊢ kvInv γ γk := by
  unfold kvInvD kvInv
  simp only [kvInvD_off_pure]
  constructor
  · iintro #H
    iapply inv_iff $$ H
    inext; imodintro
    unfold iff
    isplit
    · iintro ⟨%L, H1, H2, %hp, Hw⟩
      iunfold kvWorkD at Hw
      icases Hw with ⟨%hs, Hc⟩
      iexists L; iframe H1 H2
      iunfold kvWork; iframe Hc
      ipureintro
      exact ⟨hp, (logShapeD_plain L hp.1).1 hs.1, hs.2⟩
    · iintro ⟨%L, H1, H2, %hp, Hw⟩
      iunfold kvWork at Hw
      icases Hw with ⟨%hs, Hc⟩
      iexists L; iframe H1 H2
      iunfold kvWorkD; iframe Hc
      ipureintro
      exact ⟨hp, (logShapeD_plain L hp.1).2 hs.1, hs.2⟩
  · iintro #H
    iapply inv_iff $$ H
    inext; imodintro
    unfold iff
    isplit
    · iintro ⟨%L, H1, H2, %hp, Hw⟩
      iunfold kvWork at Hw
      icases Hw with ⟨%hs, Hc⟩
      iexists L; iframe H1 H2
      iunfold kvWorkD; iframe Hc
      ipureintro
      exact ⟨hp, (logShapeD_plain L hp.1).2 hs.1, hs.2⟩
    · iintro ⟨%L, H1, H2, %hp, Hw⟩
      iunfold kvWorkD at Hw
      icases Hw with ⟨%hs, Hc⟩
      iexists L; iframe H1 H2
      iunfold kvWork; iframe Hc
      ipureintro
      exact ⟨hp, (logShapeD_plain L hp.1).1 hs.1, hs.2⟩

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

/-- **Draft of `reqPropOk`** (`InvRequest.lean`), in the cluster's compaction mode `cmp`: today's
forms (no `irrNoDelPut`: review round 1's F-5, the fork fix's form); or, in compaction mode, a
compaction in M2's scope at a reached revision, its result trivial. -/
def reqPropOkD (γk : KVNames) (cmp : Bool) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop(reqPropOk γk rq Qr ∨
    (⌜cmp = true ∧ compactPropOkD rq ∧ rqShapeD rq ∧ irrNoZeroEnd rq ∧
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

/-! ## The request path's mode -/

/-- **Draft of `srvReqFieldsAt`** (`InvProposer.lean`; review round 1's F-3, round 2's N-2): today's
with the KV invariant in the server's compaction mode, `kvInvD ρ.raft ρ.kv E.cmp`, in place of
`kvInv ρ.raft ρ.kv` (one invariant: a second copy beside the off one could not be allocated, each
owning half of `srvRLog`), and the certificates' invariant `kvCertInv` (review round 5's F5-1: the
commit step reads a compaction's `cmpReach` through it, `kv_cert_read`, before the atomic update;
`start` has it from `srvKVInvs`). At the switch `kvInv` is `kvInvD … ρ.kv.cmp` (item 5) and this conjunct
is `kvInv ρ.raft ρ.kv ∗ ⌜ρ.kv.cmp = E.cmp⌝` (item 19), made by `NewServer` from its
`ρ.rd.kv.cmp = E₀.cmp` and `envAgree`. -/
def srvReqFieldsAtD (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) : IProp GF :=
  iprop(structFieldRef EtcdServer go!"reqIDGen" s ↦□ v.gen ∗ idGen ρ.ids v.gen (srvFloorFact E) ∗
    structFieldRef EtcdServer go!"w" s ↦□ v.w ∗ waitInv v.w ρ E ∗
    srvRaftNode s ρ.raft ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ v.maxReq ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ v.fg ∗ isFeatureGate v.fg ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ v.cca ∗
    srvCfgFieldAddr s go!"ElectionTicks" ↦□ v.electionTicks ∗
    srvCfgFieldAddr s go!"TickMs" ↦□ v.tickMs ∗
    structFieldRef EtcdServer go!"authStore" s ↦□ v.auth ∗ isReqAuth v.auth E.RD ∗
    structFieldRef EtcdServer go!"done" s ↦□ v.done ∗ srvDoneChan v.done ∗
    structFieldRef EtcdServer go!"memberID" s ↦□ v.memberID ∗
    srvAtomicU64 (structFieldRef EtcdServer go!"lead" s) ∗
    structFieldRef EtcdServer go!"cluster" s ↦□ v.cluster ∗
    structFieldRef raftNodeConfig go!"transport"
      (structFieldRef raftNode go!"raftNodeConfig" (structFieldRef EtcdServer go!"r" s)) ↦□ v.tr ∗
    srvPeersOk v.cluster v.cid v.tr ∗
    srvIndexInvs s E ∗
    srvMintInv ρ ∗ kvInvD ρ.raft ρ.kv E.cmp ∗ kvCertInv ρ.raft ρ.kv ∗
    ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

/-- **Off, today's with the certificates' invariant** (item 19 adds `kvCertInv`, review round 5's
F5-1: the commit step compares a compaction's reached revision with the committed log). -/
theorem srvReqFieldsAtD_off (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields)
    (h : E.cmp = false) :
    srvReqFieldsAtD (GF := GF) s E ρ v ⊣⊢ srvReqFieldsAt s E ρ v ∗ kvCertInv ρ.raft ρ.kv := by
  unfold srvReqFieldsAtD srvReqFieldsAt
  rw [h]
  constructor
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, Hkv, Hci, Hc⟩
    iframe
    iapply (kvInvD_off ρ.raft ρ.kv).1 $$ Hkv
  · iintro ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, Hkv, Hc⟩, Hci⟩
    iframe
    iapply (kvInvD_off ρ.raft ρ.kv).2 $$ Hkv

/-- **The tie by the auth mode** (review round 6's R6-1, item 19): the KV names' compaction mode
the server's with auth off; nothing with auth on (auth-on servers keep retention `0` and the auth
mode's own vocabulary excludes a compaction, so no consumer reads it there, and `start.specOn`
has no producer for it). `srvReqFieldsAtM on` carries `kvTieM on γk E` (both `rfl` laws kept; no
auth-on text touched). `cmp` stands for `KVNames.cmp` until the switch adds the field. -/
def kvTieM (on : Bool) (cmp : Bool) (E : apply.AEnv GF) : Prop :=
  match on with
  | false => cmp = E.cmp
  | true => True

theorem kvTieM_off (cmp : Bool) (E : apply.AEnv GF) : kvTieM (GF := GF) false cmp E = (cmp = E.cmp) :=
  rfl

/-- **Draft of `srvKVInvs`** (`InvApplier.lean`; review round 3's R3-2, item 19): the apply side's
and the readers' KV invariants (`isServerRead`, `srvBuilt`, `isServer(M)` carry it), today's with
the KV invariant in the server's mode, `kvInvD γr.raft γr.kv E.cmp` (at the switch `kvInv γr.raft
γr.kv ∗ ⌜γr.kv.cmp = E.cmp⌝`: the tie of the apply side's `E.cmp` to the invariant's mode). -/
def srvKVInvsD (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(kvInvD γr.raft γr.kv E.cmp ∗ kvCertInv γr.raft γr.kv ∗ srvRaftLogInv γr.raft ∗
    ⌜E.γ.cok = γr.kv.cok⌝)

theorem srvKVInvsD_off (E : apply.AEnv GF) (γr : ReadNames) (h : E.cmp = false) :
    srvKVInvsD (GF := GF) E γr ⊣⊢ srvKVInvs E γr := by
  unfold srvKVInvsD srvKVInvs
  rw [h]
  constructor
  · iintro ⟨Hkv, H2, H3, H4⟩
    iframe
    iapply (kvInvD_off γr.raft γr.kv).1 $$ Hkv
  · iintro ⟨Hkv, H2, H3, H4⟩
    iframe
    iapply (kvInvD_off γr.raft γr.kv).2 $$ Hkv

end claims

end EtcdGrove
end Perennial
