/-
**M2, the apply side: the server's KV model and invariant with compaction (Draft)**
(`notes/m2-apply-plan.md`). Imported by nothing but the apply side's spec Draft; no `axiom`, no
`sorry`; nothing switched. Each `…D` drafts the unsuffixed statement it names (to replace it in
place at the switch); `cmp` stands for the field `KVNames.cmp` the switch adds (the cluster's
compaction mode, one for every member: `envAgree` ties each member's `E.cmp` to it).

- **One KV invariant** (`kvInvD`, M2's round-1 decision "one family"; the user's 2026-10-28 "mode
  as a fact"): the committed entries plain or, in the cluster's compaction mode, compactions in
  M2's scope (`plainLogM`, `compactPropOkD`: at a revision `≥ 1`, Q7 (a); no side-effect-free or
  admin field beside it, so `Apply` neither skips nor rejects it); each committed compaction's
  claims at the model of the entries before it (`cmpLogOk`: its revision one of the model's, no
  delete-then-put at it); in compaction mode no delete-then-put at any revision of the model (the
  `NoDelPutAt` premise of `store.Compact`, from the admitted writes until the fork takes
  etcd-io/etcd#22377). At `cmp = false` it is today's `kvInv` (`kvInvD_off`).
- **The compaction revision of the committed log** (`crevOf`, Q5 (a): logical across a restore):
  `kvEntry`'s twin (`kvCrevEntry`, `apply.dispatchCrev` per normal entry above the start's
  consistent index), from `-1`; monotone (`crevOf_mono`: the `c ≤ c'` the snapshot track's #8
  needs), `-1` on a plain log, `-1` or at least `1` (`crevOf_pos`: with `recsPos_crev`, #8's corner
  closed, Q7 (a)), and the apply thread's step (`crevOf_step`).
- **The proposal's form** (`reqPropOkD`): today's write forms, each with `irrNoDelPut` in
  compaction mode; or a compaction in M2's scope with a reached revision (`cmpReach`: a KV
  certificate of a longer log, which `kvCertInv` makes a committed model log).
- **The entry's facts at the apply thread** (`cmpEntryOk`, from `cmpLogOk` of a committed log:
  `cmpLogOk_snoc_entry`) give the apply package's `cmpAdmit` (`cmpAdmit_of_entry`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.CompactMode
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.M2ApplyDraft

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

/-- **The request's shape** (draft of `rqShape` over `dispatchOkD`; at the switch `rqShape` itself,
`dispatchOk` being redefined in place). -/
def rqShapeD (rq : apply.IRRModel) : Prop :=
  (∀ on, apply.dispatchOkD on rq) ∧ ∀ log, rqSmall log rq → apply.rqOk log rq

theorem rqShapeD_of (rq : apply.IRRModel) (h : rqShape rq) : rqShapeD rq :=
  ⟨fun on => apply.dispatchOkD_of on rq (h.1 on), h.2⟩

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
compaction mode only, at a revision of the model of `A` (no `ErrFutureRev`), with no
delete-then-put at it (`mvcc.NoDelPutAt`, until etcd-io/etcd#22377 is in the fork). -/
def cmpEntryOk (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    apply.dispatchKind rq = .compaction → cmp = true ∧
      ∀ r, rq.compaction = some r → sint.Z r < (kvModel γk A).length ∧
        mvcc.NoDelPutAt (kvModel γk A) (sint.Z r)

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
  intro hk
  obtain ⟨hc, hr⟩ := h ht hd rq hdec hk
  subst hl
  exact ⟨hkb hc, hr⟩

/-! ## The KV invariant -/

/-- **Draft of `kvInv`** (`InvRequest.lean`), in the cluster's compaction mode `cmp`: today's, its
log plain in the mode (`plainLogM`), its compactions' claims (`cmpLogOk`), and in compaction mode
no delete-then-put at any revision of its model. -/
def kvInvD (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗ ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
    ⌜plainLogM cmp L ∧ cmpLogOk γk cmp L ∧
      (cmp = true → ∀ c, mvcc.NoDelPutAt (kvModel γk L) c) ∧
      srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ []⌝ ∗ kvWork γ.raft γk L)

instance kvInvD_persistent (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool) :
    Persistent (kvInvD (GF := GF) γ γk cmp) := by
  unfold kvInvD; infer_instance

theorem kvInvD_off_pure (γk : KVNames) (L : List EntryModel) (Q : Prop) :
    (plainLogM false L ∧ cmpLogOk γk false L ∧
      (false = true → ∀ c, mvcc.NoDelPutAt (kvModel γk L) c) ∧ Q) ↔ (plainLog L ∧ Q) := by
  rw [plainLogM_false]
  constructor
  · rintro ⟨h1, -, -, h4⟩; exact ⟨h1, h4⟩
  · rintro ⟨h1, h4⟩
    exact ⟨h1, cmpLogOk_plain γk false L h1, fun h => absurd h (by decide), h4⟩

/-- **At the mode off it is today's** (so every compaction-off statement over it reads as today). -/
theorem kvInvD_off (γ : ServerRaftNames) (γk : KVNames) :
    kvInvD (GF := GF) γ γk false = kvInv γ γk := by
  unfold kvInvD kvInv
  simp only [kvInvD_off_pure]

/-! ## The proposal's form -/

/-- **A compaction's revision reached** (persistent): a KV certificate (`kvCert`: the model of a
committed raft log, by `kvCertInv`; or one of the start's two revisions) of a log longer than it.
What `reqPropOkD`'s compaction form carries to the commit, where the KV invariant records the
revision as one of the model before the entry (`cmpLogOk`). -/
def cmpReach (γk : KVNames) (r : w64) : IProp GF :=
  iprop(∃ l : mvcc.Log, kvCert γk l ∗ ⌜sint.Z r < l.length⌝)

instance cmpReach_persistent (γk : KVNames) (r : w64) : Persistent (cmpReach (GF := GF) γk r) := by
  unfold cmpReach; infer_instance

/-- **Draft of `reqPropOk`** (`InvRequest.lean`), in the cluster's compaction mode `cmp`: today's
forms, each, in compaction mode, deleting no key it puts again in its revision (`irrNoDelPut`: the
`NoDelPutAt` the invariant keeps; a put and a delete meet it by their kind, a transaction by the
`Txn` caller's premise, until the fork takes etcd-io/etcd#22377); or, in compaction mode, a
compaction in M2's scope at a reached revision, its result trivial. -/
def reqPropOkD (γk : KVNames) (cmp : Bool) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop((reqPropOk γk rq Qr ∗ ⌜cmp = true → irrNoDelPut rq⌝) ∨
    (⌜cmp = true ∧ compactPropOkD rq ∧ rqShapeD rq ∧ irrNoZeroEnd rq ∧
        Qr = fun _ => iprop(True)⌝ ∗
      ∃ r : w64, ⌜rq.compaction = some r⌝ ∗ cmpReach γk r))

/-- At the mode off, today's. -/
theorem reqPropOkD_off (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    reqPropOkD (GF := GF) γk false rq Qr ⊣⊢ reqPropOk γk rq Qr := by
  unfold reqPropOkD
  constructor
  · iintro (⟨H, -⟩ | ⟨%h, -⟩)
    · iexact H
    · exact absurd h.1 (by decide)
  · iintro H
    ileft
    iframe H
    ipureintro; intro h; exact absurd h (by decide)

end claims

end EtcdGrove
end Perennial
