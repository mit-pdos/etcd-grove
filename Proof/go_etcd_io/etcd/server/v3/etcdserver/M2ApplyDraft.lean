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

/- (#7-cmp's Freeze, 2026-11-02: `kvCrevEntry`, `kvCrevOf` and their laws moved to `KVModelDefs.lean`,
`crevOf` and its laws to `InvRequest.lean`, beside `kvApplied`, which carries `x.crev = crevOf γk A`.) -/

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

/- (`cmpAdmit_of_entry` moved to `ApplyCmpArm.lean`.) -/

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

/- (Stage 4c: `cmpReach` in place, `InvRequest.lean`.) -/

/- (Stage 4c: `cmpReach_of_srvRevLb` moved to `CompactMode.lean`.) -/

/-- **Draft of `reqPropOk`** (`InvRequest.lean`), in the cluster's compaction mode `cmp`: today's
forms (no `irrNoDelPut`: review round 1's F-5, the fork fix's form); or, in compaction mode, a
compaction in M2's scope at a reached revision, its result trivial. -/
def reqPropOkD (γk : KVNames) (cmp : Bool) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) : IProp GF :=
  iprop(reqPropOk γk rq Qr ∨
    (⌜cmp = true ∧ compactPropOk rq ∧ rqShape false rq ∧ irrNoZeroEnd rq ∧
        Qr = fun _ => iprop(True)⌝ ∗
      ∃ r : w64, ⌜rq.compaction = some r⌝ ∗ kvRevLb γk r))

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
