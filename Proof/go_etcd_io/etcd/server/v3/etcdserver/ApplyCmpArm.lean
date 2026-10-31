/-
**The apply thread's compaction arm** (M2's apply side, 2026-10-31, the user's (a): the snapshot
track's `srvEnvOkD` in place, so a compaction entry reaches `applyEntryNormal` in the cluster's
compaction mode). The facts `applyEntryNormal`'s proof needs of a committed entry that is a covered
request or a compaction in M2's scope (`plainOrCmp`): the certificates `Apply` asks
(`kv_certPre_M`), the rest buckets after it (`srvRest_apply_M`), the KV state after it
(`batchStep_plainM`), its result's error not `ErrNoSpace`'s at the start's chain
(`applyResultIs_notNoSpace_M`); and a compaction's facts (`cmpAdmit`) from the KV invariant's claims
(`kv_entry_claim`, S3-3's transfer, `cmpEntryOk_transfer`; `cmpAdmit_of_entry`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A covered request or a compaction in M2's scope**: what a committed entry plain in the mode
decodes to. -/
def plainOrCmp (rq : apply.IRRModel) : Prop := plainCover rq ∨ compactPropOk rq

theorem plainOrCmp_of_entryM (cmp : Bool) (m : EntryModel) (h : plainEntryM cmp m)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (rq : apply.IRRModel)
    (hdec : apply.irrDecode m.data = some rq) : plainOrCmp rq := by
  rcases h ht hd rq hdec with h | ⟨-, h⟩
  · exact Or.inl h.1
  · exact Or.inr h

/-- Neither skipped nor rejected: `Apply`'s rest-bucket effect is `dispatch`'s. -/
theorem restOut_plainOrCmp (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (r : apply.RestM) (hp : plainOrCmp rq)
    (h : apply.applyStep rq v3 x x' out) :
    apply.restOut rq v3 out r = apply.restAfter rq v3 r := by
  rcases hp with hp | hc
  · exact restOut_plain rq v3 x x' out r hp h
  · cases out with
    | skipped => exact absurd h.1 (by rw [hc.2.1]; decide)
    | rejected => exact absurd h.1 (by rw [hc.2.2]; decide)
    | dispatched o skip => rfl

/-- **`Apply` on a compaction keeps the chain and the KV's log.** -/
theorem applyStep_cmp (rq : apply.IRRModel) (hc : compactPropOk rq) (v3 : Bool)
    (x x' : apply.ApplyKV) (out : apply.ApplyOut) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧ x'.log = x.log := by
  have hk := hc.1.1
  cases out with
  | skipped => rw [h.2]; exact ⟨rfl, rfl⟩
  | rejected => rw [h.2]; exact ⟨rfl, rfl⟩
  | dispatched o skip =>
    obtain ⟨-, hd, hl, hch, -⟩ := h
    refine ⟨?_, ?_⟩
    · rcases hch with h | ⟨-, hka, -⟩
      · exact h
      · rw [hk] at hka; cases hka
    · rw [hl]
      unfold apply.dispatchStep at hd
      simp only [hk, apply.preV3Kind, apply.storeKind, Bool.false_eq_true, _root_.false_or,
        ↓reduceIte] at hd
      split at hd
      · rw [hd]; rfl
      · exact apply.chainStep_cmp_log rq hk hc.2.2 x.log x.chain o hd

/-- A compaction entry leaves the model's log. -/
theorem kvEntry_cmp (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (hc : compactPropOk rq) : kvEntry c₀ ch lt log m = log :=
  kvEntry_nonwrite _ _ _ _ m (Or.inr (Or.inr fun rq' h => by
    rw [hdec] at h; cases h; exact compactPropOk_nonwrite rq hc))

/-- **A raft entry's step on an entry plain in the mode**, at a `kvExact` chain: the chain
unchanged and the log as `kvEntry` says (a compaction: unchanged). -/
theorem batchStep_plainM (c₀ : w64) (lt : LeaseTable) (cmp : Bool) (m : EntryModel)
    (x x' : apply.ApplyKV) (hp : plainEntryM cmp m) (hoff : x.chain.kvExact = true)
    (h : batchStep c₀ m x x') :
    x'.chain = x.chain ∧ x'.log = kvEntry c₀ x.chain lt x.log m := by
  by_cases hcm : ∃ rq, m.typ = W32 0 ∧ m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧
      compactPropOk rq
  · obtain ⟨rq, ht, hd, hdec, hc⟩ := hcm
    rw [kvEntry_cmp c₀ x.chain lt x.log m rq hdec hc]
    unfold batchStep at h
    rw [if_pos ht] at h
    obtain ⟨out, h⟩ := h
    unfold entryStep at h
    rw [if_neg hd] at h
    obtain ⟨rq', id, hdec', -, h⟩ := h
    rw [hdec] at hdec'
    cases hdec'
    exact applyStep_cmp rq hc _ x x' out h
  · have hpl : plainEntry m := by
      intro ht hd rq hdec
      rcases hp ht hd rq hdec with h | ⟨-, hc⟩
      · exact h
      · exact absurd ⟨rq, ht, hd, hdec, hc⟩ hcm
    exact batchStep_plain c₀ lt m x x' hpl hoff h

/-- **A compaction dispatched at the start's chain is applied** (the chain reaches the backend). -/
theorem dispatchStep_start_cmp (rq : apply.IRRModel) (hc : compactPropOk rq) (log : mvcc.Log)
    (o : apply.Outcome) (h : apply.dispatchStep (apply.alarmChain false false false) rq true log o) :
    o = .applied log false := by
  have hk := hc.1.1
  have hna := hc.2.2
  unfold apply.dispatchStep at h
  simp only [hk, apply.preV3Kind, apply.storeKind, Bool.false_eq_true, _root_.false_or,
    _root_.or_false, ↓reduceIte] at h
  simp [apply.alarmChain, apply.baseChain, apply.chainStep, apply.authChecks, apply.cappedRejects,
    apply.corruptRejects, apply.backendStep, hk, hna] at h
  exact h

/-- **The transfer (S3-3, item 8), pure**: a committed log `A ++ [m]` whose requested entries are
a prefix of the server's log `L`'s (no fillers in `L`) gets the entry's claim from `L`'s claims:
`m`, if a compaction, is one of `L`'s entries, at the position after the prefix `A'` of `L` with
`A`'s requested entries, and the model of `A'` is `A`'s (`kvModel_eqv`). -/
theorem cmpEntryOk_transfer (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool)
    (A L : List EntryModel) (m : EntryModel)
    (hAm : srvIdxOkW γ.ai0 (A ++ [m])) (hL : srvIdxOkW γ.ai0 L)
    (hnf : ∀ e ∈ L, ¬ e.toLE.isFiller ∧ ¬ e.toLE.isEmptyV2)
    (h : opsOf ((A ++ [m]).map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) (hcl : cmpLogOk γk cmp L) :
    cmpEntryOk γk cmp A m := by
  intro ht hd rq hdec hk
  have hA : srvIdxOkW γ.ai0 A := srvIdxOkW_prefix _ A _ hAm (List.prefix_append _ _)
  have hf : ¬ m.toLE.isFiller := fun hf => hd hf.1
  have hv : ¬ m.toLE.isEmptyV2 := fun hv => by
    have h2 : m.typ = W32 2 := hv.2
    rw [ht] at h2; exact absurd h2 (by decide)
  have hops : opsOf ((A ++ [m]).map EntryModel.toLE) =
      opsOf (A.map EntryModel.toLE) ++ [m.toLE] := by
    rw [List.map_append, opsOf_append]
    simp [opsOf, hf, hv]
  rw [hops] at h
  -- the prefix of `L` with `A`'s requested entries, and the entry after it
  obtain ⟨A', hA'L, hAA'⟩ := srv_eqv_prefix γ A L hA hL hnf
    ((List.prefix_append _ _).trans h)
  have hA'nf : ∀ x ∈ A'.map EntryModel.toLE, ¬ x.isFiller ∧ ¬ x.isEmptyV2 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hnf y (hA'L.subset hy)
  have hlen : (opsOf (A.map EntryModel.toLE)).length = A'.length := by
    rw [hAA'.2.2, opsOf_nofill _ hA'nf, List.length_map]
  have hA'eq : A' = L.take A'.length := List.prefix_iff_eq_take.1 hA'L
  obtain ⟨t, htl⟩ := h
  have hget : (L.map EntryModel.toLE)[A'.length]? = some m.toLE := by
    rw [← htl, List.append_assoc, List.getElem?_append_right (by omega), ← hlen, Nat.sub_self]
    rfl
  rw [List.getElem?_map, Option.map_eq_some_iff] at hget
  obtain ⟨m', hm', he⟩ := hget
  have h1 := congrArg LogEntry.type he
  have h2 := congrArg LogEntry.data he
  simp only [EntryModel.toLE] at h1 h2
  have := hcl A'.length m' hm' (h1 ▸ ht) (h2 ▸ hd) rq (h2 ▸ hdec) hk
  rw [← hA'eq, ← (kvModel_eqv γ γk A A' hAA' hc).1] at this
  exact this


end pure

section arm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The certificates `Apply` asks of an entry's request**, covered or a compaction (whose
outcomes keep the log, certified as the entry's model log). -/
theorem kv_certPre_M (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (lt : LeaseTable) (x : apply.ApplyKV) (m : EntryModel) (rq : apply.IRRModel) (v3 : Bool)
    (hp : plainOrCmp rq) (hoff : x.chain.kvExact = true) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : v3 = decide (uint.Z c₀ < uint.Z m.index)) :
    kvCert (GF := GF) γk (kvEntry c₀ x.chain lt x.log m) ⊢ apply.certPreV v3 E x.chain rq x.log := by
  rcases hp with hp | hc
  · exact kv_certPre E γk hγ c₀ lt x m rq v3 hp hoff ht hd hdec hv
  rw [kvEntry_cmp c₀ x.chain lt x.log m rq hdec hc]
  iintro #Hc
  cases v3
  · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [apply.certPreV, ↓reduceIte]
    unfold apply.certPre
    imodintro
    iintro %oc %hs
    rw [apply.chainStep_cmp_log rq hc.1.1 hc.2.2 x.log x.chain oc hs]
    iapply kvCert_certOk γk E.γ hγ $$ Hc

/-- **The rest buckets after an entry's request**, covered or a compaction. -/
theorem srvRest_apply_M (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hp : plainOrCmp rq)
    (hs : apply.applyStep rq v3 x x' out) :
    E.RO (apply.restOut rq v3 out (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) =
      srvRest E γr (A ++ [m]) := by
  rw [srvRest_snoc, restEntry_normal _ _ rq _ ht hd hdec, restOut_plainOrCmp rq v3 x x' out _ hp hs,
    hv3]

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


/-- **The transfer (S3-3, item 8)**: an entry `m` of the committed log after `A` (a lower bound of
it, as `applyEntryNormal`'s proof holds) gets its claim from the KV invariant's, at the invariant's
mode. At `⊤`, as `kv_log_plain`. -/
theorem kv_entry_claim (γ : ServerRaftNames) (γk : KVNames)
    (A : List EntryModel) (m : EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ (A ++ [m]) ={⊤}=∗
      ⌜cmpEntryOk γk γk.cmp A m⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L (A ++ [m]) $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ (A ++ [m]) $$ HB
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  obtain ⟨-, -, hc0, -, -, hcl⟩ := Hok
  exact cmpEntryOk_transfer γ γk γk.cmp A L m HBi Hp.1 Hp.2.1 Hp.2.2 hc0 hcl


end arm

section nospace
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A compaction's answer at the backend's outcome is not `ErrNoSpace`'s** (given back): `nil`,
or mvcc's `ErrCompacted` (apart from `ErrNoSpace`, `applyErrVars`); the corrupt applier's
`ErrCorrupt` comes only with its rejection. -/
theorem dispatchAnswer_notNoSpace_cmp (rq : apply.IRRModel) (log : mvcc.Log) (skip : Bool)
    (resp err : GoInterface) (tr : Loc) (o : apply.Outcome) (log' : mvcc.Log)
    (hk : apply.dispatchKind rq = .compaction) (ho : o = .applied log' false) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.dispatchAnswer rq log skip resp err tr o -∗
      apply.dispatchAnswer rq log skip resp err tr o ∗ notNoSpaceErr err := by
  unfold apply.dispatchAnswer
  simp only [hk]
  iintro #Hv H
  icases Hv with ⟨-, -, -, -, -, #HC, -, -, -, #AC, -⟩
  icases H with ⟨%rp, %hrp, (⟨%he, Hok⟩ | ⟨%h3, (#HeC | ⟨%hoc, -⟩)⟩)⟩
  · isplitl
    · iexists rp
      isplitr
      · ipureintro; exact hrp
      ileft; iframe Hok; ipureintro; exact he
    rw [he]; iunfold notNoSpaceErr; ileft; ipureintro; rfl
  · isplitl
    · iexists rp
      isplitr
      · ipureintro; exact hrp
      iright
      isplitr
      · ipureintro; exact h3
      ileft; iexact HeC
    iunfold txn.errVarIs at HeC
    iapply errVarIs_notNoSpace _ _ $$ HC AC HeC
  · subst ho; cases hoc

/-- **`apply.Apply`'s result at the start's chain** (given back), for a covered request or a
compaction: `nil`, or its `Err` is not `ErrNoSpace`'s. -/
theorem applyResultIs_notNoSpace_M (rq : apply.IRRModel) (x x' : apply.ApplyKV) (ar : Loc)
    (out : apply.ApplyOut) (hp : plainOrCmp rq)
    (hch : x.chain = apply.alarmChain false false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.applyResultIs rq true x.log ar out -∗
      apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  rcases hp with hp | hc
  · exact applyResultIs_notNoSpace rq x x' ar out hp hch hs
  iintro #Hv H
  cases out with
  | skipped => exact absurd hs.1 (by rw [hc.2.1]; decide)
  | rejected => exact absurd hs.1 (by rw [hc.2.2]; decide)
  | dispatched o skip =>
    obtain ⟨-, hd, -, -⟩ := hs
    rw [hch] at hd
    have ho := dispatchStep_start_cmp rq hc x.log o hd
    simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    ihave ⟨Hans, #Hn⟩ := dispatchAnswer_notNoSpace_cmp rq x.log skip v.Resp' v.Err' v.Trace' o x.log
      hc.1.1 ho $$ Hv Hans
    isplitl [Hans]
    · isplitr
      · ipureintro; exact hnn
      iexists v
      iframe Hvv Hans HeI
    iright
    iexists v.Err'
    iframe Hn
    iapply apply.result_err_ro
    iexact Hvv

end nospace

end EtcdGrove
end Perennial
