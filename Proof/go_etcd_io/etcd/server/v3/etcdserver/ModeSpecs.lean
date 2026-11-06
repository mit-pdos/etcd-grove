/-
**The server's mode variants of its merged specs** (the auth-mode merge,
`notes/auth-mode-merge-plan.md`, 2026-10-29): a merged spec is one statement for both auth modes,
the mode the environment's (`E.authOn`); for each, until its callers are merged too, the
statements of the two modes as they were (`specOff`, with the premise `E.authOn = false`, and
`specOn`, with `E.authOn = true`) and their corollaries `spec_off`/`spec_on` (no second proof:
`.claude/skills/spec/PRINCIPLES.md`, "One spec per function"). Each goes when no caller uses it.

The request path (step 5, 2026-10-29): `parseProposeCtxErr`, `processInternalRaftRequestOnce`,
`raftRequest`, `doSerialize`. (Their instances at a mode, `<F>.specM on`, went in the auth
component's stage 3, 2026-11-04: a caller applies `<F>.spec` and reads `E.authOn` off the
proposer's view, `isServerReqM_authOn`.) Their `<F>.specOff`, the mode-off statement before the
merge (over `isServerReq`, `reqPropOk`, the result at `kvModel`; `<F>.spec_off`), stays for the off
proofs that use it (`Compact`, the off tails of `Put`/`DeleteRange`/`Range`). The off and on texts of
`Put`, `DeleteRange`, `Range` and `Txn` themselves went in the auth component's stage 4
(2026-11-04): their clients take the merged spec at `E.authOn`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__parseProposeCtxErr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDRun
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section variants
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## `applyEntryNormal` -/

/-- **`spec` with auth off** (a corollary, `spec_off`; until step 6 of the auth-mode merge,
2026-10-30, `spec` itself). `s.applyEntryNormal(e, v3)`, by the apply thread (protocol state `st`, out of flight).
With `v3` (`ApplyBoth`: the entry `i = p + 1`, above `ci`, whose index and term are the
applying index; the state loaded, `stLoaded γ st = st`, as `apply`'s `ConsistentIndex` left it,
which the applier's `ConsistentIndex` lends, `srvCiC`; S8d, 2026-10-26): the entry is applied (through `apply.Apply`, or not at all if it has no data)
and, after it, `ci` and the processed-through index are both `i` (the post-lock hook set `ci`
if the entry had writes; else the deferred update does, outside the lock). Without `v3` (an
entry at or below `ci`, replayed): nothing is written to the backend and the state is
unchanged. **The KV** (the apply package's unit 3): the apply thread's applier state
`srvApplyKV s E ρ.wait x`, with the entry's premise `entryOk x m` (its data decode to a request with an
id, neither a compaction nor empty, satisfying the txn package's premises at `x.log`), goes to
`x'` by `entryStep m v3 x x' out` (no data: nothing; else `apply.Apply`'s `applyStep`). **The wait** (the request path's unit 2,
2026-10-12): the server's wait is the registry (`waitInv`, in `isServer`, with the request path's
names `ρ`); the entry is normal (`m.typ = 0`) and its id was claimed for its data
(`entryWaitOk`), so the result handed to `Trigger(id, ar)` is the registered proposer's
expectation (`resultΨ`: this request's `applyStep`, `applyResultIs`, and the certificate of the
log after). It spends one write token of the store (`mvcc.storeWT E.γ`, `apply.Apply`'s;
2026-10-13, unit 6). **The delivery** (the request path's unit 4d): to a caller that knows the
entry's id was registered (`entryRegd ρ.wait m (some t)`), the entry is applied in full (its
outcome not waived for want of a waiter) unless that registration is gone (`entryDelivered`:
a `Trigger` took it out first); the apply loops know nothing (`none`). **The applied log**
(2026-10-14, unit C2a): at the applied index `v = m.index - 1` with its log the KV's
(`appliedLogAt γr v x.log`) and the entry committed (`committedAtLeast γr m.index`, raft's
`toApply` batches: `rnApP`), the KV log after the entry is deposited as the log applied through
`m.index` before the result goes to the waiter (`srvAppliedPre`, `applied_predeposit`; the
result's witness, `resultIsW`), for `apply`'s `setAppliedIndex(m.index)` to publish. **The KV
model** (2026-10-14, unit T1): the apply thread at the committed raft log `A` through `v`
(`kvApplied`), the entry committed after it, `v3` as the model's (above the start's consistent
index): the apply thread at `A ++ [m]` after, its log deposited as the model's (`kvLogAt`). -/
abbrev EtcdServer.applyEntryNormal.specOff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel),
  E.authOn = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryRegd ρ.wait ρ.ids m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E ρ.wait x ∗ mvcc.storeWT E.γ ∗ srvFS s ∗
      srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗
      ⌜srvMemCover γr.raft γr.kv.c0 A⌝ ∗ srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
      ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
      ⌜st.pending = false ∧ entryOk E.lm x m ∧ m.typ = W32 0⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
       else iprop(True)) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
        ⌜entryStep m v3 x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
        srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗ srvRest E γr (A ++ [m])) ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) }}

/-- **`spec` in the auth mode `on`** (a corollary, `spec_on`) (the auth plan's E3o, 2026-10-27; `notes/decisions.md`, "E3o of
the auth plan"): the server as the apply thread sees it with auth on (`isServerM true`: the wait's
results `resultΨOn`, the applied logs the mode-`on` model's, `srvKVInvsOn`), the environment's
mode `on γa`; the applier state with the auth row at the model's auth state `sa`
(`srvApplyKVOn`), the apply thread at the mode-`on` model of `A` (`kvAppliedOn`, from the server's
start state `srvAuthSt0`); the entry's premise `entryOkOn` (an admitted admin request too); the
server's lessor finding no lease (`srvLessorNil`, `srv_uberKVL_on`'s named premise); one time
receipt (an admin step's cost, E2l) under the receipts' bound. After the entry, as `spec`'s, the
apply thread at the model's state after `A ++ [m]` (its auth state `sa'`), the log deposited as the
mode-`on` model's (`srvAppliedPre`, `kvLogAtM true`), and a registered proposer's result handed
over with the auth layer's verdict the model's (`resultΨOn`). -/
abbrev EtcdServer.applyEntryNormal.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel) (γa : auth.AuthNames)
    (sa : auth.AuthState),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ entryWaitOk ρ E m ∗
      entryRegd ρ.wait ρ.ids m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVOn s E ρ.wait x sa ∗ mvcc.storeWT E.γ ∗ srvFS s ∗
      ⧗ 1 ∗ srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      ⌜srvMemCover γr.raft γr.kv.c0 A⌝ ∗ srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
      ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
      ⌜st.pending = false ∧ entryOkOn x m ∧ m.typ = W32 0 ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
       else iprop(True)) ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
        srvApplyKVOn s E ρ.wait x' sa' ∗ ⌜entryStep m v3 x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
        srvAppliedPre γr v m.index x'.log ∗
        kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m])) ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) ∗
      (if v3 then srvTokRights E m.index else srvTokRights E (ciEff γ st.k)) }}

/-- **`specOff`**, `spec` with auth off (the auth-mode merge's corollary). -/
theorem EtcdServer.applyEntryNormal.spec_off
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOff (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A hoff
  have hm : E.authMode = .off := by
    rw [apply.AEnv.authOn_eq] at hoff
    cases h' : E.authMode <;> simp_all [auth.AuthMode.isOn]
  have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
    intro k; unfold srvTokRights; rw [hm]
  have := h s γ ci TM E ρ b e m st v3 x γr ot v A srvAuthSt0 (by rw [hm]; simp)
  rw [hoff] at this
  simp only [isServerM_false, srvLessorNilM_false, srvApplyKVM_false, kvAppliedM_false,
    entryOkM_false, hT, Bool.false_eq_true, ↓reduceIte] at this
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, Hao, Hlog,
    #Hcm, Hka, HRS, %Hmc, #Hrl, %Hv, %Hidx, %Hpre, Hv3⟩ HΦ
  iapply this $$ [Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hao Hlog Hka HRS Hv3]
  · iframe Hpkg Hsrv Hew Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hao Hlog Hcm Hka HRS Hrl Hv3
    ipureintro; exact ⟨Hmc, Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2, fun h => absurd h (by simp)⟩
  inext
  iintro ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x', %out, %sa', HKV, %Hstep, Hdel, Hap, Hka, HRS⟩, Hst, -⟩
  iapply HΦ
  iframe Hbe Hlr Hgr Hfs Hst
  iexists x', out; iframe HKV Hdel Hap Hka HRS; ipureintro; exact Hstep

/-- **`specOn`**, `spec` in the mode `on` (the auth-mode merge's corollary). -/
theorem EtcdServer.applyEntryNormal.spec_on
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOn (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A γa sa hM
  have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
  have := h s γ ci TM E ρ b e m st v3 x γr ot v A sa (by rw [hM]; simp)
  rw [hon] at this
  simp only [srvLessorNilM_true, srvApplyKVM_true, kvAppliedM_true, entryOkM_true,
    ↓reduceIte] at this
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hln, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, Hr, Hao, Hlog,
    #Hcm, Hka, HRS, %Hmc, #Hrl, %Hv, %Hidx, %Hpre, Hv3, Htok⟩ HΦ
  iapply this $$ [Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hr Hao Hlog Hka HRS Hv3 Htok] HΦ
  iframe Hpkg Hsrv Hln Hew Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hr Hao Hlog Hcm Hka HRS Hrl Hv3 Htok
  ipureintro; exact ⟨Hmc, Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2.1, fun _ => Hpre.2.2.2⟩

end variants

/-! ## The apply loop: `apply`, `applyEntries` -/

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open Iris.ProofMode

/-- **`spec` with auth off** (a corollary, `spec_off`; until step 3 of the auth-mode merge,
2026-10-30, `spec` itself). `s.apply(es, ep, rac)`, by the apply thread, on a non-empty batch of consecutive
committed entries from `f0` (`entriesFrom`), with the protocol's state `st` processed through
the larger of `ci` and `f0 - 1` (`loopOk`): each entry at or below `ci` is replayed with no
backend writes (`ApplyV2storeOnly`), each above is applied (`ApplyBoth`), and afterwards
`ci` and the processed-through index are both the larger of the old `ci` and the last index
`L`, which it returns with its term. So no entry's writes are applied twice, and none above
`ci` is skipped. **The KV** (the apply package's unit 3): the apply thread's applier state goes
from `x` to `x'` by `entriesStep c ms x x'` (`c` the consistent index the batch starts at: each
normal entry applied by `apply.Apply`, with `v3` iff above `c`), under `logShape ms` (each
normal entry's request meets its premise wherever the size clauses hold; the apply thread's log
is small, `srvApplyKV_small`, so they hold at the state each entry meets: D19c's move,
2026-10-18; until then `entriesOk c ms x`, the premise at every state the batch can reach). **The wait** (unit 2 of the
request path): `batchWaitOk` (each normal entry's id claimed for its data; each conf change's id,
`ccIdOf`, no KV request's registration), so every `Trigger` meets the registry's contract. **The
applied index** (the request path's unit 4b): the apply thread's half of the ghost applied index
(`srvAppliedOwn γr`) goes from `f0 - 1` to the last index, each `setAppliedIndex` depositing the KV
log after its entry, so the last index's log is `x'.log` (`appliedLogAt`); since 2026-10-14 (unit
C2a) from the log applied through `f0 - 1` the KV's (`appliedLogAt γr (f0 - 1) x.log`), with each
entry committed (`batchCommittedIdx`: raft's batches, `rnApP`), each entry's log deposited ahead
of its result (`applyEntryNormal`'s `srvAppliedPre`). **The KV model** (2026-10-14, unit T1): the
apply thread at the committed raft log `A` through `f0 - 1` (`kvApplied`), the batch committed after
it (`kvBatch`), at `A ++ ms` after. **The write budget**
(2026-10-13, unit 6): one write token of the store per entry, spent (a conf change's is wasted);
since D19b (2026-10-18) taken from the budget `srvWTPool E` with a time receipt of the entry's
iteration, until then handed in (`txn.storeWTs E.γ ms.length`); (D22 J5, 2026-10-26) the count of
tokens taken goes from `w` to `w + ms.length` (`srvWTTaken`; until J5 from `f0 - 1` to the last
index, `srvWTAt`). **The stop** (D19m, 2026-10-18): it
returns `shouldStop = false`, since `applyConfChange` removes no member (`ccApplyOk`), so the
caller's `stopWithDelay` is never reached. **The driver's view** (D43 M3, 2026-10-25; raft's
dynamic mode): with a view `dv` (`dvOk`: no replay, the node at the server's decoder), the view
after `A` goes to the view after `A ++ ms`, each conf entry applied through `applyConfChange`;
without, nothing (raft's static mode, or no conf entry in the batch). **The membership** (D43
M5e, 2026-10-26): the apply thread's membership resource (`srvApRes`: the fields and the cluster
and transport `applyConfChange` writes) from `A` to `A ++ ms`. -/
abbrev EtcdServer.apply.specOff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat),
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShape E.lm ms →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) f0 ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ batchWaitOk ρ E ms ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr (f0 - 1) ∗
      appliedLogAt γr (f0 - 1) x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) (f0 - 1) A ms ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ ms) ∗ srvRunH ρ.raft dv ∗ srvApRes s γr A }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop); srvFS s ∗ dvView ρ.raft dv (A ++ ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (A ++ ms) ∗
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
        epConfState ep csl ∗ epCsAt ρ.raft (A ++ ms) csl ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr appliedi ∗
        srvWTTaken γp.cnt (w + ms.length) ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗
          appliedLogAt γr appliedi x'.log ∗ kvApplied γr.raft γr.kv (A ++ ms) x' ∗ srvRest E γr (A ++ ms)) ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
          shouldStop = false⌝ }}


/-- **`spec` in the auth mode `on`** (a corollary, `spec_on`) (the auth plan's E3p, 2026-10-27; `notes/decisions.md`, "E3p of
the auth plan"): the loop over `applyEntryNormal.specOn`. The server as the apply thread sees it with
auth on (`isServerM true`), the environment's mode `on γa`; the batch of the mode-`on` log's shapes
(`logShapeOn`: an admitted admin request too); the applier state with the auth row at the model's
auth state `sa` (`srvApplyKVOn`), the apply thread at the mode-`on` model of `A`
(`kvAppliedOn … srvAuthSt0`); the server's lessor finding no lease (`srvLessorNil`) and the receipts'
bound (`applyEntryNormal.specOn`'s; each entry's receipt for its admin step comes from the
iteration's Go steps). After the batch, as `spec`'s, the apply thread at the model's state after
`A ++ ms` (its auth state `sa'`). -/
abbrev EtcdServer.apply.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat) (γa : auth.AuthNames)
    (sa : auth.AuthState),
  E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShapeOn ms →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) f0 ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ batchWaitOk ρ E ms ∗ es ↦*□ ents ∗
      entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVOn s E ρ.wait x sa ∗ srvAppliedOwn γr (f0 - 1) ∗
      appliedLogAt γr (f0 - 1) x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      kvBatch γr (ciEff γ st.k) (f0 - 1) A ms ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ ms) ∗ srvRunH ρ.raft dv ∗ srvApRes s γr A ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop); srvFS s ∗ dvView ρ.raft dv (A ++ ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (A ++ ms) ∗
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' at' ∗
        epConfState ep csl ∗ epCsAt ρ.raft (A ++ ms) csl ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr appliedi ∗
        srvWTTaken γp.cnt (w + ms.length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗ appliedLogAt γr appliedi x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ ms) x' sa' ∗ srvRest E γr (A ++ ms)) ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
          shouldStop = false⌝ }}

/-- **`spec` with auth off** (a corollary, `spec_off`; until step 3 of the auth-mode merge,
2026-10-30, `spec` itself). `s.applyEntries(ep, ap)`, by the apply thread: the entries of `ap` (consecutive from
`f0`, with no gap after the applied index `ep.appliedi = ai`, as raft hands them over) from
`ai + 1` on are applied (`apply`), and `ep.appliedi`, `ep.appliedt` advance to the last; the
apply thread's relation `loopOk` (processed through the larger of `ci` and the applied
index) is kept. **The KV** (the apply package's unit 3): the apply thread's applier state goes
from `x` to `x'` by `entriesStep c (unapplied ai ms) x x'`, `c` the consistent index at the
start (`ciEff γ st.k`), under `logShape (unapplied ai ms)` (D19c's move; until then
`entriesOk c (unapplied ai ms) x`), and `batchWaitOk` of the
batch (unit 2 of the request path: the wait's premise, see `apply`). **The applied index** (the
request path's unit 4b): the apply thread's half of the ghost applied index (`srvAppliedOwn γr`)
at `ai`, with the log applied through `ai` the KV's (`appliedLogAt γr ai x.log`), goes to `ai'`, the
log applied through `ai'` the KV's after (`apply` deposits one per entry; 2026-10-14, unit C2a:
each entry committed, `batchCommittedIdx`). **The write budget**
(2026-10-13, unit 6): one write token of the store per entry applied (since D19b, 2026-10-18,
taken by `apply` from the budget `srvWTPool E` with a time receipt; until then
`txn.storeWTs E.γ (unapplied ai ms).length`, handed in and spent; D22 J5, 2026-10-26: the count of
tokens taken goes from `w` to `w` plus the entries applied, `srvWTTaken`, until then from `ai` to
`ai'`, `srvWTAt`: `apply.Apply` may open one store write transaction per entry, and over the real backend
every write transaction's `Unlock` may write back, costing one of the backend's write-back
tokens, `backend.wbTok`). **The KV model** (2026-10-14, unit T1): the apply thread at the committed
raft log `A` through `ai` (`kvApplied`), the entries above `ai` committed after it (`kvBatch`), at
`A` and those entries after. -/
abbrev EtcdServer.applyEntries.specOff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShape E.lm (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvRunH ρ.raft dv ∗ srvApRes s γr A }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (A ++ unapplied ai ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (A ++ unapplied ai ms) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (A ++ unapplied ai ms) cs' ∗
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr ai' ∗ srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvApplied γr.raft γr.kv (A ++ unapplied ai ms) x' ∗ srvRest E γr (A ++ unapplied ai ms)) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          -- (D22 J5) one index per entry applied
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          -- (2026-10-31, the snapshot track: S1) the consistent index unchanged only for an empty batch
          ((unapplied ai ms = [] ∧ ciEff γ st'.k = ciEff γ st.k) ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}


/-- **`spec` in the auth mode `on`** (a corollary, `spec_on`) (the auth plan's E3p, 2026-10-27): over `apply.specOn` (the
server with auth on, `logShapeOn`, the applier state with the auth row at the model's auth state
`sa`, the apply thread at the mode-`on` model; the lessor finding no lease, the receipts' bound),
after the batch at the model's state after `A ++ unapplied ai ms` (its auth state `sa'`). -/
abbrev EtcdServer.applyEntries.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat)
    (γa : auth.AuthNames) (sa : auth.AuthState),
  E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeOn (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKVOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvRunH ρ.raft dv ∗ srvApRes s γr A ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (A ++ unapplied ai ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (A ++ unapplied ai ms) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (A ++ unapplied ai ms) cs' ∗
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr ai' ∗ srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗ srvRest E γr (A ++ unapplied ai ms)) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          -- (D22 J5) one index per entry applied
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          -- (2026-10-31, the snapshot track: S1) the consistent index unchanged only for an empty batch
          ((unapplied ai ms = [] ∧ ciEff γ st'.k = ciEff γ st.k) ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}


/-- **`specOff`**, `apply.spec` with auth off (the auth-mode merge's corollary; the mode read off
the server's view, `authOn_false_of_off`). -/
theorem EtcdServer.apply.spec_off
    (h : EtcdServer.apply.spec (GF := GF) (hG := hG)) :
    EtcdServer.apply.specOff (GF := GF) (hG := hG) := by
  unfold EtcdServer.apply.spec at h
  simp only [srvRunH_apply_spec] at h
  intro s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp dv w hne hfrom hok hEok hdv
  iintro %Φ ⟨#Hpkg, #Hsrv, Hbw, Hes, Hents, Hst, Hbe, Happ, Hcs, Hcv, Hlr, Hgr, HKV, Hao, Hlog0, Hbc,
    HWP, HWA0, Hfs, Hka, HRS, Hkb, Hdv, Hdvr, Hrun, HAR⟩ HΦ
  imod authOn_false_of_off s γ ci TM E ρ γr ρ.wait x A $$ [$Hsrv $HKV $Hka] with ⟨%hoff, HKV, Hka⟩
  have hm : E.authMode = .off := by
    rw [apply.AEnv.authOn_eq] at hoff
    cases h' : E.authMode <;> simp_all [auth.AuthMode.isOn]
  have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
    intro k; unfold srvTokRights; rw [hm]
  have h' := h s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp dv w srvAuthSt0
    (by rw [hm]; simp) (fun h1 => absurd (hoff ▸ h1) (by simp)) hne hfrom hok
    (by rw [hoff]; exact hEok) hdv
  rw [hoff] at h'
  simp only [isServerM_false, srvLessorNilM_false, srvApplyKVM_false, kvAppliedM_false, hT] at h'
  iapply h' $$ [Hbw Hes Hents Hst Hbe Happ Hcs Hcv Hlr Hgr HKV Hao Hlog0 Hbc HWP HWA0 Hfs Hka HRS Hkb
    Hdv Hdvr Hrun HAR] [HΦ]
  · iframe Hpkg Hsrv Hbw Hes Hents Hst Hbe Happ Hcs Hcv Hlr Hgr HKV Hao Hlog0 Hbc HWP HWA0 Hfs Hka HRS
      Hkb Hdv Hdvr Hrun HAR
  iintro !> %appliedt %appliedi %shouldStop ⟨Hfs, Hdv, Hrun, HAR, %st', %a', %at', %csl, Hst, -,
    Hbe, Hci, Hcs, Hcv, Hlr, Hgr, Hao, HWT, ⟨%x', %sa', HKV, %Hstep, Hlog, Hka, HRS⟩, %Hp⟩
  iapply HΦ
  iframe Hfs Hdv Hrun HAR
  iexists st', a', at', csl
  iframe Hst Hbe Hci Hcs Hcv Hlr Hgr Hao HWT
  isplitl [HKV Hlog Hka HRS]
  · iexists x'; iframe HKV Hlog Hka HRS; ipureintro; exact Hstep
  ipureintro; exact Hp

/-- **`specOn`**, `apply.spec` in the mode `on` (the auth-mode merge's corollary). -/
theorem EtcdServer.apply.spec_on
    (h : EtcdServer.apply.spec (GF := GF) (hG := hG)) :
    EtcdServer.apply.specOn (GF := GF) (hG := hG) := by
  unfold EtcdServer.apply.spec at h
  simp only [srvRunH_apply_spec] at h
  intro s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp dv w γa sa hM hRB hne hfrom hok
    hEok hdv
  have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
  have h' := h s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp dv w sa
    (by rw [hM]; simp) (fun _ => hRB) hne hfrom hok (by rw [hon]; exact hEok) hdv
  rw [hon] at h'
  simp only [srvLessorNilM_true, srvApplyKVM_true, kvAppliedM_true] at h'
  exact h'

end loop

/-! ## The request path -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The handoff.** `s.processInternalRaftRequestOnce(ctx, r)`, any goroutine, at a context, for
a request `r` holding `rq` but for its header (which it sets: the fresh id `Next` returns, the
auth info's user name and revision), with no `ID` (the server's requests have none; `Apply` takes
the header's), one id credit, a reader slot of `s.leadTimeMu` and (2026-10-14, unit A2) the auth store's reader
resource `E.RD` (`AuthInfoFromCtx`):
* success (`err = nil`): `res` is the apply thread's result of applying `rq'`, the request the
  proposed data decode to (`irrWireOf`: `rq` with its header, up to the model's `[0]` range ends):
  `resultIs E rq' res` (the apply package's `applyStep` and `applyResultIs` at the KV state the
  entry met, and mvcc's certificate of the log after; 2026-10-14, unit C2a: `resultIsW E ρ.rd`, with
  the witness that the log after is applied through an index of the committed log, `appliedWit`);
  and (2026-10-14, unit T1) the result `Qr` of the proposal's update at a committed log (`reqPropOk
  ρ.kv rq Qr`: the request has no KV write, `Qr` trivial; or, since 2026-10-15 (unit T2), it is a
  plain write, a put, a delete or a transaction, with its client's update over the whole state,
  `Qr L` the client's `□ Q` at the state of `L`'s model): `□ Qr L` of the committed log `L` before
  the entry the result is of, whose model is the log `lb` the entry met (unit W-M3: the result's
  `y.log`, so the update's state is the write's);
* failure: no result, an error the gRPC layer can take (`applyErrIs`: in an error tree, a safe map
  key, with a message; 2026-10-12, unit 3a), and the proposal, if made, deposited (`srvMaybeDeposited`: it may
  still be applied: the request limit, the auth store's error, the marshal's error, the size
  limit come before the proposal; `Propose`'s error, the context's (`parseProposeCtxErr`) and the
  server's stop (`ErrStopped`) after it). -/
abbrev EtcdServer.processInternalRaftRequestOnce.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  -- (2026-10-31) the request within protobuf's recursion limit (`proto.MarshalIRR`'s premise: a
  -- deeper one would be proposed and panic every member's apply,
  -- `issues/etcd-txn-nested-depth-apply-panic.md`)
  apply.irrDepthOk rq →
  -- (2026-11-02, the cluster-rows stage) no attribute request: the monitors' alone propose them
  -- (`reqPropOkM`'s `attrIdOk`)
  apply.dispatchKind rq ≠ .clusterMemberAttrSet →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
          ∃ lb : mvcc.Log, resultIsW E ρ.rd rq' F res lb ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ srvMaybeDeposited ρ rq)) }}

/-- `s.raftRequest(ctx, r)` (as `processInternalRaftRequestOnce`): success, the apply thread's
answer to `rq'` (`appliedOk`: dispatched, the apply package's response, no error); failure, no
response and an error (2026-10-14, unit C2a: the success with the result's witness at `ρ.rd`,
`appliedWit`): the apply's (`appliedErr`), or `processInternalRaftRequestOnce`'s (the
proposal, if made, deposited). Unit W-M3: the update's committed log `L` is the raft prefix whose
model is the log `lb` the entry met (`appliedOk`'s `x.log`), and the log after is certified. -/
abbrev EtcdServer.raftRequest.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  -- (2026-10-31) the request within protobuf's recursion limit (`proto.MarshalIRR`'s premise: a
  -- deeper one would be proposed and panic every member's apply,
  -- `issues/etcd-txn-nested-depth-apply-panic.md`)
  apply.irrDepthOk rq →
  -- (2026-11-02, the cluster-rows stage) no attribute request: the monitors' alone propose them
  -- (`reqPropOkM`'s `attrIdOk`)
  apply.dispatchKind rq ≠ .clusterMemberAttrSet →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (lb : mvcc.Log),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedOk E ρ.rd rq' F resp lb ∗
          ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ rq))) }}

/-- **`s.doSerialize(ctx, chk, get)`** at a context, with the permission check `chk` (a triple:
on any auth info, an error the gRPC layer can take) and the read `get` (`{G} get() {Q}`): the
request's auth info (`AuthInfoFromCtx`, or an empty one), `chk` of it, `get()`, then the
token's revision against the auth store's (`ErrAuthOldRevision`). Success: `get` ran (`Q`);
failure: an error the gRPC layer can take, and `get` ran or not (`G ∨ Q`). 2026-10-14 (unit A2):
the auth store's reader resource `E.RD`, which `AuthInfoFromCtx` and `chk` take and give back.
2026-10-23 (auth plan A1): `C info`, what a passed `chk` establishes of the auth info it saw (the
permission class of the request's keys, `apply.rangeClass`, `apply.txnClass`); success gives it
of some auth info (the context's, or the empty one). -/
abbrev EtcdServer.doSerialize.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF)
    (C : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}


end specs

/-! ## The instances from the spec -/

section corollaries
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The mode-off handoff from the spec (a constant result; the success post's model fact
`kvModel L = y.log`). -/
theorem EtcdServer.processInternalRaftRequestOnce.spec_off
    (h : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG)) :
    EtcdServer.processInternalRaftRequestOnce.specOff (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd p rq Qr F Hid0 Hdpt Hka
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨Ha, #Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hb
  have hM := h s E ρ ctx cd p rq (fun _ => Qr) F Hid0 Hdpt
  rw [hon] at hM
  iapply hM $$ [Ha Hc Hd He Hf Hg Hok Hi Hj] [HΦ]
  · ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr (attrIdOk_of_kind _ _ Hka) $$ Hok
    rw [isServerReqM_false]
    iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  · iintro !> %res %err ⟨Hrd, Hard, Hpost⟩
    iapply HΦ
    iframe Hrd Hard
    icases Hpost with (⟨%He, %hm, %rq', %Hw, HTr, %L, #HL, Hp, -, #HQ, -⟩ | Herr)
    · ileft
      isplitr
      · ipureintro; exact He
      iexists hm, rq'
      iframe HTr
      isplitr
      · ipureintro; exact Hw
      iunfold resPostM at Hp
      icases Hp with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5, -, -, Hr6⟩
      iexists y.log
      iunfold resultIsW
      isplitl [Hr1 Hr2 Hr3 Hr4 Hr5 Hr6]
      · isplitr
        · ipureintro; exact Hnn
        iexists y, y', out
        iframe Hr1 Hr2 Hr3 Hr4 Hr5 Hr6
        ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
      iexists L
      iframe HL HQ
      ipureintro; exact Hst.2.2.2
    · iright; iexact Herr

/-- The mode-off `raftRequest` from the spec. -/
theorem EtcdServer.raftRequest.spec_off
    (h : EtcdServer.raftRequest.spec (GF := GF) (hG := hG)) :
    EtcdServer.raftRequest.specOff (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd p rq Qr F Hid0 Hdpt Hka
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨Ha, #Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hb
  have hM := h s E ρ ctx cd p rq (fun _ => Qr) F Hid0 Hdpt
  rw [hon] at hM
  ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr (attrIdOk_of_kind _ _ Hka) $$ Hok
  rw [← isServerReqM_false]
  iapply hM $$ [Ha Hc Hd He Hf Hg Hok' Hi Hj] [HΦ]
  · iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  iintro !> %resp %err ⟨Hrd, Hard, Hpost⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hpost with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hok, -, #HQ, -⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hst, Ha1, Ha2, Ha3, Ha4, Ha5, -⟩
    iexists hm, rq', x.log
    isplitr
    · ipureintro; exact Hw
    isplitl [Ha1 Ha2 Ha3 Ha4 Ha5]
    · iunfold appliedOk
      iexists x, x', o, skip
      iframe Ha1 Ha2 Ha3 Ha4 Ha5
      ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
    iexists L
    iframe HL HQ
    ipureintro; exact Hst.2.2.2.1
  · iright
    icases Herr with ⟨%Hr, #HaE, (⟨%hm, %rq', %Hw, Ha, -⟩ | Hdep)⟩
    · iframe HaE
      isplitr
      · ipureintro; exact Hr
      ileft; iexists hm, rq'; iframe Ha; ipureintro; exact Hw
    · iframe HaE Hdep
      ipureintro; exact Hr

/-- The mode-off `doSerialize` from the spec (the auth info's binding dropped). -/
theorem EtcdServer.doSerialize.spec_off
    (h : EtcdServer.doSerialize.spec (GF := GF) (hG := hG)) :
    EtcdServer.doSerialize.specOff (GF := GF) (hG := hG) := by
  intro s E ρ γr ctx cd chk get G Q C t e
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨Ha, #Hb, Hpre⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hb
  have hM := h s E ρ γr ctx cd chk get G Q C t e
  rw [hon] at hM
  iapply hM $$ %Φ [Ha Hpre]
  · rw [isServerReqM_false, isServerReadM_false]; iframe Ha Hb Hpre
  inext
  iintro %err ⟨Hrd, Hres⟩
  iapply HΦ
  iframe Hrd
  icases Hres with (⟨%He, ⟨%info, HC, -⟩, HQ⟩ | Hr)
  · ileft; iframe HQ; isplitr
    · ipureintro; exact He
    · iexists info; iexact HC
  · iright; iexact Hr


end corollaries

section snap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- (moved from `SnapAuthOnDraft.lean`, the auth component's stage 2, 2026-11-04) -/
/-- **Lean's `applyAll.specSnap` is `applyAll.specSnapM`'s `off` case** (F9). -/
theorem EtcdServer.applyAll.specSnap_of_M
    (h : EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specSnap (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk q γn
    rt n hai hi61 hboot hAL hcia hraft hc0 hch hlog0 hγn _hpre hnI
  cases hon : E.authOn with
  | false =>
    have H := h s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk
      q γn rt n srvAuthSt0 (by rw [authMode_off_of E hon]; simp) hai hi61 hboot hAL hcia hraft hc0
      (by rw [hon]; exact hch) hlog0 hγn hnI
    rw [hon] at H
    exact H
  | true =>
    -- lean's rows are the mode `off`'s: its precondition refutes `authOn`
    wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
      #Hracf, #Hracc, #Hrtf, #Hrt, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog,
      #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
    imod (authOn_false_of_off s γ ci TM E ρ γr ρ.wait x A) $$ [$Hsrv $HKV $Hka] with ⟨%Hoff, -, -⟩
    rw [hon] at Hoff
    cases Hoff

end snap

section merged
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ### The auth component's merged specs' off and on texts (stage 2, 2026-11-04)

Until stage 2 these were the linked specs (`X.spec`, `X.specOn`); the merged `X.spec` (one
statement over `C : AuthC`) is now linked, and these, with their texts unchanged, are its
corollaries (`X.spec_off`, `X.spec_on`), what the off-only examples and the `_on` results took.
Stage 3 (2026-11-04) deleted them: their callers instantiate the merged specs (an off client of
`start`/`Start` through `isServerBuilt_offC`). What is left here is a lemma about the merged
`applyAll`'s matcher and the off premise's laws. -/

/-- The merged `applyAll.specBatch`'s running-token match is `srvRunH` (the auth component's 2c). -/
theorem srvRunH_applyAll_specBatch (γs : ServerRaftNames) (dv : Option Loc) :
    _root_.Perennial.EtcdGrove.EtcdServer.applyAll.specBatch.match_1 (fun _ => IProp GF) dv
      (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH γs dv := by
  cases dv <;> rfl

/-- **`start`'s construction premise has auth off** (`authOn_false_of_run` at the apply thread's
start, as `start`'s off proof). -/
theorem isServerBuilt_off (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    isServerBuilt (GF := GF) s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ={⊤}=∗
      ⌜E.authMode = AuthC.off.mode⌝ ∗ isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  iintro H
  iunfold isServerBuilt at H
  icases H with ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, #Hrvkb, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩
  iunfold applyBuilt at Happ
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hlo, Hbe, Hca, Halg, Hbm, Hbo, ⟨%ua, Hua, #Hfor, Hkv⟩, HRA, HAR, Hrdat, Hao,
    #Hlog, Hkr, Hfs⟩
  imod authOn_false_of_run E γr ua x₀ ai₀ c₀ [] $$ [$Hkvi $Hkv $Hkr] with ⟨%hoff, Hkv, Hkr⟩
  imodintro
  isplitr
  · ipureintro; exact authMode_off_of E hoff
  iunfold isServerBuilt
  iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hkvi Hti Hci' Hrn HEr Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hrvkb Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb
  iunfold applyBuilt
  iexists st₀, a, t, f
  iframe Hth Hbe Hca Halg Hbm Hbo HRA HAR Hrdat Hao Hlog Hkr Hfs
  isplitr
  · ipureintro; exact Hlo
  iexists ua
  iframe Hua Hfor Hkv

/-- **The off construction premise at the slot** (the auth component's stage 3, 2026-11-04: what
an off client of the merged `start.spec`/`Start.spec` gives at `C := .off`, where stage 2's
corollaries `start.spec_off`/`Start.spec_off` did): the environment's mode off
(`isServerBuilt_off`), the premise as the slot's row (`isServerBuiltM_C`, with the stop's slot,
`srvStop.slot`: R2c-3) and the slot's lessor (nothing, off). -/
theorem isServerBuilt_offC (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    isServerBuilt (GF := GF) s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗ srvStop.slot s E γn Er ={⊤}=∗
      ⌜E.authMode = AuthC.off.mode⌝ ∗ isServerBuiltC .off s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ∗
        acLessor .off s := by
  iintro ⟨Hb, Hsk⟩
  imod isServerBuilt_off s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N $$ Hb with ⟨%hm, Hb⟩
  have hB := isServerBuiltM_C (GF := GF) .off s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N hm
  dsimp only [AuthC.isOn] at hB
  rw [isServerBuiltM_false] at hB
  ihave Hb' := hB.1 $$ [Hb Hsk]
  · iframe Hb Hsk
  have hL : acLessor (GF := GF) .off s = iprop(True) := by rw [← srvLessorNilM_eq]; rfl
  rw [hL]
  imodintro
  isplitr
  · ipureintro; exact hm
  iframe Hb'

end merged

end EtcdGrove
end Perennial
