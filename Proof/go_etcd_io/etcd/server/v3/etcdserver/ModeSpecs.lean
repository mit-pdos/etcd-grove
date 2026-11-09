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
public import Proof.go_opentelemetry_io.otel.trace.Defs
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
if the entry had writes; else the deferred update does, outside the lock). Without `v3`, a
replay (R2d'a, Q23 (a), 2026-11-06: `spec`'s second case; the first start's ghost-advancing case it
replaced was never reached): nothing is written to the backend, the KV and the state are
unchanged, and the rest buckets at the backend's log go to `restEntryV2 m r`. **The KV** (the apply package's unit 3): the apply thread's applier state
`srvApplyKV s E ρ.wait x`, with the entry's premise `entryOk x m` (its data decode to a request with an
id, neither a compaction nor empty, satisfying the txn package's premises at `x.log`), goes to
`x'` by `entryStep m v3 x x' out` (no data: nothing; else `apply.Apply`'s `applyStep`). **The wait** (the request path's unit 2,
2026-10-12): the server's wait is the registry (`waitInv`, in `isServer`, with the request path's
names `ρ`); the entry is normal (`m.typ = 0`) and its id was claimed for its data
(`entryWaitOk`), so the result handed to `Trigger(id, ar)` is the registered proposer's
expectation (`resultΨ`: this request's `applyStep`, `applyResultIs`, and the certificate of the
log after). It spends one write token of the store (`srvWT E`, `apply.Apply`'s;
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
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel) (A₀ : List EntryModel)
    (r : apply.RestM),
  E.authOn = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      (if v3 then iprop(
        isServer s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryRegd ρ.wait ρ.ids m ot ∗ entryAt e m ∗
        applyThread γ st ∗ applyBackend γ ci b ∗
        srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKV s E ρ.wait x ∗ srvWT E ∗ srvFS s ∗
        srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
        kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗
        ⌜srvMemCover γr.raft γr.kv.c0 A⌝ ∗ srvRLogLb γr.raft (A ++ [m]) ∗
        ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ uint.Z γr.kv.c0 < uint.Z m.index⌝ ∗
        ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
        ⌜st.pending = false ∧ entryOk E.lm x m ∧ m.typ = W32 0⌝ ∗
        (ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝))
      else iprop(
        isServer s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryAt e m ∗ applyThread γ st ∗
        applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKV s E ρ.wait x ∗
        srvWT E ∗ srvFS s ∗ committedAtLeast γr m.index ∗ srvRestRp E γr A₀ r ∗
        srvRLogLb γr.raft A₀ ∗ ⌜m ∈ A₀⌝ ∗
        ⌜st.pending = false ∧ entryOk E.lm x m ∧ m.typ = W32 0 ∧
          uint.Z m.index ≤ uint.Z (ciEff γ st.k) ∧
          ∀ k, k ∈ γr.raft.raft.cfg → (r.mem !! k).isSome = true⌝)) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvFS s ∗
      (if v3 then iprop(
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m true x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
          srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗
          srvRest E γr (A ++ [m])) ∗
        (ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩))
      else iprop(
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m false x x' out⌝) ∗
        srvRestRp E γr A₀ (restEntryV2 m r) ∗ applyThread γ st)) }}

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
    (sa : auth.AuthState) (A₀ : List EntryModel) (r : apply.RestM),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      (if v3 then iprop(
        isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ entryWaitOk ρ E m ∗
        entryRegd ρ.wait ρ.ids m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
        srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKVOn s E ρ.wait x sa ∗ srvWT E ∗ srvFS s ∗
        ⧗ 1 ∗ srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
        kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
        ⌜srvMemCover γr.raft γr.kv.c0 A⌝ ∗ srvRLogLb γr.raft (A ++ [m]) ∗
        ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ uint.Z γr.kv.c0 < uint.Z m.index⌝ ∗
        ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
        ⌜st.pending = false ∧ entryOkOn x m ∧ m.typ = W32 0 ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
        (ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝) ∗
        -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
        srvTokRights E (ciEff γ st.k))
      else iprop(
        isServerM true s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryAt e m ∗ applyThread γ st ∗
        applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKVOn s E ρ.wait x sa ∗
        srvWT E ∗ srvFS s ∗ ⧗ 1 ∗ committedAtLeast γr m.index ∗ srvRestRp E γr A₀ r ∗
        srvRLogLb γr.raft A₀ ∗ ⌜m ∈ A₀⌝ ∗
        ⌜st.pending = false ∧ entryOkOn x m ∧ m.typ = W32 0 ∧
          uint.Z m.index ≤ uint.Z (ciEff γ st.k) ∧ receiptBound GF ≤ 2 ^ 48 ∧ x.chain = γr.kv.ch0 ∧
          ∀ k, k ∈ γr.raft.raft.cfg → (r.mem !! k).isSome = true⌝)) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvFS s ∗
      (if v3 then iprop(
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
          srvApplyKVOn s E ρ.wait x' sa' ∗ ⌜entryStep m true x x' out⌝ ∗
          entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m])) ∗
        (ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩) ∗
        srvTokRights E m.index)
      else iprop(
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKVOn s E ρ.wait x' sa ∗
          ⌜entryStep m false x x' out⌝) ∗
        srvRestRp E γr A₀ (restEntryV2 m r) ∗ applyThread γ st)) }}

/-- **`specOff`**, `spec` with auth off (the auth-mode merge's corollary). -/
theorem EtcdServer.applyEntryNormal.spec_off
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOff (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A A₀ r hoff
  have hm : E.authMode = .off := by
    rw [apply.AEnv.authOn_eq] at hoff
    cases h' : E.authMode <;> simp_all [auth.AuthMode.isOn]
  have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
    intro k; unfold srvTokRights; rw [hm]
  have := h s γ ci TM E ρ b e m st v3 x γr ot v A srvAuthSt0 A₀ r (by rw [hm]; simp)
  rw [hoff] at this
  cases v3
  · simp only [isServerM_false, srvApplyKVM_false, entryOkM_false, Bool.false_eq_true,
      ↓reduceIte] at this ⊢
    iintro %Φ ⟨#Hpkg, #Hsrv, #Hew, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, #Hcm, HRS, #HA0, %HmA,
      %Hpo⟩ HΦ
    iapply this $$ [He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs HRS] HΦ
    iframe Hpkg Hsrv Hew He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hcm HRS HA0
    isplitr; · itrivial
    ipureintro
    exact ⟨HmA, Hpo.1, Hpo.2.1, Hpo.2.2.1, Hpo.2.2.2.1, fun h => absurd h (by simp), Hpo.2.2.2.2⟩
  · simp only [isServerM_false, srvLessorNilM_false, srvApplyKVM_false, kvAppliedM_false,
      entryOkM_false, hT, Bool.false_eq_true, ↓reduceIte] at this ⊢
    iintro %Φ ⟨#Hpkg, #Hsrv, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, Hao, Hlog,
      #Hcm, Hka, HRS, %Hmc, #Hrl, %Hv, %Hidx, %Hpre, Hv3⟩ HΦ
    iapply this $$ [Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hao Hlog Hka HRS Hv3]
    · iframe Hpkg Hsrv Hew Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hao Hlog Hcm Hka HRS Hrl Hv3
      isplitr; · itrivial
      ipureintro; exact ⟨Hmc, Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2⟩
    inext
    iintro ⟨Hbe, Hlr, Hgr, Hmr, Hfs, ⟨%x', %out, %sa', HKV, %Hstep, Hdel, Hap, Hka, HRS⟩, Hst, -⟩
    iapply HΦ
    iframe Hbe Hlr Hgr Hmr Hfs Hst
    iexists x', out; iframe HKV Hdel Hap Hka HRS; ipureintro; exact Hstep

/-- **`specOn`**, `spec` in the mode `on` (the auth-mode merge's corollary). -/
theorem EtcdServer.applyEntryNormal.spec_on
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOn (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A γa sa A₀ r hM
  have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
  have := h s γ ci TM E ρ b e m st v3 x γr ot v A sa A₀ r (by rw [hM]; simp)
  rw [hon] at this
  cases v3
  · simp only [srvApplyKVM_true, entryOkM_true, Bool.false_eq_true, ↓reduceIte] at this ⊢
    iintro %Φ ⟨#Hpkg, #Hsrv, #Hew, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, Hr, #Hcm, HRS, #HA0,
      %HmA, %Hpo⟩ HΦ
    iapply this $$ [He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr HRS] HΦ
    iframe Hpkg Hsrv Hew He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hcm HRS HA0
    isplitr; · ipureintro; exact fun _ => Hpo.2.2.2.2.1
    ipureintro
    exact ⟨HmA, Hpo.1, Hpo.2.1, Hpo.2.2.1, Hpo.2.2.2.1,
      fun _ => Hpo.2.2.2.2.2.1, Hpo.2.2.2.2.2.2⟩
  · simp only [srvLessorNilM_true, srvApplyKVM_true, kvAppliedM_true, entryOkM_true,
      ↓reduceIte] at this ⊢
    iintro %Φ ⟨#Hpkg, #Hsrv, #Hln, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, Hr, Hao, Hlog,
      #Hcm, Hka, HRS, %Hmc, #Hrl, %Hv, %Hidx, %Hpre, Hv3, Htok⟩ HΦ
    iapply this $$ [Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hao Hlog Hka HRS Hv3 Htok] HΦ
    iframe Hpkg Hsrv Hln Hew Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hao Hlog Hcm Hka HRS Hrl Hv3 Htok
    isplitr; · ipureintro; exact fun _ => Hpre.2.2.2
    ipureintro; exact ⟨Hmc, Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2.1⟩

end variants

/-! ## The apply loop (`apply`'s and `applyEntries`' mode corollaries went with R2d'a swap batch 3: their proofs prove `specAt`/`specBatchAt` at the mode) -/

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open Iris.ProofMode

/-- **The start's consistent index at most raft's first index** (R2d'a, Q23 (a), 2026-11-06): the
KV invariant's `c0 ≤ ai0`, in either mode (`kvInv`, `kvInvOn`). So every entry after the applied
index is above `c0`: `applyEntryNormal.spec`'s `v3` case is the only one `apply` reaches. -/
theorem isServerM_c0_le (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    ⊢ isServerM on s γ ci TM E ρ γr ={⊤}=∗ ⌜uint.Z γr.kv.c0 ≤ uint.Z γr.raft.ai0⌝ := by
  iintro #Hsrv
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨-, -, -, #Hat, -⟩
  iunfold srvAtomicsM at Hat
  icases Hat with ⟨-, -, #Hkvi⟩
  cases on
  · rw [srvKVInvsM_false] at *
    iunfold srvKVInvs at Hkvi
    icases Hkvi with ⟨#HkI, -⟩
    iunfold kvInv at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
    imod Hclose $$ [HL Hσ HG] with -
    · inext; iexists L; iframe HL Hσ Hw HG; ipureintro; exact Hok
    imodintro; ipureintro; exact Hok.2.2.1
  · ihave #Hkvi : srvKVInvsOn E γr srvAuthSt0 $$ []
    · iapply srvKVInvsM_true; iexact Hkvi
    iunfold srvKVInvsOn at Hkvi
    icases Hkvi with ⟨#HkI, -⟩
    iunfold kvInvOn at HkI
    iinv HkI with >Hi Hclose
    icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
    imod Hclose $$ [HL Hσ Hh] with -
    · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
    imodintro; ipureintro; exact Hok.2.2.2.1

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
      trace.spanCtxOk ctx ∗ irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      srvApi.kvLogLb E.γs F }}
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
      trace.spanCtxOk ctx ∗ context.startTimeOk ctx ∗ irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      srvApi.kvLogLb E.γs F }}
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
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ authApplyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ authApplyErrIs err ∗
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
  icases Hpre with ⟨Ha, #Hb, Hc, Hd, He, Hf, Hsp, Hg, Hok, Hi, Hj⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hb
  have hM := h s E ρ ctx cd p rq (fun _ => Qr) F Hid0 Hdpt
  rw [hon] at hM
  iapply hM $$ [Ha Hc Hd He Hf Hsp Hg Hok Hi Hj] [HΦ]
  · ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr (attrIdOk_of_kind _ _ Hka) $$ Hok
    rw [isServerReqM_false]
    iframe Ha Hb Hc Hd He Hf Hsp Hg Hok' Hi Hj
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
      icases Hp with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5, -, -, #Hr8, %Hr9, Hr6⟩
      iexists y.log
      iunfold resultIsW
      isplitl [Hr1 Hr2 Hr3 Hr4 Hr5 Hr6]
      · isplitr
        · ipureintro; exact Hnn
        iexists y, y', out
        iframe Hr1 Hr2 Hr3 Hr4 Hr5 Hr8 Hr6
        isplitr
        · ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
        ipureintro; exact Hr9
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
  icases Hpre with ⟨Ha, #Hb, Hc, Hd, He, Hf, Hsp, #Hst, Hg, Hok, Hi, Hj⟩
  ihave %hon := isServerReq_authOn s E ρ $$ Hb
  have hM := h s E ρ ctx cd p rq (fun _ => Qr) F Hid0 Hdpt
  rw [hon] at hM
  ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr (attrIdOk_of_kind _ _ Hka) $$ Hok
  rw [← isServerReqM_false]
  iapply hM $$ [Ha Hc Hd He Hf Hsp Hg Hok' Hi Hj] [HΦ]
  · iframe Ha Hb Hc Hd He Hf Hsp Hst Hg Hok' Hi Hj
  iintro !> %resp %err ⟨Hrd, Hard, Hpost⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hpost with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hok, -, #HQ, -⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hst, Ha1, Ha2, Ha3, Ha4, Ha5, -, #Ha7, %Ha8, -⟩
    iexists hm, rq', x.log
    isplitr
    · ipureintro; exact Hw
    isplitl [Ha1 Ha2 Ha3 Ha4 Ha5]
    · iunfold appliedOk
      iexists x, x', o, skip
      iframe Ha1 Ha2 Ha3 Ha4 Ha5 Ha7
      isplitr
      · ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
      ipureintro; exact Ha8
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
  icases H with ⟨#Hci, #Hfb, #Hreqb, #Hrdb, #Hrunb, Hcrun, #Hsab, #Hai, #Hkvi, #Hti, #Hci', #Hrn, #HEr, Hwpend, Hrunh, Hwth, Hwtl, #Hdisk, #Hslg, #Hρrd, #Hmid, #Hmidc, #HmetaSnap, Hsnap, Hloop, Hsend, Happly, Hrdone, #HNR, #Hcv, #Hcci, #Hwci, #Hbound, #Hrvkb, Hw, Haw, Hdone, Hstop, Hstopping, Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr, HWB, Hwtok, Hsnapb⟩
  iunfold applyBuilt at Happ
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hlo, Hbe, Hca, Halg, Hbm, Hrdk, Hbo, ⟨%ua, Hua, #Hfor, Hkv⟩, HRA, HAR, Hrdat, Hao,
    #Hlog, Hkr, Hfs⟩
  imod authOn_false_of_run E γr ua x₀ ai₀ c₀ [] $$ [$Hkvi $Hkv $Hkr] with ⟨%hoff, Hkv, Hkr⟩
  imodintro
  isplitr
  · ipureintro; exact authMode_off_of E hoff
  iunfold isServerBuilt
  iframe Hci Hfb Hreqb Hrdb Hrunb Hcrun Hsab Hai Hkvi Hti Hci' Hrn HEr Hwpend Hrunh Hwth Hwtl Hdisk Hslg Hρrd Hmid Hmidc HmetaSnap Hsnap Hloop Hsend Happly Hrdone HNR Hcv Hcci Hwci Hbound Hrvkb Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hwtok Hsnapb
  iunfold applyBuilt
  iexists st₀, a, t, f
  iframe Hth Hbe Hca Halg Hbm Hrdk Hbo HRA HAR Hrdat Hao Hlog Hkr Hfs
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
