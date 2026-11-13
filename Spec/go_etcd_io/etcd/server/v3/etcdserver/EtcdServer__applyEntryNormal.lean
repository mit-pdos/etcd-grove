/-
`(*EtcdServer).applyEntryNormal(e, shouldApplyV3)` (server.go): one normal entry, and the
consistent index after it. Lean-first (no Rocq counterpart); see `InvApplier.lean`,
`InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.applyEntryNormal(e, v3)`, by the apply thread, in the environment's auth mode (`E.authOn`;
step 6 of the auth-mode merge, 2026-10-30: one statement for both modes, `.any` excluded; until then
`specOff`/`specOn`, now `ModeSpecs.lean`'s corollaries). The protocol state `st` out of flight. Two
cases, by `v3` (R2d'a, Q23 (a), 2026-11-06: until then the `v3 = false` case was a first start's,
the ghost rows stepped, which no caller reaches: the KV invariant's `c0 ≤ ai0` puts every entry
after the applied index above `c0`). **With `v3`** (`ApplyBoth`: the entry `i = p + 1`, above `ci`,
whose index and term are the applying index; the state loaded, `stLoaded γ st = st`): the entry is
applied (through `apply.Apply`, or not at all if it has no data) and, after it, `ci` and the
processed-through index are both `i`. **The KV**: the apply thread's applier state in the mode
(`srvApplyKVM E.authOn`, the model's auth state `sa`), with the entry's premise in the mode
(`entryOkM`: with auth on, an admitted admin request too), goes to `x'` by `entryStep m true x x'
out`. **The wait**: the server's wait is the registry, in the mode (`isServerM E.authOn`: with auth
on the results carry the auth layer's verdict, `resultΨOn`), the entry normal (`m.typ = 0`) and its
id claimed for its data (`entryWaitOk`). It spends one write-back token of the backend (`srvWT E`; strict
M1: until then mvcc's `storeWT`). **The delivery**: to a caller that knows the entry's id registered (`entryRegd ρ.wait m (some
t)`), the entry is applied in full unless that registration is gone (`entryDelivered`). **The
applied log**: at the applied index `v = m.index - 1` with its log the KV's and the entry committed,
the KV log after the entry is deposited as the log applied through `m.index` before the result goes
to the waiter (`srvAppliedPre`). **The KV model**: the apply thread at the mode's model of the
committed raft log `A` through `v` (`kvAppliedM E.authOn`, from the server's start state
`srvAuthSt0`), at `A ++ [m]` after, the entry above the start's consistent index `c0`; the voters
members of the rest state at `A` (`srvMemCover`: with `entryWaitOk`'s `attrEntryOk`, `dispatch`'s
`restReqOk`; the cluster-rows stage, 2026-11-02). **With auth on** (only): the server's lessor finds
no lease (`srvLessorNilM`), one time receipt (an admin step's cost) under the receipts' bound, and
the rights to issue tokens at the consistent index (`srvTokRights`, `True` off), at the entry's
index after it. The receipt and the bound are both cases' (R2d'a swap batch 4, 2026-11-07: one
`if E.authOn` and one `receiptBound` premise, outside the `if v3`; until then each case had its
copy, the same meaning).

**Without `v3`, a replay** (an entry at or below the effective consistent index, at a restart; at
the pin `673da07c8`, `server.go:1975-2005`): no deferred `SetConsistentIndex`; an empty entry
notifies `firstCommitInTerm` and may promote the lessor; otherwise `apply.Apply(…, false)` dispatches
v2-only (`apply/uber_applier.go:93-127`) and the function returns before `Trigger`. So the KV and the
applied index are untouched (`entryStep m false`, which keeps the state, at the auth state `sa`),
the state `st` is unchanged, and the rest buckets at the backend's log `A₀` (`srvRestRp`, at an image
`r`) go to `restEntryV2 m r` (the attribute write in memory); the attribute's member is a voter
(`entryWaitOk`'s `attrEntryOk`), which the image's members include (Go's `UpdateAttributes` panics
on an unknown, unremoved member, `membership/cluster.go:467-496`). The backend's log committed with
the entry in it (the KV invariant's shape of a committed entry, `kv_log_plain`, is what makes a
skipped or rejected request leave the members, as `restEntryV2` says); the backend's write-back token spent (`srvWT E`)
(`apply.Apply`'s). With auth on, it **spends one time receipt (`⧗ 1`) per replayed entry**, not
given back (Go runs the auth applier's `IsAdminPermitted` on an admin entry at `v3 = false` too), so
each restart's replay of `A₀` consumes `|A₀|` receipts again against the fixed `receiptBound`; the
bound itself, and the chain the start's (`x.chain = γr.kv.ch0`: an admin request runs `adminEntryOn`
at `v3 = false`, which takes it). -/
abbrev EtcdServer.applyEntryNormal.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel) (sa : auth.AuthState)
    (A₀ : List EntryModel) (r : apply.RestM),
  E.authMode ≠ .any →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      -- the auth-on-only rows, both cases': one time receipt under the receipts' bound, and
      -- (auth-schema-fix F1) three write-back tokens of the tie's backend, an admin step's
      (if E.authOn then iprop(⧗ 1 ∗ apply.adminWTs E) else iprop(True)) ∗
      ⌜E.authOn = true → receiptBound GF ≤ 2 ^ 48⌝ ∗
      (if v3 then iprop(
        isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ entryWaitOk ρ E m ∗
        entryRegd ρ.wait ρ.ids m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
        srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvWT E ∗
        srvFS s ∗ srvAppliedOwn γr v ∗
        appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
        kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
        ⌜srvMemCover γr.raft γr.kv.c0 A⌝ ∗
        srvRLogLb γr.raft (A ++ [m]) ∗
        ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ uint.Z γr.kv.c0 < uint.Z m.index⌝ ∗
        ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
        ⌜st.pending = false ∧ entryOkM E.authOn E.lm x m ∧ m.typ = W32 0⌝ ∗
        (ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝) ∗
        srvTokRights E (ciEff γ st.k))
      else iprop(
        isServerM E.authOn s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryAt e m ∗ applyThread γ st ∗
        applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗
        srvWT E ∗ srvFS s ∗
        committedAtLeast γr m.index ∗ srvRestRp E γr A₀ r ∗ srvRLogLb γr.raft A₀ ∗ ⌜m ∈ A₀⌝ ∗
        ⌜st.pending = false ∧ entryOkM E.authOn E.lm x m ∧ m.typ = W32 0 ∧
          uint.Z m.index ≤ uint.Z (ciEff γ st.k) ∧
          (E.authOn = true → x.chain = γr.kv.ch0) ∧
          ∀ k, k ∈ γr.raft.raft.cfg → (r.mem !! k).isSome = true⌝)) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ mvcc.api.mvccReaders E.γ 1 ∗ srvFS s ∗
      (if v3 then iprop(
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
          srvApplyKVM E.authOn s E ρ.wait x' sa' ∗ ⌜entryStep m true x x' out⌝ ∗
          entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗
          srvRest E γr (A ++ [m])) ∗
        (ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩) ∗
        srvTokRights E m.index)
      else iprop(
        (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKVM E.authOn s E ρ.wait x' sa ∗
          ⌜entryStep m false x x' out⌝) ∗
        srvRestRp E γr A₀ (restEntryV2 m r) ∗ applyThread γ st)) }}

end spec

end EtcdGrove
end Perennial
