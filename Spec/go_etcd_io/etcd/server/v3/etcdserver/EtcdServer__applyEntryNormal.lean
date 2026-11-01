/-
`(*EtcdServer).applyEntryNormal(e, shouldApplyV3)` (server.go): one normal entry, and the
consistent index after it. Lean-first (no Rocq counterpart); see `InvApplier.lean`,
`InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn

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
`specOff`/`specOn`, now `ModeSpecs.lean`'s corollaries). The protocol state `st` out of flight.
With `v3` (`ApplyBoth`: the entry `i = p + 1`, above `ci`, whose index and term are the applying
index; the state loaded, `stLoaded γ st = st`): the entry is applied (through `apply.Apply`, or not
at all if it has no data) and, after it, `ci` and the processed-through index are both `i`. Without
`v3` (an entry at or below `ci`, replayed): nothing is written to the backend and the state is
unchanged. **The KV**: the apply thread's applier state in the mode (`srvApplyKVM E.authOn`, the
model's auth state `sa`), with the entry's premise in the mode (`entryOkM`: with auth on, an
admitted admin request too), goes to `x'` by `entryStep m v3 x x' out`. **The wait**: the
server's wait is the registry, in the mode (`isServerM E.authOn`: with auth on the results carry
the auth layer's verdict, `resultΨOn`), the entry normal (`m.typ = 0`) and its id claimed for its
data (`entryWaitOk`). It spends one write token of the store (`mvcc.storeWT E.γ`). **The
delivery**: to a caller that knows the entry's id registered (`entryRegd ρ.wait m (some t)`), the
entry is applied in full unless that registration is gone (`entryDelivered`). **The applied log**:
at the applied index `v = m.index - 1` with its log the KV's and the entry committed, the KV log
after the entry is deposited as the log applied through `m.index` before the result goes to the
waiter (`srvAppliedPre`). **The KV model**: the apply thread at the mode's model of the committed
raft log `A` through `v` (`kvAppliedM E.authOn`, from the server's start state `srvAuthSt0`), at
`A ++ [m]` after. **With auth on** (only): the server's lessor finds no lease (`srvLessorNilM`),
one time receipt (an admin step's cost) under the receipts' bound, and the rights to issue tokens
at the consistent index (`srvTokRights`, `True` off), at the entry's index after it with `v3`. -/
abbrev EtcdServer.applyEntryNormal.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel) (sa : auth.AuthState),
  E.authMode ≠ .any →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ entryWaitOk ρ E m ∗
      entryRegd ρ.wait ρ.ids.pfx m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗ mvcc.storeWT E.γ ∗
      srvFS s ∗ (if E.authOn then iprop(⧗ 1) else iprop(True)) ∗ srvAppliedOwn γr v ∗
      appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
      ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
      ⌜st.pending = false ∧ entryOkM E.authOn x m ∧ m.typ = W32 0 ∧
        (E.authOn = true → receiptBound GF ≤ 2 ^ 48)⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
       else iprop(True)) ∗
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
        srvApplyKVM E.authOn s E ρ.wait x' sa' ∗ ⌜entryStep m v3 x x' out⌝ ∗
        entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
        kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m])) ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) ∗
      (if v3 then srvTokRights E m.index else srvTokRights E (ciEff γ st.k)) }}

end spec

end EtcdGrove
end Perennial
