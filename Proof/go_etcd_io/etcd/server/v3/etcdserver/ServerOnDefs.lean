/-
**The server's mode-indexed read-side vocabulary** (strict M1, 2026-11-06: split off `ServerOn`,
unchanged, so that the read side, `ReadOn`, does not import the built part and the boot, `InvBuild`,
`BuildGap`, `BuildAlloc`): the applied index's invariant in the auth mode `on`
(`kvLogAtM`, `kvLogsOkM`, `appliedPubM`, `kvLogsPubM`, `srvAppliedBodyM`, `srvAppliedInvM`, with
`kvLogsPubM_ok` and `appliedLogAt_kvLogAtM`, from `AppliedOn`), the server's uber-applier's auth
layer and contracts (`srvUberBase`, `srvLessorNil`, `srvUberOn`) and the KV invariants of the mode
(`srvKVInvsM`), and the certificates' invariant of the mode (`kvCertInvM`). `ServerOn` imports it; its text and the names are `ServerOn`'s.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelM
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BaseAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthReqDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section appliedM
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The KV log `L` applied through the index `i` is the mode's KV model of a committed raft
log** (persistent; `kvLogAt` at `false`). -/
def kvLogAtM (on : Bool) (γr : ReadNames) (i : w64) (L : mvcc.Log) : IProp GF :=
  iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
    ⌜uint.Z i = uint.Z γr.raft.ai0 + A.length ∧ L = kvModelM on γr.kv A⌝)

instance kvLogAtM_persistent (on : Bool) (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    Persistent (kvLogAtM (GF := GF) on γr i L) := by
  unfold kvLogAtM; infer_instance

theorem kvLogAtM_false (γr : ReadNames) (i : w64) (L : mvcc.Log) :
    kvLogAtM (GF := GF) false γr i L = kvLogAt γr i L := rfl

/-- **The applied logs are the mode's KV models of committed raft logs** (`kvLogsOk` at
`false`). -/
def kvLogsOkM (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) : IProp GF :=
  iprop(∃ Lb : List EntryModel, srvRLogLb γr.raft Lb ∗
    ⌜∀ k L, M.lookup k = some L → ∃ A, A <+: Lb ∧
      uint.Z k = uint.Z γr.raft.ai0 + A.length ∧ L = kvModelM on γr.kv A⌝)

instance kvLogsOkM_persistent (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    Persistent (kvLogsOkM (GF := GF) on γr M) := by
  unfold kvLogsOkM; infer_instance

instance kvLogsOkM_timeless (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    Timeless (kvLogsOkM (GF := GF) on γr M) := by
  unfold kvLogsOkM; infer_instance

theorem kvLogsOkM_false (γr : ReadNames) (M : GMap w64 mvcc.Log) :
    kvLogsOkM (GF := GF) false γr M = kvLogsOk γr M := rfl

/-- **The auth state at the log applied through `i` is published** (persistent; the auth plan's
E3u, 2026-10-27): in the mode `on`, a committed raft log `A` through `i` whose model's auth state is
published (`authPubAt`); `True` at `false`. The applied index's invariant holds it of the current
applied index, so a linearizable reader, which waits for the applied index to reach its read index
before its auth check, gets a lower bound of the published index without a write of its own. -/
def appliedPubM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (i : w64) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ A : List EntryModel, srvRLogLb γr.raft A ∗
      ⌜uint.Z i = uint.Z γr.raft.ai0 + A.length⌝ ∗
      authPubAt E.authMode (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) A).1)

instance appliedPubM_persistent (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (i : w64) :
    Persistent (appliedPubM (GF := GF) on E γr i) := by
  cases on <;> unfold appliedPubM <;> infer_instance

instance appliedPubM_timeless (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (i : w64) :
    Timeless (appliedPubM (GF := GF) on E γr i) := by
  cases on <;> unfold appliedPubM <;> infer_instance

/-- **The applied logs, and in the mode `on` the auth state at the current one published**
(`kvLogsOk` at `false`, by definition; `kvLogsOkM on` and `appliedPubM on` of the current applied
index `a`, `kvLogsPubM_iff`). -/
def kvLogsPubM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (M : GMap w64 mvcc.Log) (a : w64) :
    IProp GF :=
  match on with
  | false => kvLogsOk γr M
  | true => iprop(kvLogsOkM true γr M ∗ appliedPubM true E γr a)

instance kvLogsPubM_persistent (on : Bool) (E : apply.AEnv GF) (γr : ReadNames)
    (M : GMap w64 mvcc.Log) (a : w64) : Persistent (kvLogsPubM (GF := GF) on E γr M a) := by
  cases on <;> unfold kvLogsPubM <;> infer_instance

instance kvLogsPubM_timeless (on : Bool) (E : apply.AEnv GF) (γr : ReadNames)
    (M : GMap w64 mvcc.Log) (a : w64) : Timeless (kvLogsPubM (GF := GF) on E γr M a) := by
  cases on <;> unfold kvLogsPubM <;> infer_instance

theorem kvLogsPubM_iff (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (M : GMap w64 mvcc.Log)
    (a : w64) :
    kvLogsPubM (GF := GF) on E γr M a ⊣⊢ kvLogsOkM on γr M ∗ appliedPubM on E γr a := by
  cases on
  · show kvLogsOk γr M ⊣⊢ kvLogsOkM false γr M ∗ iprop(True)
    rw [kvLogsOkM_false]
    exact ⟨by iintro H; iframe H, by iintro ⟨H, -⟩; iexact H⟩
  · exact .rfl

/-- `kvLogsPubM` at a new current applied index `a'`, with the auth state there published (E3u;
`setAppliedIndex`). -/
theorem kvLogsPubM_move (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (M : GMap w64 mvcc.Log)
    (a a' : w64) :
    kvLogsPubM (GF := GF) on E γr M a ∗ appliedPubM on E γr a' ⊢ kvLogsPubM on E γr M a' := by
  iintro ⟨H, #Hp⟩
  icases (kvLogsPubM_iff on E γr M a).1 $$ H with ⟨#Hk, -⟩
  iapply (kvLogsPubM_iff on E γr M a').2
  iframe Hk Hp

/-- The auth state at the start published, at the applied index `0` (E3u; the start's raft log
empty). -/
theorem appliedPubM_zero (on : Bool) (E : apply.AEnv GF) (γr : ReadNames)
    (hai : γr.raft.ai0 = W64 0) :
    srvRLogLb (GF := GF) γr.raft [] ⊢ authPubAt E.authMode srvAuthSt0 -∗ appliedPubM on E γr (W64 0) := by
  cases on
  · iintro - -; unfold appliedPubM; itrivial
  · iintro #HL #Hp
    unfold appliedPubM
    iexists []
    iframe HL
    isplitr
    · ipureintro; rw [hai]; simp
    simp only [kvRaftOfOn_nil]
    iexact Hp

/-- **The applied index's invariant's body in the mode `on`** (`srvAppliedBody` at `false`): its
applied logs the mode's KV models and, with auth on, the auth state at the current one published
(`kvLogsPubM`, E3u). -/
def srvAppliedBodyM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ (v a : w64) (L : mvcc.Log) (M : GMap w64 mvcc.Log) (p : Bool),
    sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) v ∗
    monoNatAuthOwn γr.applied (1 : Qp).half (uint.nat a) ∗
    ghostMapAuth γr.logs 1 M ∗ ghostVar γr.pend (1 : Qp).half p ∗
    ⌜uint.Z v ≤ uint.Z a ∧ appliedKeysOk M a p ∧ appliedMonoMap M⌝ ∗
    appliedLogAt γr a L ∗ srvApi.kvLogLb E.γs L ∗ kvLogsPubM on E γr M a)

theorem srvAppliedBodyM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAppliedBodyM (GF := GF) false s E γr = srvAppliedBody s E γr := rfl

/-- **The applied index's invariant in the mode `on`** (`srvAppliedInv` at `false`). -/
def srvAppliedInvM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  inv srvN (srvAppliedBodyM on s E γr)

instance srvAppliedInvM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAppliedInvM on s E γr) := by
  unfold srvAppliedInvM; infer_instance

theorem srvAppliedInvM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAppliedInvM (GF := GF) false s E γr = srvAppliedInv s E γr := rfl

end appliedM

section appliedLemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The applied logs of `kvLogsPubM` (E3u). -/
theorem kvLogsPubM_ok (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (M : GMap w64 mvcc.Log)
    (a : w64) : kvLogsPubM (GF := GF) on E γr M a ⊢ kvLogsOkM on γr M := by
  iintro H
  icases (kvLogsPubM_iff on E γr M a).1 $$ H with ⟨H, -⟩
  iexact H

/-- **An applied log is the mode's KV model of the committed raft log through its index**
(`appliedLogAt_kvLogAt`'s counterpart). -/
theorem appliedLogAt_kvLogAtM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (i : w64) (L1 : mvcc.Log) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ appliedLogAt γr i L1 ={⊤}=∗ kvLogAtM on γr i L1 := by
  iintro #Hinv #H1
  iunfold srvAppliedInvM at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  ihave %Hm1 : iprop(⌜M.lookup i = some L1⌝) $$ [HM]
  · iunfold appliedLogAt at H1
    iapply ghost_map_lookup $$ HM H1
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBodyM
    iexists vat, v, L, M, p
    iframe Hat Hauth HM Hp HL Hc Hkl
    ipureintro; exact HMk
  imodintro
  ihave #Hkl := kvLogsPubM_ok on E γr M v $$ Hkl
  iunfold kvLogsOkM at Hkl
  icases Hkl with ⟨%Lb, #Hlb, %Hm⟩
  obtain ⟨A, hA, h1, h2⟩ := Hm i L1 Hm1
  iunfold kvLogAtM
  iexists A
  isplitr
  · iapply srvRLogLb_mono γr.raft A Lb hA $$ Hlb
  ipureintro; exact ⟨h1, h2⟩

end appliedLemmas

section uber
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's uber-applier's base applier's auth layer** (the auth plan's E3k; persistent):
its store and lessor the server's `authStore` and `lessor` fields' (`apply.uberBaseAuth`), what the
apply thread's latest-state KV triples come from (`apply.uberKVL_of_base`); with the store's
checks at the latest state in the environment's mode (`authStoreLatestM`, E3l: with auth on, of the
store's invariant), its range check at a reader's lower bound (`authStoreLbM`, E3s) and publication
(`authPublishM`, E3t), and (E3zb) with auth on, its request side bound to the request context's token
(`isReqAuthBound`, of the store's invariant: the header a request is stamped with names its
context's principal). -/
def srvUberBase (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ au le : GoInterface, srvAuthStoreAddr s ↦□ au ∗ srvLessorAddr s ↦□ le ∗
    apply.uberBaseAuth ua E au le ∗ authStoreLbM E.authMode au E.RD ∗
    ∃ stl : Loc, ⌜au = auth.authIface stl⌝ ∗ authPublishM E.authMode stl ∗
      authStoreLatestM E.authMode au E.RD stl ∗
      □ (⌜E.authMode.isOn = true⌝ → isReqAuthBound au E.RD E.authMode))

instance srvUberBase_persistent (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) :
    Persistent (srvUberBase s ua E) := by
  unfold srvUberBase; infer_instance

/-- **The server's lessor finds no lease** (persistent; a named premise, see `UberOn.lean`). -/
def srvLessorNil (s : Loc) : IProp GF :=
  iprop(∃ le : GoInterface, srvLessorAddr s ↦□ le ∗ apply.lookupNil le)

instance srvLessorNil_persistent (s : Loc) : Persistent (srvLessorNil (GF := GF) s) := by
  unfold srvLessorNil; infer_instance

/-- (step 6 of the auth-mode merge, 2026-10-30) **The server's uber-applier's latest-state `Apply`
contracts, with auth on** (persistent): for every environment with auth on and every uber-applier
the server holds (`applySnapshot` replaces it) with its base applier's auth layer (`srvUberBase`),
its KV contract (`apply.uberKVC`) given that the lessor finds no lease, and its admin contract
(`apply.uberAdmC`) at every admin row's store, backend and write token. Whoever constructs the
uber-applier establishes its contract: `NewServer` with auth on (`uberKitM`); `applyEntryNormal`
reads it (`srvKVInvsM_uberOn`). (Strict M1, 2026-11-06: the admin contract at the environment's
batch lock invariant, one for every backend of the epoch, `⌜E.Pk = fun _ => Pk⌝`, as
`srvAuthApplyResB`'s.) -/
def srvUberOn (s : Loc) : IProp GF :=
  iprop(□ ∀ (E : apply.AEnv GF) (γa : auth.AuthNames) (ua : GoInterface), ⌜E.authMode = .on γa⌝ →
    srvUberBase s ua E -∗
    (srvLessorNil s -∗ ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        apply.uberKVC ua E (.quota .backend) (auth.latestRes stl (.on γa))) ∗
    (∀ (stl bel : Loc) (T Pk : IProp GF), ⌜E.Pk = fun _ => Pk⌝ -∗
        srvAuthStoreAddr s ↦□ auth.authIface stl -∗
        apply.isAuthStepsX (auth.authIface stl) Pk E.f (.on γa) (auth.tieRes stl (.on γa))
          (adminW stl bel (.on γa) Pk E.f T) E.RD -∗
        apply.uberAdmC ua E (adminW stl bel (.on γa) Pk E.f T)
          (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
          (auth.latestRes stl (.on γa))))

instance srvUberOn_persistent (s : Loc) : Persistent (srvUberOn (GF := GF) s) := by
  unfold srvUberOn; infer_instance

/-- **The apply thread's KV invariants in the auth mode `on`**: `srvKVInvs`, or at `on = true`
`srvKVInvsOn` from `srvAuthSt0` (the mode's KV and certificates' invariants, and the auth history's
tie to the log, `authHistTie`) with (step 6 of the auth-mode merge, 2026-10-30) the server's
uber-applier contracts (`srvUberOn s`). -/
def srvKVInvsM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  match on with
  | false => srvKVInvs E γr
  | true => iprop(srvKVInvsOn E γr srvAuthSt0 ∗ srvUberOn s)

instance srvKVInvsM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvKVInvsM (GF := GF) on s E γr) := by
  cases on <;> unfold srvKVInvsM <;> infer_instance

theorem srvKVInvsM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) false s E γr = srvKVInvs E γr := rfl

/-- `srvKVInvsM true`'s KV invariants. -/
theorem srvKVInvsM_true (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) true s E γr ⊢ srvKVInvsOn E γr srvAuthSt0 := by
  unfold srvKVInvsM; iintro ⟨#H, -⟩; iexact H

/-- `srvKVInvsM true`'s uber-applier contracts. -/
theorem srvKVInvsM_uberOn (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) true s E γr ⊢ srvUberOn s := by
  unfold srvKVInvsM; iintro ⟨-, #H⟩; iexact H

/-- **The row's KV contract** at an uber-applier of the server (`srvUberBase`), given that the
lessor finds no lease. -/
theorem srvUberOn_kv (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ua : GoInterface)
    (hM : E.authMode = .on γa) :
    srvUberOn (GF := GF) s ∗ srvUberBase s ua E ∗ srvLessorNil s ⊢
      ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        apply.uberKVC ua E (.quota .backend) (auth.latestRes stl (.on γa)) := by
  iintro ⟨#H, #Hb, #Hln⟩
  iunfold srvUberOn at H
  ihave ⟨#Hkv, -⟩ := H $$ %E %γa %ua %hM Hb
  iapply Hkv $$ Hln

/-- **The row's admin contract** at an uber-applier of the server (`srvUberBase`), at an admin
row's store, backend and write token. -/
theorem srvUberOn_adm (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ua : GoInterface)
    (stl bel : Loc) (T Pk : IProp GF) (hM : E.authMode = .on γa) (hPk : E.Pk = fun _ => Pk) :
    srvUberOn (GF := GF) s ∗ srvUberBase s ua E ∗ srvAuthStoreAddr s ↦□ auth.authIface stl ∗
      apply.isAuthStepsX (auth.authIface stl) Pk E.f (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl bel (.on γa) Pk E.f T) E.RD ⊢
      apply.uberAdmC ua E (adminW stl bel (.on γa) Pk E.f T)
        (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
        (auth.latestRes stl (.on γa)) := by
  iintro ⟨#H, #Hb, #Hf, #Hsteps⟩
  iunfold srvUberOn at H
  ihave ⟨-, #Had⟩ := H $$ %E %γa %ua %hM Hb
  iapply Had $$ %stl %bel %T %Pk %hPk Hf Hsteps

/-- **The certificates' invariant in the auth mode `on`**: `kvCertInv` off, `kvCertInvOn` on. -/
def kvCertInvM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) :
    IProp GF :=
  match on with
  | false => kvCertInv γ γk
  | true => kvCertInvOn γ γk st₀

instance kvCertInvM_persistent (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) : Persistent (kvCertInvM (GF := GF) on γ γk st₀) := by
  cases on <;> unfold kvCertInvM <;> infer_instance

end uber

end EtcdGrove
end Perennial
