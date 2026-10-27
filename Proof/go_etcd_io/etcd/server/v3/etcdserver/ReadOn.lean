/-
**The read side in the auth mode `on`** (the auth plan's E3r, 2026-10-27; `notes/decisions.md`,
"E3r of the auth plan"). A reader deposits its update with the read index (`kvDep`), and the read
loop fires every deposited update at the state of the committed log (`readCompose`); the read side
is generic in the state function `F` of the deposits (`kvDep`, `regOk`, `readInv`, `isReadNotify`,
... take it, by default the mode `off`'s, `kvStOff`). With auth on the KV invariant's state is the
mode-`on` model's (`kvInvOn`), so the deposits are at `kvStOn`.

- `kvStOn`, `kvStM`: the state function of the mode (`kvStM false` is `kvStOff`);
- `kv_read_compose_on`: the read loop's update from `kvInvOn` (`kv_read_compose`'s);
- `srvReadFieldsAtM`, `isServerReadM`: the reader's view with the read notifier at the mode's
  state function, the applied index's invariant and the KV invariants of the mode (`srvReadFieldsAt`,
  `isServerRead` at `on = false`, by definition);
- (E3s, 2026-10-27) what a reader with auth on reads: `readWit_fireOn` (`readWit_fire`'s: the
  deposit's result at a committed raft log whose mode-`on` model is the log read, through
  `kv_read_logOn`), `rangeReadOkM` (`rangeReadOk` over the mode's model), and the store's range
  check at a reader's lower bound as the server keeps it (`srvAuthLb`, from the built part's
  `srvUberBase`).

**Additive.** Nothing mode-off changes.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The KV state of the committed log `L` in the auth mode `on`**: the mode-`on` model's, from
the start's auth state `st₀` (`kvInvOn`'s ghost state). -/
@[reducible] def kvStOn (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) : KVState :=
  kvStateOf (kvModelOn γk st₀ L)

/-- **The deposits' state function in the auth mode `on`**: `kvStOff` at `false`, `kvStOn` from the
server's start state `srvAuthSt0` at `true`. -/
def kvStM (on : Bool) (γk : KVNames) : List EntryModel → KVState :=
  match on with
  | false => kvStOff γk
  | true => kvStOn γk srvAuthSt0

theorem kvStM_false (γk : KVNames) : kvStM false γk = kvStOff γk := rfl
theorem kvStM_true (γk : KVNames) : kvStM true γk = kvStOn γk srvAuthSt0 := rfl

/-- **The server, as a reader sees it, in the auth mode `on`** (`srvReadFieldsAt` with the read
notifier at the mode's state function, `srvAppliedInvM` and `srvKVInvsM`). -/
def srvReadFieldsAtM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v : ReadFields) :
    IProp GF :=
  iprop(srvReadAddr s ↦□ v.read ∗ isReadNotify v.read γr (kvStM on γr.kv) ∗
    srvKVAddr s ↦□ v.kv ∗ txn.isKV v.kv E.s E.γ ∗
    E.s.[go_etcd_io.etcd.server.v3.storage.mvcc.store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.readView.ty)
        #v.rv : GoInterface) ∗
    mvcc.isReadView v.rv E.s E.γ ∗
    srvLessorAddr s ↦□ v.lessor ∗ apply.isApplyLessor v.lessor E.s E.γ E.P E.f E.RW ∗
    srvAuthStoreAddr s ↦□ v.auth ∗ apply.isAuthStore v.auth E.γ E.P E.f E.RD E.authMode E.RW ∗
    srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
    srvCfgFieldAddr s go!"WarningApplyDuration" ↦□ v.wad ∗
    inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    storeSmall E.γ ∗
    (∃ log₀ : mvcc.Log, mvcc.idxCert E.γ.idx log₀ ∗ ⌜2 ≤ log₀.length⌝) ∗
    srvAppliedInvM on s E γr ∗ srvKVInvsM on E γr ∗ srvCommittedInv s γr ∗
    srvApplyWaitAddr s ↦□ v.aw ∗ isWaitTime v.aw (appliedAtLeast γr) ∗
    srvLeaderChangedAddr s ↦□ v.lc ∗ srvFirstCommitAddr s ↦□ v.fc ∗
    srvStoppingAddr s ↦□ v.stopping ∗ stopChan v.stopping)

instance srvReadFieldsAtM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (v : ReadFields) : Persistent (srvReadFieldsAtM on s E γr v) := by
  unfold srvReadFieldsAtM; infer_instance

theorem srvReadFieldsAtM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v : ReadFields) :
    srvReadFieldsAtM (GF := GF) false s E γr v = srvReadFieldsAt s E γr v := rfl

/-- **The server, as a reader sees it, in the auth mode `on`** (persistent). -/
def isServerReadM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(∃ v : ReadFields, srvReadFieldsAtM on s E γr v)

instance isServerReadM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (isServerReadM (GF := GF) on s E γr) := by
  unfold isServerReadM; infer_instance

theorem isServerReadM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    isServerReadM (GF := GF) false s E γr = isServerRead s E γr := rfl

/-- **The store's range check at a reader's lower bound, as the server keeps it** (the auth plan's
E3s, 2026-10-27; persistent): the server's `authStore` field and `authStoreLbM` of it (with auth on,
`IsRangePermitted`'s verdict no older than any lower bound of the published index). -/
def srvAuthLb (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ au : GoInterface, srvAuthStoreAddr s ↦□ au ∗ authStoreLbM E.authMode au E.RD)

instance srvAuthLb_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvAuthLb (GF := GF) s E) := by
  unfold srvAuthLb; infer_instance

/-- **A successful `Range` in the auth mode `on`** (`rangeReadOk` with the deposit's committed log
`L` at the mode's model, `kvModelM on`; `rangeReadOk` at `on = false`, by definition). -/
def rangeReadOkM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (resp : Loc) (Q : List EntryModel → IProp GF) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert E.γ.idx log ∗ mvcc.certOk E.γ log ∗
    ⌜2 ≤ log.length ∧ log.length + 3 ≤ 2 ^ 63 ∧ F <+: log⌝ ∗
    (if o.base.serializable then iprop(True) else readLogOk γr c log) ∗
    (if o.base.serializable then iprop(True) else
      ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM on γr.kv L = log⌝ ∗ □ Q L) ∗
    txn.rangeResult resp GoInterface.nil log (W64 ((log.length : Int) - 1)) o true ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" resp))

theorem rangeReadOkM_false (E : apply.AEnv GF) (γr : ReadNames) (c : w64) (F : mvcc.Log)
    (o : OpFull) (resp : Loc) (Q : List EntryModel → IProp GF) :
    rangeReadOkM (GF := GF) false E γr c F o resp Q = rangeReadOk E γr c F o resp Q := rfl

/-- **The auth state at an applied log through an index at least `c` is published** (persistent;
the auth plan's E3u): what a linearizable read waiting for the read index `c` finds in the applied
index's invariant (`appliedPubM`). -/
def appliedPubFrom (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(∃ i : w64, ⌜uint.Z c ≤ uint.Z i⌝ ∗ appliedPubM on E γr i)

instance appliedPubFrom_persistent (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    Persistent (appliedPubFrom (GF := GF) on E γr c) := by
  unfold appliedPubFrom; infer_instance

/-- **A floor of a linearizable read's auth check** (persistent; the auth plan's E3u): in the mode
`on γa`, the model's auth state at a committed raft log through an index at least the read index `c`
is recorded in the store's history at an index at most `m`; so a check whose verdict comes from
states at indices at least `m` (`apply.rangeClassFrom M m`) saw a state no older than the one the
committed log through the read index left. `True` in the other modes. -/
def authFloorAt (M : auth.AuthMode) (γr : ReadNames) (c : w64) (m : Nat) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (A : List EntryModel) (i : Nat), srvRLogLb γr.raft A ∗
      ⌜uint.Z c ≤ uint.Z γr.raft.ai0 + A.length ∧ i ≤ m⌝ ∗
      auth.authStateAt γa i (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) A).1)
  | _ => iprop(True)

instance authFloorAt_persistent (M : auth.AuthMode) (γr : ReadNames) (c : w64) (m : Nat) :
    Persistent (authFloorAt (GF := GF) M γr c m) := by
  cases M <;> unfold authFloorAt <;> infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Firing every registered read update at the state of `L`'s mode-`on` model, the KV authority's
half agreeing (`kv_fire_reads`'s). -/
theorem kv_fire_reads_on (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel) :
    ∀ gs : List GName,
      ⊢ ghostVar (GF := GF) γk.st (1 : Qp).half (kvStOn γk st₀ L) -∗
        ([∗list] g ∈ gs, regOk γk g (kvStOn γk st₀)) -∗
        |={(⊤ \ ↑srvRaftN) \ ↑kvN}=> ghostVar γk.st (1 : Qp).half (kvStOn γk st₀ L) ∗
          readQs gs L
  | [] => by
    iintro Hσ -
    imodintro
    iframe Hσ
    unfold readQs
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | g :: gs => by
    iintro Hσ #Hgs
    icases (BigSepL.bigSepL_cons (Φ := fun _ g => regOk (GF := GF) γk g (kvStOn γk st₀))).1 $$ Hgs
      with ⟨#Hg, #Hgs'⟩
    iunfold regOk at Hg
    icases Hg with ⟨%Q, #HQ, #Hd⟩
    iunfold kvDep at Hd
    icases Hd with (⟨%Q0, %HQeq, #Hau⟩ | %HQeq)
    rotate_left
    · imod kv_fire_reads_on γk st₀ L gs $$ Hσ Hgs' with ⟨Hσ, #Hrest⟩
      imodintro
      iframe Hσ
      unfold readQs
      iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
        savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L))).2
      isplitl []
      · iexists Q
        iframe HQ
        rw [HQeq]
        iintro !>; itrivial
      · iexact Hrest
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hc, Hucl⟩
    iunfold etcdKV at Hc
    ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ Hc
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    imod Hcommit $$ [Hc] with #HQ0
    · iunfold etcdKV; iexact Hc
    imod kv_fire_reads_on γk st₀ L gs $$ Hσ Hgs' with ⟨Hσ, #Hrest⟩
    imodintro
    iframe Hσ
    unfold readQs
    iapply (BigSepL.bigSepL_cons (Φ := fun _ g => iprop(∃ Q : List EntryModel → IProp GF,
      savedPredOwn (GF := GF) g DFrac.discard Q ∗ □ Q L))).2
    isplitl []
    · iexists Q
      iframe HQ
      rw [HQeq]
      iintro !> !>
      rw [Hag]
      iexact HQ0
    · iexact Hrest

/-- The clients' results are ones the server's two logs agree on, in the mode `on`
(`readQs_qinv`'s, through `kvRaftOfOn_eqv`). -/
theorem readQs_qinv_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (gs : List GName) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ ([∗list] g ∈ gs, regOk γk g (kvStOn γk st₀)) -∗
      srvQInv γ (readQs gs) := by
  iintro #Hinv #Hgs
  iunfold srvQInv
  iintro !> %A %B %Hab #HA
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  ihave HB := readQs_eqv γk (kvStOn γk st₀) A B
    (by simp only [kvStOn, kvModelOn,
      kvRaftOfOn_eqv γ γk.c0 γk.ch0 (st₀, γk.log0) A B Hab Hok.2.2.2.1]) gs $$ Hgs HA
  imodintro
  inext
  iintro !>
  iexact HB

/-- **One read update for the registered clients `gs`, from the KV invariant in the mode `on`**
(`kv_read_compose`'s): at every firing, every client's read update is fired in turn at the state of
the mode-`on` model. -/
theorem kv_read_compose_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (gs : List GName) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ ([∗list] g ∈ gs, regOk γk g (kvStOn γk st₀)) -∗
      srvReadAu γ (readQs gs) := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hgs
  unfold srvReadAu
  isplitr
  rotate_left
  · iapply readQs_qinv_on γ γk st₀ gs $$ Hinv Hgs
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod kv_fire_reads_on γk st₀ L gs $$ Hσ Hgs with ⟨Hσ, #HQs⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    iintro !>
    iexact HQs

/-- **The read loop's update with auth on** (`readCompose` at the mode-`on` state function), from
the KV invariants in the mode. -/
theorem readCompose_on (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) true E γr ⊢ readCompose γr (kvStM true γr.kv) := by
  rw [srvKVInvsM_true, kvStM_true]
  iintro #Hkvi
  iunfold srvKVInvsOn at Hkvi
  icases Hkvi with ⟨#HkvI, -⟩
  iunfold readCompose
  iintro !> %gs #Hgs
  iapply kv_read_compose_on γr.raft γr.kv srvAuthSt0 gs $$ HkvI Hgs

/-- The server's range check at a reader's lower bound, from the built part's store fact. -/
theorem srvAuthLb_of_uberBase (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) :
    srvUberBase (GF := GF) s ua E ⊢ srvAuthLb s E := by
  iintro #Hb
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, -, -, #HLb, -⟩
  iunfold srvAuthLb
  iexists au
  iframe Hauf HLb

/-- `readIndexOk_log` over the mode's applied index's invariant. -/
theorem readIndexOk_logM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ readIndexOk γr c ={⊤}=∗
      ∃ (ci₀ : w64) (L₀ : mvcc.Log), ⌜uint.Z c ≤ uint.Z ci₀⌝ ∗ appliedLogAt γr ci₀ L₀ ∗
        mvcc.idxCert E.γ.idx L₀ ∗ appliedPubM on E γr ci₀ := by
  iintro #Hinv #Hok
  iunfold readIndexOk at Hok
  icases Hok with ⟨%ci, %Hci, #Hlb⟩
  iunfold srvAppliedInvM at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  iunfold appliedAtLeast at Hlb
  ihave %Hle := monoNatLbOwn_valid γr.applied _ _ _ $$ Hauth Hlb
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext; iunfold srvAppliedBodyM; iexists vat, v, L, M, p; iframe Hat Hauth HM Hp HL Hc Hkl
    ipureintro; exact HMk
  ihave ⟨-, #Hpub⟩ := (kvLogsPubM_iff on E γr M v).1 $$ Hkl
  imodintro
  iexists v, L
  iframe HL Hc Hpub
  ipureintro
  have h2 := Hle.2
  word

/-- `readIndexOk_logR` over the mode's applied index's invariant. -/
theorem readIndexOk_logRM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64)
    (log₀ : mvcc.Log) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ readIndexOk γr c -∗ mvcc.idxCert E.γ.idx log₀ ={⊤}=∗
      ∃ logR : mvcc.Log, mvcc.idxCert E.γ.idx logR ∗ ⌜log₀ <+: logR⌝ ∗ readLogOk γr c logR ∗
        appliedPubFrom on E γr c := by
  iintro #Hinv #Hri #Hc0
  imod readIndexOk_logM on s E γr c $$ Hinv Hri with ⟨%ci₀, %L₀, %Hci, #HL, #HcL, #Hpub⟩
  ihave #HpF : appliedPubFrom on E γr c $$ []
  · iunfold appliedPubFrom; iexists ci₀; iframe Hpub; ipureintro; exact Hci
  ihave %Hpre := mvcc.idxCert_prefix E.γ.idx log₀ L₀ $$ [Hc0 HcL]
  · iframe Hc0 HcL
  imodintro
  rcases Hpre with h | h
  · iexists L₀
    iframe HcL HpF
    isplitr
    · ipureintro; exact h
    iunfold readLogOk
    iframe Hri
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨Hci, List.prefix_refl _⟩
  · iexists log₀
    iframe Hc0 HpF
    isplitr
    · ipureintro; exact List.prefix_refl _
    iunfold readLogOk
    iframe Hri
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨Hci, h⟩

/-- **The trivial lower bound** (E3u): any reader may take `0`; with `authFloorAt`, `Range.specOn`
at `n = 0` still checks a linearizable read no older than its read index. -/
theorem authPubLbM_zero (M : auth.AuthMode) : ⊢ |==> auth.authPubLbM (GF := GF) M 0 := by
  cases M with
  | on γa => unfold auth.authPubLbM auth.authPubLb; exact monoNatLbOwn_0 γa.pub
  | _ => unfold auth.authPubLbM; iintro; imodintro; itrivial

/-- **A linearizable read's floor** (E3u): from the reader's bound `n` and the published auth state
at an applied log through the read index (`appliedPubFrom`), a bound `m ≥ n` with the floor at it
(the larger of `n` and the index the published state is recorded at). -/
theorem authFloor_of_pubFrom (E : apply.AEnv GF) (γr : ReadNames) (γa : auth.AuthNames) (c : w64)
    (n : Nat) (hM : E.authMode = .on γa) :
    auth.authPubLbM (GF := GF) (.on γa) n ⊢ appliedPubFrom true E γr c -∗
      ∃ m : Nat, ⌜n ≤ m⌝ ∗ auth.authPubLbM (.on γa) m ∗ authFloorAt (.on γa) γr c m := by
  iintro #Hn #HpF
  iunfold appliedPubFrom at HpF
  icases HpF with ⟨%i0, %hci, #Hpi⟩
  iunfold appliedPubM at Hpi
  icases Hpi with ⟨%A, #HA, %hA, #Hpa⟩
  ihave #Hpa' : authPubAt (GF := GF) (.on γa)
      (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) A).1 $$ []
  · rw [← hM]; iexact Hpa
  iunfold authPubAt at Hpa'
  icases Hpa' with ⟨%i, #Hlb, #Hst⟩
  have hfl : uint.Z c ≤ uint.Z γr.raft.ai0 + A.length := by omega
  by_cases hni : n ≤ i
  · iexists i
    isplitr
    · ipureintro; exact hni
    isplitr
    · iunfold auth.authPubLbM; iexact Hlb
    iunfold authFloorAt
    iexists A, i
    iframe HA Hst
    ipureintro; exact ⟨hfl, Nat.le_refl _⟩
  · iexists n
    isplitr
    · ipureintro; exact Nat.le_refl _
    iframe Hn
    iunfold authFloorAt
    iexists A, i
    iframe HA Hst
    ipureintro; exact ⟨hfl, by omega⟩

/-- `readServed_logR` over the mode's applied index's invariant. -/
theorem readServed_logRM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (c : w64)
    (g : GName) (Q : List EntryModel → IProp GF) (log₀ : mvcc.Log) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ readServed γr c g -∗ savedPredOwn g DFrac.discard Q -∗
      mvcc.idxCert E.γ.idx log₀ ={⊤}=∗
      ∃ logR : mvcc.Log, mvcc.idxCert E.γ.idx logR ∗ ⌜log₀ <+: logR⌝ ∗ readLogOk γr c logR ∗
        readWitAt γr Q g logR ∗ appliedPubFrom on E γr c := by
  iintro #Hinv #Hsv #HQ #Hc0
  iunfold readServed at Hsv
  icases Hsv with ⟨%ci, %ai, %gs, %k, %Hp, #Hai, #HW⟩
  ihave #Hri : readIndexOk γr ci $$ []
  · iunfold readIndexOk; iexists ai; iframe Hai; ipureintro; exact Hp.2.1
  imod readIndexOk_logRM on s E γr ci log₀ $$ Hinv Hri Hc0 with ⟨%logR, #HcR, %HpR, #HrlR, #HpF⟩
  iunfold appliedPubFrom at HpF
  icases HpF with ⟨%i, %hi, #Hpi⟩
  ihave #HpF : appliedPubFrom on E γr c $$ []
  · iunfold appliedPubFrom; iexists i; iframe Hpi; ipureintro; omega
  imodintro
  iexists logR
  iframe HcR HpF
  isplitr
  · ipureintro; exact HpR
  iunfold readLogOk at HrlR
  icases HrlR with ⟨#Hri', %ci₀, %L₀, %Hc, #HL, %HpL⟩
  isplitr
  · iunfold readLogOk
    isplitr
    · iunfold readIndexOk at Hri'
      icases Hri' with ⟨%c1, %Hc1, #Hl1⟩
      iunfold readIndexOk
      iexists c1; iframe Hl1; ipureintro; omega
    iexists ci₀, L₀
    iframe HL
    ipureintro; exact ⟨by omega, HpL⟩
  iunfold readWitAt
  iexists ci, ci₀, L₀, gs, k
  iframe HL HW HQ
  ipureintro; exact ⟨Hc, Hp.2.2, HpL⟩

/-- **What a linearizable read reads, in the mode `on`** (`kv_read_log`'s): a certified log `l`
extending the log `L₀` applied through `i` is the mode-`on` model of a committed raft log through an
index at least `i`. -/
theorem kv_read_logOn (γr : ReadNames) (γs : mvcc.StoreNames) (hγ : γs.cok = γr.kv.cok)
    (E : CoPset) (hE : ↑kvcN ⊆ E) (i : w64) (L₀ l : mvcc.Log) (hp : L₀ <+: l) :
    ⊢ kvCertInvOn (GF := GF) γr.raft γr.kv srvAuthSt0 -∗ kvLogAtM true γr i L₀ -∗
      mvcc.certOk γs l ={E}=∗
      ∃ A, srvRLogLb γr.raft A ∗
        ⌜kvModelM true γr.kv A = l ∧ uint.Z i ≤ uint.Z γr.raft.ai0 + A.length⌝ := by
  iintro #Hinv #Hat #Hc
  iunfold kvLogAtM at Hat
  icases Hat with ⟨%AR, #HAR, %HR⟩
  ihave #Hinv' := Hinv
  iunfold kvCertInvOn at Hinv'
  iinv Hinv' with >Hi Hclose
  icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
  imod Hclose $$ [HC Hhi'] with -
  · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
  have h2 : 2 ≤ L₀.length := by
    have h1 := (kvRaftOfOn_extends γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) AR).length_le
    have h0 := Hok.2
    rw [HR.2]; unfold kvModelM kvModelOn; simp only at h1 ⊢; omega
  imod kv_cert_read_on γr.raft γr.kv srvAuthSt0 γs hγ E hE l $$ Hinv Hc
    with (%hl | ⟨%A', #HA', %hA'⟩)
  · have heq : L₀ = l := hp.eq_of_length (by have := hp.length_le; omega)
    imodintro
    iexists AR
    iframe HAR
    ipureintro; exact ⟨by rw [← heq]; exact HR.2.symm, by omega⟩
  · ihave %Hcmp := srvRLogLb_prefix γr.raft AR A' $$ [HAR HA']
    · iframe HAR HA'
    imodintro
    rcases Hcmp with h | h
    · iexists A'
      iframe HA'
      ipureintro
      exact ⟨hA', by have := h.length_le; omega⟩
    · have hk := kvRaftOfOn_prefix γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) A' AR h
      have hk' : l <+: L₀ := by
        have hR2 : L₀ = kvModelOn γr.kv srvAuthSt0 AR := HR.2
        unfold kvModelOn at hR2
        unfold kvModelOn at hA'
        rw [hA', ← hR2] at hk; exact hk
      have heq : L₀ = l := hp.eq_of_length (Nat.le_antisymm hp.length_le hk'.length_le)
      iexists AR
      iframe HAR
      ipureintro; exact ⟨by rw [← heq]; exact HR.2.symm, by omega⟩

/-- **A served read's result at the log it read, in the mode `on`** (`readWit_fire`'s): `l` is the
mode-`on` model of a committed raft log `L`, and raft's witness gives the client's `□ Q L`. -/
theorem readWit_fireOn (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (Q : List EntryModel → IProp GF) (g : GName) (l : mvcc.Log) :
    ⊢ srvAppliedInvM (GF := GF) true s E γr -∗ srvKVInvsM true E γr -∗ readWitAt γr Q g l -∗
      mvcc.certOk E.γ l -∗ £ 6
      ={⊤}=∗ ∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜kvModelM true γr.kv L = l⌝ ∗ □ Q L := by
  rw [srvKVInvsM_true]
  iintro #Hainv #Hkvi #Hw #Hc Hlc
  iunfold srvKVInvsOn at Hkvi
  icases Hkvi with ⟨-, #HcI, -, %Hcok⟩
  iunfold readWitAt at Hw
  icases Hw with ⟨%ci, %ci₀, %L₀, %gs, %k, %Hp, #HL, #HW, #HQ⟩
  imod appliedLogAt_kvLogAtM true s E γr ci₀ L₀ $$ Hainv HL with #HkL
  imod kv_read_logOn γr E.γ Hcok ⊤ (fun _ _ => CoPset.mem_full) ci₀ L₀ l Hp.2.2 $$ HcI HkL Hc
    with ⟨%A, #HA, %HAp⟩
  iunfold srvReadWit at HW
  icases (lc_split (n := 5) (m := 1)).1 $$ Hlc with ⟨Hlc2, Hlc1⟩
  imod HW $$ %A HA %(by omega) Hlc2 with #HQs
  ihave HQL := readQs_get gs A k g Q Hp.2.1 $$ HQs HQ
  imod lc_fupd_elim_later $$ Hlc1 HQL with #HQL
  imodintro
  iexists A
  iframe HA HQL
  ipureintro; exact HAp.1

end lemmas

end EtcdGrove
end Perennial
