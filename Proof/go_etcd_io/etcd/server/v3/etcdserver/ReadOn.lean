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
  `isServerRead` at `on = false`, by definition).

**Additive.** Nothing mode-off changes.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

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

end lemmas

end EtcdGrove
end Perennial
