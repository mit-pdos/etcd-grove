/- Lean-first (no Rocq counterpart).

# The shared handle (wal-link L1a, 2026-11-17; `notes/wal-link-scope.md` §3.2, §8)

etcd's server writes its WAL from two threads at once (the raft loop's `Save`/`SaveSnapshot`/`Sync`, the apply
thread's `SaveSnapshot`/`ReleaseLockTo`), each under the storage's *read* lock; what serializes them is `w.mu`,
which `Save`, `SaveSnapshot`, `Sync`, `ReleaseLockTo` and `Close` take first (S/wal.go:1003-1105; Go evidence
C2, `examples/wallink/link_test.go`). So the specs of those five methods take a **share** of the handle:

* `walOpenWS Sio P Mr w dir γ q`: a fraction `q` of the token `γ.γ`, the invariant `walShInv`, and the
  persistent facts the methods use before they hold the lock (`w.mu`'s `isMutex` with invariant `True`, the
  `sync` package's initialization, `SegmentSizeBytes`). The mutex's own invariant stays `True` (`Create`
  allocates it, and calls `SaveSnapshot` on its pre-handle, before any share exists).
* `walShInv`: the handle (`walHdl`) with the lock state `γ.γl ↦ false` (whole), or `w.mu`'s lock token
  (`ownMutex`, exclusive) with half of `γ.γl ↦ true`, or the whole token `γ.γ` (closed). After `w.mu.Lock()` a method
  swaps its lock token in and takes the handle out (`walOpenWS_acquire`), keeping the other half
  `walHeld γ := γ.γl ↦ true`; before `Unlock` it swaps back (`walOpenWS_release`); `Close`, with the whole
  share, leaves the whole token (`walOpenWS_finish`), so no later share finds a handle.
* `walHdl Sio …`: the handle (`walOpenWF`) when the no-I/O-error set `Sio` does not cover every inode, else
  the handle with the fresh room (`walOpenWFR … walFreshRoom`: the no-error specs need the pending bytes to end
  before `maxBytes`, where a write fails with `EFBIG` whatever the premise). Every method that writes leaves
  the tail below `SegmentSizeBytes` or cuts (`Save`, and `SaveSnapshot` since the fork's fix 0007), so the room
  is fresh again at every unlock. The specs' one form, parameterised by `Sio`, is error-free exactly when
  `walCov Sio` (§8). `walOpenWS_alloc` shares a handle given as `walHdl`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleRoom
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- The ghost names of a shared handle: the shares' token and the lock-state variable. -/
structure WalShN where
  γ : GName
  γl : GName
  /-- The WAL's incarnation (P6b, `notes/wal-p6b-design.md`): the shared handle's state's `inc`. -/
  inc : Nat

/-- **The states of a handle `Close` takes** (`WAL.Close.spec`, one spec over them; wal-link L1a): the whole
share of an open WAL (`shared`), a failed `ReadAll`'s handle (`failed`), `Open`'s handle before `ReadAll`
(`opening`, at its decoder's start `s`), `Create`'s handle before naming (`unnamed`, with the roots `Rp`,
fraction `qp` and tail file `tf` `Create` lent, at the incarnation `i`). -/
inductive WalCloseSt where
  | shared (γ : WalShN)
  | failed
  | opening (s : w64 × w64)
  | unnamed (Rp : Roots) (qp : Qp) (tf : Loc) (i : Nat)

/-- **The states of a handle `SaveSnapshot` takes** (`WAL.SaveSnapshot.spec`, one spec over them; wal-link
L1a): a share `q` of an open WAL (`shared`), or `Create`'s `w` before the rename (`pre`: its logger, metadata,
encoder `e`, locked file `lt` of the `*os.File` `f`, indices (`walPreIn`); the writer's states `W`/`B` and
what an fdatasync makes of them `S`, its bound `lim`, what it holds `out`, the encoder's pending bytes `pend`
and CRC `c`; `WAL__SaveSnapshotPre.lean`). -/
inductive WalSnapSt (GF : BundledGFunctors) where
  | shared (γ : WalShN) (q : Qp)
  | pre (lg : Loc) (mds : GoSlice) (md : List w8) (e lt f : Loc) (snapi enti : w64)
      (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF) (S : List w8 → IProp GF)
      (lim : Nat) (out pend : List w8) (c : w32)

/-- **`Sio` covers every inode** (coverage (a), `notes/decisions.md`, "fsExt: no I/O errors on chosen
files"): the case in which the specs return no error. -/
def walCov (Sio : IoSet) : Prop := ∀ st i, Sio.ino st i

/-- **No file covered** (`NoIoErr ioNone` holds of every step: a client that assumes nothing of the I/O
errors, WalTester's, takes the specs at it). -/
def ioNone : IoSet := ⟨fun _ _ => False, fun _ => False⟩

theorem walCov_ioNone : ¬ walCov ioNone := fun h => h default 0

/-- **A no-error spec holds vacuously at `ioNone`** (its premise, that `Sio` covers every inode, fails): how
`etc/gen-link.py --wal-tester` discharges such a hypothesis of a WAL result the tester takes at `ioNone`. -/
theorem noErr_ioNone {A : Prop} : (∀ st i, ioNone.ino st i) → A := fun h => absurd h walCov_ioNone

instance fsStepSat_ioNone [ExtSemantics fsExt] : FsStepSat (NoIoErr ioNone) where
  sat := by
    intro _ _ o v _ st _ e' _ _ _ _ hc
    exfalso
    unfold IoCovers at hc
    split at hc <;> simp_all [ioNone]

/-- `NoMapLockErr ioNone` holds of every step too (no file or path covered): a client at `ioNone` (WalTester's,
`Create`'s `SaveSnapshot` call) takes the specs that assume it. -/
instance fsStepSat_ioNoneL [ExtSemantics fsExt] : FsStepSat (NoMapLockErr ioNone) where
  sat := by
    intro _ _ o v _ st _ e' _ _ _ _ hc
    exfalso
    unfold MapLockCovers at hc
    split at hc <;> simp_all [ioNone]

/-- The shared handles' invariant's namespace. -/
def walShN : Namespace := nroot .@ "walShared"

/-- Fractions as ghost values (the lock state records the holder's share). -/
instance qp_countable_walSh : Pos.Countable Qp :=
  .ofInjective (fun q : Qp => Pos.Countable.encode (q.1.num, q.1.den))
    (by
      intro a b h
      have h := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Rat.ext h.1 h.2))

/-- A share and the whole token are not valid together. -/
theorem qp_add_one_not_le (q : Qp) : ¬ (q + 1 ≤ 1) := by
  intro h
  apply Qp_one_add_not_le q
  have he : (1 : Qp) + q = q + 1 := Subtype.ext (by simp only [Qp.val_add]; exact Rat.add_comm _ _)
  rw [he]; exact h

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **The client model of a client that hands the WAL no message** (`Open`'s read-mode `Close` of its own
handle, which `WAL.Close.spec` takes at a model it ignores in that state). -/
def walPbNone : WalPbIn GF := ⟨fun _ _ => iprop(True), fun _ _ => iprop(True), fun _ _ => inferInstance, fun _ _ => inferInstance⟩

/-- **The handle a holder of `w.mu` finds** (see the file header); also the handle before it is shared
(`walOpenWS_alloc`'s input). -/
def walHdl (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (i : Nat) :
    IProp GF :=
  iprop((⌜¬ walCov Sio⌝ ∗ walOpenWFI (W := W) P Mr w dir i) ∨ walOpenWFR (W := W) P Mr w dir walFreshRoom i)

/-- `walHdl` of a handle, when `Sio` does not cover every inode. -/
theorem walHdl_of_wf (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (i : Nat) (hc : ¬ walCov Sio) :
    walOpenWFI (W := W) P Mr w dir i ⊢ walHdl (W := W) Sio P Mr w dir i := by
  unfold walHdl
  iintro Hw
  ileft
  iframe Hw
  ipureintro; exact hc

/-- **The handle a lock holder finds, unfolded**: a quiescent handle, with the fresh room when `Sio` covers
every inode. -/
theorem walHdl_open (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (i : Nat) :
    walHdl (W := W) Sio P Mr w dir i ⊢
      ∃ h : WalHS, walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⌜h.Done⌝ ∗ ⌜h.md.length < 2 ^ 41⌝ ∗
        ⧗ h.pc ∗ ⌜walCov Sio → h.o0 + h.out.length + h.pend.length + walFreshRoom ≤ maxBytes⌝ ∗
        ⌜h.inc = i⌝ := by
  unfold walHdl
  iintro Hw
  icases Hw with (⟨%hc, Hw⟩ | Hw)
  · icases (walOpenWFI_iff P Mr w dir i).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, %hi, Hr⟩
    iexists h
    iframe Hh Hr
    ipureintro; exact ⟨hD, hmd, fun h => absurd h hc, hi⟩
  · icases (walOpenWFR_iff P Mr w dir _ _).1 $$ Hw with ⟨%h, Hh, %hD, %hmd, Hr, %hb, %hi⟩
    iexists h
    iframe Hh Hr
    ipureintro; exact ⟨hD, hmd, fun _ => hb, hi⟩

/-- **The handle given back to the lock** (`walHdl_open`'s converse). -/
theorem walHdl_close (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (h : WalHS) (hD : h.Done) (hmd : h.md.length < 2 ^ 41)
    (hroom : walCov Sio → h.o0 + h.out.length + h.pend.length + walFreshRoom ≤ maxBytes) (i : Nat)
    (hi : h.inc = i) :
    walHandleIn (W := W) P Mr w dir h TailMetaW ∗ ⧗ h.pc ⊢ walHdl (W := W) Sio P Mr w dir i := by
  iintro ⟨Hh, Hr⟩
  unfold walHdl
  by_cases hc : walCov Sio
  · iright
    iapply (walOpenWFR_iff P Mr w dir _ _).2
    iexists h
    iframe Hh Hr
    ipureintro; exact ⟨hD, hmd, hroom hc, hi⟩
  · ileft
    isplitr
    · ipureintro; exact hc
    iapply (walOpenWFI_iff P Mr w dir i).2
    iexists h
    iframe Hh Hr
    ipureintro; exact ⟨hD, hmd, hi⟩

/-- **The handle of a client that assumes nothing of `Sio`** (WalTester's, between calls). -/
theorem walHdl_wf (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (i : Nat) :
    walHdl (W := W) Sio P Mr w dir i ⊢ walOpenWFI (W := W) P Mr w dir i := by
  unfold walHdl
  iintro Hw
  icases Hw with (⟨-, Hw⟩ | Hw)
  · iexact Hw
  · iapply walOpenWFR_wf P Mr w dir _ _ $$ Hw

/-- **The shared handle's invariant** (see the file header). -/
def walShInv (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (γ : WalShN) :
    IProp GF :=
  iprop((walHdl (W := W) Sio P Mr w dir γ.inc ∗ ghostVar γ.γl 1 (none : Option Qp)) ∨
    (sync.ownMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) ∗
      ∃ q : Qp, ghostVar γ.γl (1 : Qp).half (some q) ∗ ghostVar γ.γ q true) ∨
    (ghostVar γ.γ 1 true ∗ ∃ v : Option Qp, ghostVar γ.γl 1 v))

/-- **The shared handle's persistent part**: the invariant and the facts a method uses before it holds the
lock. -/
def walShPers (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (γ : WalShN) :
    IProp GF :=
  iprop(inv walShN (walShInv (W := W) Sio P Mr w dir γ) ∗
    sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) (BI.pure True : IProp GF) ∗
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000) ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal)

instance walShPers_persistent (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) : Persistent (walShPers (W := W) Sio P Mr w dir γ) := by
  unfold walShPers; infer_instance

/-- **A share `q` of the open WAL `w`** (see the file header). -/
def walOpenWS (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (γ : WalShN)
    (q : Qp) : IProp GF :=
  iprop(ghostVar γ.γ q true ∗ walShPers (W := W) Sio P Mr w dir γ)

/-- **The lock holder's half of the lock state**, recording the share it deposited (`walOpenWS_acquire`'s,
`walOpenWS_release`'s). -/
def walHeld (γ : WalShN) (q : Qp) : IProp GF := ghostVar γ.γl (1 : Qp).half (some q)

instance walHeld_timeless (γ : WalShN) (q : Qp) : Timeless (walHeld (GF := GF) γ q) := by
  unfold walHeld; infer_instance

/-- The shares are fractional. -/
theorem walOpenWS_split (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) (q1 q2 : Qp) :
    walOpenWS (W := W) Sio P Mr w dir γ (q1 + q2) ⊣⊢
      walOpenWS (W := W) Sio P Mr w dir γ q1 ∗ walOpenWS (W := W) Sio P Mr w dir γ q2 := by
  unfold walOpenWS
  constructor
  · iintro ⟨Ht, #Hp⟩
    icases (ghostVar_fractional (GF := GF) γ.γ true).fractional q1 q2 |>.1 $$ Ht with ⟨H1, H2⟩
    iframe H1 H2 Hp
  · iintro ⟨⟨H1, #Hp⟩, ⟨H2, -⟩⟩
    ihave Ht := (ghostVar_fractional (GF := GF) γ.γ true).fractional q1 q2 |>.2 $$ [H1 H2]
    · iframe H1 H2
    iframe Ht Hp

/-- The persistent part of a share. -/
theorem walOpenWS_pers (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) (q : Qp) :
    walOpenWS (W := W) Sio P Mr w dir γ q ⊢
      walOpenWS (W := W) Sio P Mr w dir γ q ∗ walShPers (W := W) Sio P Mr w dir γ := by
  unfold walOpenWS
  iintro ⟨Ht, #Hp⟩
  iframe Ht Hp

/-- The facts a method uses before it holds the lock. -/
theorem walShPers_facts (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) :
    walShPers (W := W) Sio P Mr w dir γ ⊢
      sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) (BI.pure True : IProp GF) ∗
        isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000) := by
  unfold walShPers
  iintro ⟨-, #Hm, #Hp, #Hs, -⟩
  iframe Hm Hp Hs

/-- The WAL package's initialization (`SaveSnapshot` marshals the record before it holds the lock). -/
theorem walShPers_pkgInit (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) :
    walShPers (W := W) Sio P Mr w dir γ ⊢
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal := by
  unfold walShPers
  iintro ⟨-, -, -, -, #Hw⟩
  iexact Hw

/-- **Sharing a handle** (a client's, once: after `Create`, after `ReadAll`): the handle as `walHdl` gives
the whole share of fresh names. -/
theorem walOpenWS_alloc (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (E : CoPset) (i : Nat) :
    walHdl (W := W) Sio P Mr w dir i ⊢
      |={E}=> ∃ γ : WalShN, walOpenWS (W := W) Sio P Mr w dir γ 1 ∗ ⌜γ.inc = i⌝ := by
  iintro Hh
  imod ghostVar_alloc (GF := GF) true with ⟨%γt, Ht⟩
  imod ghostVar_alloc (GF := GF) (none : Option Qp) with ⟨%γl, Hl⟩
  -- the persistent facts, from the handle
  ihave ⟨Hh, #Hm, #Hp, #Hs, #Hwp⟩ : iprop(walHdl (W := W) Sio P Mr w dir i ∗
      (sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) (BI.pure True : IProp GF) ∗
      isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000) ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal))
    $$ [Hh]
  · icases walHdl_open Sio P Mr w dir i $$ Hh with ⟨%h, Hh, %hD, %hmd, Hr, %hroom, %hi⟩
    icases walHandleIn_lockFacts P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hm, #Hp, #Hs⟩
    icases walHandleIn_pkgInit P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hwp⟩
    iframe Hm Hp Hs Hwp
    iapply walHdl_close Sio P Mr w dir h hD hmd hroom i hi
    iframe Hh Hr
  imod inv_alloc walShN E (walShInv (W := W) Sio P Mr w dir ⟨γt, γl, i⟩) $$ [Hh Hl] with #Hinv
  · inext
    unfold walShInv
    ileft
    iframe Hh Hl
  imodintro
  iexists ⟨γt, γl, i⟩
  unfold walOpenWS walShPers
  iframe Ht Hinv Hm Hp Hs Hwp
  ipureintro; rfl

/-- **After `w.mu.Lock()`**: the lock token and the share go into the invariant, the handle comes out. -/
theorem walOpenWS_acquire (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) (q : Qp) :
    walOpenWS (W := W) Sio P Mr w dir γ q ∗
      sync.ownMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) ∗ £ 1 ⊢
      |={⊤}=> walShPers (W := W) Sio P Mr w dir γ ∗ walHeld γ q ∗ walHdl (W := W) Sio P Mr w dir γ.inc := by
  iintro ⟨Hw, Hl, Hlc⟩
  unfold walOpenWS
  icases Hw with ⟨Ht, #Hp⟩
  ihave #Hp0 := Hp
  iunfold walShPers at Hp0
  icases Hp0 with ⟨#Hinv, -⟩
  iinv Hinv with Hc Hclose
  unfold walShInv
  icases Hc with (⟨Hh, >Hg⟩ | ⟨>Hl', -⟩ | ⟨>Ht', -⟩)
  · imod lc_fupd_elim_later $$ Hlc Hh with Hh
    imod ghostVar_update (GF := GF) (some q) γ.γl (none : Option Qp) $$ Hg with Hg
    icases ghostVar_split_half (GF := GF) γ.γl 1 (some q) |>.1 $$ Hg with ⟨Hg1, Hg2⟩
    imod Hclose $$ [Hl Hg1 Ht] with _
    · inext; iright; ileft; iframe Hl; iexists q; iframe Hg1 Ht
    imodintro
    unfold walHeld
    iframe Hp Hg2 Hh
  · ihave %hf := sync.ownMutex_exclusive (GF := GF)
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) $$ Hl Hl'
    exact hf.elim
  · icombine Ht Ht' gives %hq2
    exfalso
    exact qp_add_one_not_le q hq2.1

/-- **Before `w.mu.Unlock()`**: the handle goes back into the invariant, the lock token and the share come
out. -/
theorem walOpenWS_release (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) (q : Qp) :
    walShPers (W := W) Sio P Mr w dir γ ∗ walHeld γ q ∗ walHdl (W := W) Sio P Mr w dir γ.inc ⊢
      |={⊤}=> walOpenWS (W := W) Sio P Mr w dir γ q ∗
        sync.ownMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) := by
  iintro ⟨#Hp, Hg, Hh⟩
  ihave #Hp0 := Hp
  iunfold walShPers at Hp0
  icases Hp0 with ⟨#Hinv, -⟩
  unfold walHeld
  iinv Hinv with Hc Hclose
  unfold walShInv
  icases Hc with (⟨-, >Hg'⟩ | ⟨>Hl, > ⟨%q', Hg', Ht⟩⟩ | ⟨-, > ⟨%v, Hg'⟩⟩)
  · icombine Hg Hg' gives %hq2
    exfalso
    exact qp_add_one_not_le _ hq2.1
  · icombine Hg Hg' gives %hq2
    obtain ⟨-, hqq⟩ := hq2
    cases hqq
    imod ghostVar_update_halves (GF := GF) (none : Option Qp) γ.γl (some q) (some q) $$ Hg Hg' with ⟨Hg, Hg'⟩
    ihave Hgf := (ghostVar_split_half (GF := GF) γ.γl 1 (none : Option Qp)).2 $$ [Hg Hg']
    · iframe Hg Hg'
    imod Hclose $$ [Hh Hgf] with _
    · inext; ileft; iframe Hh Hgf
    imodintro
    unfold walOpenWS
    iframe Ht Hp Hl
  · icombine Hg Hg' gives %hq2
    exfalso
    exact qp_add_one_not_le _ hq2.1

/-- **`Close`'s end, or a failed method's with the whole share**: the lock token comes out, the whole token
stays in, and no share is left to find a handle. -/
theorem walOpenWS_finish (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) :
    walShPers (W := W) Sio P Mr w dir γ ∗ walHeld γ 1 ⊢
      |={⊤}=> sync.ownMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w) := by
  iintro ⟨#Hp, Hg⟩
  unfold walShPers
  icases Hp with ⟨#Hinv, -⟩
  unfold walHeld
  iinv Hinv with Hc Hclose
  unfold walShInv
  icases Hc with (⟨-, >Hg'⟩ | ⟨>Hl, > ⟨%q', Hg', Ht⟩⟩ | ⟨-, > ⟨%v, Hg'⟩⟩)
  · icombine Hg Hg' gives %hq2
    exfalso
    exact qp_add_one_not_le _ hq2.1
  · icombine Hg Hg' gives %hq2
    obtain ⟨-, hqq⟩ := hq2
    cases hqq
    ihave Hgf := (ghostVar_split_half (GF := GF) γ.γl 1 (some (1 : Qp))).2 $$ [Hg Hg']
    · iframe Hg Hg'
    imod Hclose $$ [Ht Hgf] with _
    · inext; iright; iright; iframe Ht; iexists _; iexact Hgf
    imodintro
    iexact Hl
  · icombine Hg Hg' gives %hq2
    exfalso
    exact qp_add_one_not_le _ hq2.1

/-- **The exclusive handle back from the whole share** (a client that shared a handle and holds every
share again, outside any method: WalTester's member between calls is the case). -/
theorem walOpenWS_reclaim (Sio : IoSet) (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (γ : WalShN) :
    walOpenWS (W := W) Sio P Mr w dir γ 1 ∗ £ 1 ⊢ |={⊤}=> walHdl (W := W) Sio P Mr w dir γ.inc := by
  iintro ⟨Hw, Hlc⟩
  unfold walOpenWS walShPers
  icases Hw with ⟨Ht, #Hinv, -⟩
  iinv Hinv with Hc Hclose
  unfold walShInv
  icases Hc with (⟨Hh, >Hg⟩ | ⟨-, > ⟨%q', -, Ht'⟩⟩ | ⟨>Ht', -⟩)
  · imod lc_fupd_elim_later $$ Hlc Hh with Hh
    imod Hclose $$ [Ht Hg] with _
    · inext; iright; iright; iframe Ht; iexists _; iexact Hg
    imodintro
    iexact Hh
  · icombine Ht Ht' gives %hq2
    exfalso
    have : (1 : Qp) + q' ≤ 1 := hq2.1
    exact Qp_one_add_not_le q' this
  · icombine Ht Ht' gives %hq2
    exfalso
    exact qp_add_one_not_le 1 hq2.1

end handle

end WalFs
end EtcdGrove
end Perennial
