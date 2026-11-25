/- Lean-first (no Rocq counterpart).

# The handle before naming (W4 of `notes/wal-fsext-plan.md`, twenty-second session)

`walOpenWFU` (`Handle.lean`) is `walOpenWF` with the naming fact left out, the WAL's name not yet
registered (the names fragment `some dir`, `Create`'s pending registration) and the two paths to `dir`
(the handle's and the pipeline's) pinned at the roots and fraction `Create` lent (design P,
`notes/wal-units/create.md`): the WAL `Create` holds between its commit (the rename of `nm.tmp` onto `nm`)
and its success exit. `renameWAL`'s two success arms converge on it (arm 1 through `Create`'s assembly,
arm 2 as the retry returns it). At the success exit the parent's fsync gives `walNamed dir`
(`walInv_named`), the registration turns the names fragment to `none` (`walInv_register`), and
`walOpenWFU_seal` makes the client handle `walOpenWF`; on a cleanup `Close.spec` (state `unnamed`) gives the pinned paths and
the fragment back. `walDirH_split`/`walHandleIn_split` take the names fragment out and put another back,
the naming fact changed; `walPipeH_mono` weakens the pipeline's pin. `walOpenWFU_dirAcc` lends the `dir`
field (`Create` reads `w.dir` after `renameWAL`), `walOpenWFU_permAcc` the handle's quarter of the call
permission (the parent's `OpenDir`/`Fsync`); both handles hold the lock token (`walOpenWFU_unlocked_excl`,
`walOpenWF_unlocked_excl`); `walPurgeW_fresh_lbs` gives `Create.spec`'s lower bounds of the fresh WAL.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- **A nil hard state holds the zero state** (`WalPbIn`'s "nil read as the zero state"; a law of `P`,
as `WalPbIn.ZeroLaw`'s converse: `Create`'s `w.state` is nil). -/
abbrev WalPbIn.NilLaw (P : WalPbIn GF) : Prop := ⊢ P.hsIn null hsZero

/-- **The handle before naming, from its state** (`Create`'s arm 1: `walOpenWFU` is sealed). -/
theorem walOpenWFU_intro (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (Rp : Roots)
    (qp : Qp) (tf : Loc) (h : WalHS) (hD : h.Done) (hmd : h.md.length < 2 ^ 41) :
    walHandleIn (W := W) P Mr w dir h TailMetaW (fun f R q => iprop(⌜f = tf ∧ R = Rp ∧ q = qp⌝))
        (some dir) (fun R dq => R = Rp ∧ dq = DFrac.own qp) ∗ ⧗ h.pc ⊢
      walOpenWFUI (W := W) P Mr w dir Rp qp tf h.inc := by
  iintro ⟨Hh, Hr⟩
  unfold walOpenWFUI
  iexists h
  iframe Hh Hr
  ipureintro; exact ⟨hD, hmd, rfl⟩

/-- **The directory share's names record out** (with the path's fraction `q` and the naming fact), and
back (another record over the same fractions) with another naming fact. -/
theorem walDirH_split (dir : GoString) (j : Ino) (dfd : w64) (ino : Ino) (name : GoString) (k : Nat)
    (lfs : List Loc) (cuts : List Nat) (qp : Qp) (A B : Roots → Qp → IProp GF) (nf : Option GoString) :
    ⊢ walDirH (W := W) dir j dfd ino name k lfs cuts qp A nf -∗
      ∃ (R : Roots) (q : Qp), A R q ∗ walHLoans (W := W) dir nf [q, qp] ∗
        ∀ nf' : Option GoString, walHLoans (W := W) dir nf' [q, qp] -∗
        B R q -∗ walDirH (W := W) dir j dfd ino name k lfs cuts qp B nf' := by
  iintro Hd
  unfold walDirH
  icases Hd with ⟨%R, %q, %X, %hj, %nm0, %ph, Hk, Hn, Hp, Hsi, Hrw, Hperm, Hdfd, Ha, Ho, Ht, Hnf, Hrest⟩
  iexists R, q
  iframe Ha Hnf
  iintro %nf' Hnf' Hw
  iexists R, q, X, hj, nm0, ph
  iframe Hk Hn Hp Hsi Hrw Hperm Hdfd Ho Ht Hnf' Hrest Hw

/-- **The pipeline's pin weakened.** -/
theorem walPipeH_mono (fp : Loc) (dir : GoString) (j : Ino) (k : Nat) (pp pp' : Roots → DFrac → Prop)
    (hpp : ∀ R dq, pp R dq → pp' R dq) :
    walPipeH (GF := GF) fp dir j k pp ⊢ walPipeH (GF := GF) fp dir j k pp' := by
  iintro Hp
  unfold walPipeH
  icases Hp with ⟨%γ, %R, %dq, %sz, %n, #Hfp, Hmain, Hc, %hn, %hfp⟩
  iexists γ, R, dq, sz, n
  iframe Hfp Hmain Hc
  ipureintro; exact ⟨⟨hn.1, hpp R dq hn.2⟩, hfp⟩

/-- **A read handle's pipeline pin** (`walReadH`'s write branch): its one loan `qs = [qp]` named. -/
theorem walPipeH_pinLoan (fp : Loc) (dir : GoString) (j : Ino) (k : Nat) (qs : List Qp) :
    walPipeH (W := W) fp dir j k (fun _ dq => ∃ qp, dq = DFrac.own qp ∧ qs = [qp]) ⊢
      ∃ qp : Qp, ⌜qs = [qp]⌝ ∗ walPipeH (W := W) fp dir j k (fun _ dq => dq = DFrac.own qp) := by
  iintro Hp
  unfold walPipeH
  icases Hp with ⟨%γ, %R, %dq, %sz, %n, #Hfp, Hmain, Hc, %hn, %hfp⟩
  obtain ⟨hnk, qp, rfl, hq⟩ := hn
  iexists qp
  isplitr
  · ipureintro; exact hq
  iexists γ, R, DFrac.own qp, sz, n
  iframe Hfp Hmain Hc
  ipureintro; exact ⟨⟨hnk, rfl⟩, hfp⟩

/-- **The handle sealed at `Create`'s success exit, the lock quarter lent**: the pending names fragment
`some dir` out (for the registration, `walInv_register`, which needs the lock at the handle's incarnation to
know the WAL is still present), and with the record of the two loans of the pinned fraction `qp` (the
handle's path and its pipeline's, `walHLoans`), the naming `walNamed dir i` (`walInv_named`, at the
handle's incarnation) and the lock quarter back, the client handle at `i`; the pins forgotten. -/
theorem walOpenWFU_sealL (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (Rp : Roots)
    (qp : Qp) (tf : Loc) (i : Nat) :
    ⊢ walOpenWFUI (W := W) P Mr w dir Rp qp tf i -∗ walNamesFrag (W := W) (some dir) ∗
      ∃ I : GMap GoString Nat, walLockedTokI (W := W) I ∗ ⌜incOf I dir = i⌝ ∗
      (walLockedTokI (W := W) I -∗ walHLoans (W := W) dir none [qp, qp] -∗ walNamed (W := W) dir i -∗
        walOpenWFI (W := W) P Mr w dir i) := by
  iintro H
  unfold walOpenWFUI
  icases H with ⟨%h, Hh, %hD, %hmd, %hi, Hrc⟩
  subst hi
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, Hd, H20, H21,
    H22, H23, H24, H25, H26, Hpipe, K1, K2, K3, Hw, K4⟩
  unfold walOpenWI
  icases Hw with ⟨%I, Hst, Hl, %hI⟩
  iunfold walPipeH at Hpipe
  icases Hpipe with ⟨%γp, %Rpp, %dqp, %szp, %np, Hisfp, Hmain, Hpc, %hnp, %hfpn, %hRpW⟩
  obtain ⟨hnk, ⟨-, hq1⟩, hq2⟩ := hnp
  have hqq : h.qp = qp := by rw [hq1] at hq2; exact (DFrac.own.inj hq2).symm
  icases walDirH_split dir j dfd h.ino name h.pc lfs.dropLast h.cuts h.qp
    (fun R q => iprop(⌜f = tf ∧ R = Rp ∧ q = qp⌝)) (fun _ _ => walNamed (W := W) dir h.inc) (some dir)
    $$ Hd with ⟨%Rd, %qd, %hA, Hnf, Hd⟩
  obtain ⟨-, -, hqd⟩ := hA
  subst hqd
  ihave Hnf := (walHLoans_some (W := W) dir dir _).1 $$ Hnf
  iframe Hnf
  iexists I
  iframe Hl
  isplitr
  · ipureintro; exact hI
  iintro Hl Hnf' #Hn
  unfold walOpenWFI walHandleIn
  iexists h
  iframe Hrc
  isplitl
  · iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25
      H26 K1 K2 K3 K4
    isplitl [Hd Hnf']
    · rw [hqq]
      iapply Hd $$ Hnf'
      iexact Hn
    isplitl [Hisfp Hmain Hpc]
    · iunfold walPipeH
      iexists γp, Rpp, dqp, szp, np
      iframe Hisfp Hmain Hpc
      ipureintro; exact ⟨⟨hnk, trivial, hq2⟩, hfpn, hRpW⟩
    unfold walOpenWI
    iexists I
    iframe Hst Hl
    ipureintro; exact hI
  ipureintro; exact ⟨hD, hmd, rfl⟩

/-- **The `dir` field of the handle before naming, lent** (`Create` reads `w.dir` after `renameWAL`). -/
theorem walOpenWFU_dirAcc (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (Rp : Roots)
    (qp : Qp) (tf : Loc) (i : Nat) :
    ⊢ walOpenWFUI (W := W) P Mr w dir Rp qp tf i -∗
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir ∗
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"dir" w ↦ dir -∗
        walOpenWFUI (W := W) P Mr w dir Rp qp tf i) := by
  iintro H
  unfold walOpenWFUI
  icases H with ⟨%h, Hh, Hr⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    H1, H2, H3, Hh⟩
  iframe H3
  iintro H3
  iexists h
  iframe Hr
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe H1 H2 H3 Hh

/-- **The handle's quarter of the call permission, lent** (`Create`'s parent fsync after `renameWAL`). -/
theorem walOpenWFU_permAcc (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (Rp : Roots)
    (qp : Qp) (tf : Loc) (i : Nat) :
    ⊢ walOpenWFUI (W := W) P Mr w dir Rp qp tf i -∗ osCallPerm (callKey W.roots dir) (1 : Qp).half.half ∗
      (osCallPerm (callKey W.roots dir) (1 : Qp).half.half -∗ walOpenWFUI (W := W) P Mr w dir Rp qp tf i) := by
  iintro H
  unfold walOpenWFUI
  icases H with ⟨%h, Hh, Hr⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, Hd, Hh⟩
  unfold walDirH
  icases Hd with ⟨%R, %q, %X, %hj, %nm0, %ph, Hk, Hn, Hp, Hsi, %hRW, Hperm, Hd⟩
  subst hRW
  iframe Hperm
  iintro Hperm
  iexists h
  iframe Hr
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 Hh
  iexists W.roots, q, X, hj, nm0, ph
  iframe Hk Hn Hp Hsi Hperm Hd
  try (ipureintro; rfl)

/-- **The fresh WAL's lower bounds** (`Create.spec`'s success post): its empty history written and
synced, from the purge right's handle name and a past state with the fresh WAL. -/
theorem walPurgeW_fresh_lbs (w : Loc) (dir : GoString) (s : AbsDiskState) (I : GMap GoString Nat)
    (d : WalDur) (hs : s.wal !! dir = some d) :
    ⊢ walPurgeW (W := W) w dir -∗ walPastI (W := W) (s, I) -∗
      walPurgeW (W := W) w dir ∗ walLenLb (W := W) w dir (incOf I dir) 0 ∗
        walSyncedLb (W := W) dir (incOf I dir) 0 := by
  iintro Hpw #Hp
  unfold walPurgeW
  icases Hpw with ⟨%γ, #Hd, Hpt⟩
  isplitl [Hpt]
  · iexists γ; iframe Hd Hpt
  isplitl []
  · unfold walLenLb
    iexists γ, s, I
    iframe Hd Hp
    ipureintro; exact Or.inl ⟨rfl, d, hs, Nat.zero_le _⟩
  · iapply walSyncedLb_intro s I dir d 0 hs (Nat.zero_le _) $$ Hp

/-- **The handle before naming holds the lock token** (`create_areaBack`'s `T`). -/
theorem walOpenWFU_unlocked_excl (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (Rp : Roots) (qp : Qp) (tf : Loc) :
    ⊢ walOpenWFU (W := W) P Mr w dir Rp qp tf -∗ walUnlockedTok (W := W) -∗ False := by
  iintro H Hu
  unfold walOpenWFU
  icases H with ⟨%h, Hh, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hw, -⟩
  unfold walOpenWI
  icases Hw with ⟨%I, -, Hl, -⟩
  ihave Hl : walLockedTok (W := W) $$ [Hl]
  · unfold walLockedTok; iexists I; iexact Hl
  iapply walLockedTok_unlocked_excl $$ Hl Hu

/-- The same against the free token less its names fragment. -/
theorem walOpenWFU_unlocked_exclX (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (Rp : Roots) (qp : Qp) (tf : Loc) :
    ⊢ walOpenWFU (W := W) P Mr w dir Rp qp tf -∗ walUnlockedTokX (W := W) -∗ False := by
  iintro H Hu
  unfold walOpenWFU
  icases H with ⟨%h, Hh, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hw, -⟩
  unfold walOpenWI
  icases Hw with ⟨%I, -, Hl, -⟩
  ihave Hl : walLockedTok (W := W) $$ [Hl]
  · unfold walLockedTok; iexists I; iexact Hl
  iapply walLockedTok_exclX $$ Hl Hu

/-- **The lock quarter of the handle before naming, lent**, at the handle's incarnation (`Create`'s
registration, `walInv_register`: a past state with the WAL is current under it). -/
theorem walOpenWFUI_lockAcc (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (Rp : Roots) (qp : Qp) (tf : Loc) (i : Nat) :
    ⊢ walOpenWFUI (W := W) P Mr w dir Rp qp tf i -∗ ∃ I : GMap GoString Nat,
      walLockedTokI (W := W) I ∗ ⌜incOf I dir = i⌝ ∗
      (walLockedTokI (W := W) I -∗ walOpenWFUI (W := W) P Mr w dir Rp qp tf i) := by
  iintro H
  unfold walOpenWFUI
  icases H with ⟨%h, Hh, %hD, %hmd, %hi, Hr⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, Hw, Hz⟩
  unfold walOpenWI
  icases Hw with ⟨%I, Hst, Hl, %hI⟩
  iexists I
  iframe Hl
  isplitr
  · ipureintro; rw [hI, hi]
  iintro Hl
  iexists h
  iframe Hr
  isplitl
  · iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 Hz
    iexists I
    iframe Hst Hl
    ipureintro; exact hI
  ipureintro; exact ⟨hD, hmd, hi⟩

/-- **The handle holds the lock token.** -/
theorem walOpenWF_unlocked_excl (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWF (W := W) P Mr w dir -∗ walUnlockedTok (W := W) -∗ False := by
  iintro H Hu
  unfold walOpenWF
  icases H with ⟨%h, Hh, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hw, -⟩
  unfold walOpenWI
  icases Hw with ⟨%I, -, Hl, -⟩
  ihave Hl : walLockedTok (W := W) $$ [Hl]
  · unfold walLockedTok; iexists I; iexact Hl
  iapply walLockedTok_unlocked_excl $$ Hl Hu

/-- The same against the free token less its names fragment. -/
theorem walOpenWF_unlocked_exclX (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) :
    ⊢ walOpenWF (W := W) P Mr w dir -∗ walUnlockedTokX (W := W) -∗ False := by
  iintro H Hu
  unfold walOpenWF
  icases H with ⟨%h, Hh, -⟩
  unfold walHandleIn
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j, %rc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, Hw, -⟩
  unfold walOpenWI
  icases Hw with ⟨%I, -, Hl, -⟩
  ihave Hl : walLockedTok (W := W) $$ [Hl]
  · unfold walLockedTok; iexists I; iexact Hl
  iapply walLockedTok_exclX $$ Hl Hu


/-- `walOpenWF_unlocked_exclX` at an incarnation (`Create`'s success exit, `create_areaBack`'s `T`). -/
theorem walOpenWFI_unlocked_exclX (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString) (i : Nat) :
    ⊢ walOpenWFI (W := W) P Mr w dir i -∗ walUnlockedTokX (W := W) -∗ False := by
  iintro H Hu
  ihave H := walOpenWFI_WF P Mr w dir i $$ H
  iapply walOpenWF_unlocked_exclX P Mr w dir $$ H Hu

end handle

end WalFs
end EtcdGrove
end Perennial

end
