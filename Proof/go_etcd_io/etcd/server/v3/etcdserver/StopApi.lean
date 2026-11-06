/-
**The stop's slot in the boot hub** (2026-11-05, the restart plan's R2b-3d; hub request H1, accepted
by the coordinator; the slot convention, `notes/spec-first-plan.md`, "The slot convention"). Lean-first.

`NewServer` keeps for the server's stop what no other part of its postcondition carries: the raft
loop's stop claim and the transport key's server (for `raftNode.stop`), the lessor's stop right and,
with auth off, the auth store's `Close` (for `Cleanup`), the store's readers it hands to nobody (for
the backend's `Close`, gap 4's census), and the storage registry's authority with the WAL's
directory (for the image). `NewServer.specG` names them only through `srvStop.keep s cfg E γrn γk`,
sealed (`etc/import-all.txt`), over the whole records it reads: the server, the configuration, the
apply environment (the store `E.s`, `E.γ`; the auth mode `E.authOn`), the raft wrapper's names and
the transport key's name. A later stop piece (auth on's closer, a lease slot's stop) changes the
sealed body and these laws, not the hub's text. Until 2026-11-05 the pieces were inline in the hub
(`srvStopKeep`, `srvTrKeyOf`, `□ (⌜on = false⌝ → srvCleanupOwn)`).

**Laws.** `srvStop.keep_intro` (`NewServer`'s proof); `srvStop.keep_split` into the four
consumers' parts (sealed too), each with one narrow elimination into what its consumer takes, all
used by `run`'s deferred shutdown (`run.spec`):
* `srvStop.raft_stop`: with the live transport, the raft loop's stop claim and the raft
  environment's `ST` (`srvTrStopK γk`), what `raftNode.stop.spec` takes;
* `srvStop.cleanup_pieces`: the lessor's stop right and, with auth off, the auth store's closer,
  what `Cleanup.spec` takes besides the apply thread's;
* `srvStop.census_readers`: out of compaction mode, no compactor and the kept store readers;
* `srvStop.image_inputs`: at the data directory `dd`, the registry's authority and the WAL's
  directory, `<dd>/member/wal`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The raft side of the stop (sealed): the raft loop's stop claim, and the server the transport's
key names. -/
@[no_expose] def srvStop.raftPart (s : Loc) (γrn : RNNames) (γk : GName) : IProp GF :=
  iprop(rnStopClaim γrn ∗ srvTrKeyOf s γk)

/-- `Cleanup`'s part of the stop (sealed): the lessor's stop right, and with auth off the auth
store's `Close`. -/
@[no_expose] def srvStop.cleanupPart (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop((∃ lp : Loc, srvLessorAddr s ↦□ lease.lessorIface lp ∗ lease.lessorStopTok lp) ∗
    □ (⌜E.authOn = false⌝ → srvCleanupOwn s))

/-- The census's part (sealed): the store readers `NewServer` hands to nobody (`srvKeepRdN`), and
the compactor's when there is no compactor; a compactor only in compaction mode (R2c-2: what makes
the stop's "no compactor" follow from its scope, `srvStop.scope`). -/
@[no_expose] def srvStop.censusPart (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(([∗list] _x ∈ List.replicate (srvKeepRdN E.γ) (), mvcc.storeReader E.s E.γ) ∗
    (∃ cp : GoInterface, srvCompactorAddr s ↦□ cp ∗
      ((⌜cp = GoInterface.nil⌝ ∗ mvcc.storeReader E.s E.γ) ∨ ⌜cp ≠ GoInterface.nil ∧ E.cmp = true⌝)))

/-- The image's part (sealed): the storage registry's authority, the configuration's data and WAL
directories, read-only, and the raft wrapper's storage writing the WAL in the latter. -/
@[no_expose] def srvStop.imagePart (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (γrn : RNNames) : IProp GF :=
  iprop((letI : MemStorReg GF := ⟨γrn.node.reg⟩; ∃ M : GMap Loc MemStorNamesRec, memStorRegAuth M) ∗
    srvCfgFieldAddr s go!"DataDir" ↦□ cfg.DataDir' ∗
    srvCfgFieldAddr s go!"DedicatedWALDir" ↦□ cfg.DedicatedWALDir' ∗
    (∃ st : GoInterface, rnStorageAddr (srvRAddr s) ↦□ st ∗
      ⌜walDirOf (storage.walOf st) = config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'⌝))

/-- **What `NewServer` keeps for the server's stop** (sealed; see the file header). -/
@[no_expose] def srvStop.keep (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) : IProp GF :=
  iprop(srvStop.raftPart s γrn γk ∗ srvStop.cleanupPart s E ∗ srvStop.censusPart s E ∗
    srvStop.imagePart s cfg γrn)

/-- **The slot, from what `NewServer` holds at its return.** -/
theorem srvStop.keep_intro (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) :
    rnStopClaim γrn ∗ srvTrKeyOf s γk ∗
      (∃ lp : Loc, srvLessorAddr s ↦□ lease.lessorIface lp ∗ lease.lessorStopTok lp) ∗
      □ (⌜E.authOn = false⌝ → srvCleanupOwn s) ∗
      ([∗list] _x ∈ List.replicate (srvKeepRdN E.γ) (), mvcc.storeReader E.s E.γ) ∗
      (∃ cp : GoInterface, srvCompactorAddr s ↦□ cp ∗
        ((⌜cp = GoInterface.nil⌝ ∗ mvcc.storeReader E.s E.γ) ∨
          ⌜cp ≠ GoInterface.nil ∧ E.cmp = true⌝)) ∗
      (letI : MemStorReg GF := ⟨γrn.node.reg⟩; ∃ M : GMap Loc MemStorNamesRec, memStorRegAuth M) ∗
      srvCfgFieldAddr s go!"DataDir" ↦□ cfg.DataDir' ∗
      srvCfgFieldAddr s go!"DedicatedWALDir" ↦□ cfg.DedicatedWALDir' ∗
      (∃ st : GoInterface, rnStorageAddr (srvRAddr s) ↦□ st ∗
        ⌜walDirOf (storage.walOf st) = config.walDirOf cfg.DataDir' cfg.DedicatedWALDir'⌝) ⊢
    srvStop.keep (GF := GF) s cfg E γrn γk := by
  iintro ⟨Hc, Hk, Hl, Ha, Hr, Hcp, Hreg, Hdd, Hwd, Hst⟩
  unfold srvStop.keep srvStop.raftPart srvStop.cleanupPart srvStop.censusPart srvStop.imagePart
  iframe

/-- **The slot, split into its consumers' parts.** -/
theorem srvStop.keep_split (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) :
    srvStop.keep (GF := GF) s cfg E γrn γk ⊢
      srvStop.raftPart s γrn γk ∗ srvStop.cleanupPart s E ∗ srvStop.censusPart s E ∗
        srvStop.imagePart s cfg γrn := by
  unfold srvStop.keep; exact .rfl

/-- **`raftNode.stop`'s pieces**: with the server's live transport (the apply thread's, `srvApRes`),
the raft loop's stop claim and the transport's stop right at the key (`srvTrStopK γk`, the server's
raft environment's `ST`). -/
theorem srvStop.raft_stop (s : Loc) (γrn : RNNames) (γk : GName) :
    srvStop.raftPart (GF := GF) s γrn γk ∗ srvTrStop s ⊢ rnStopClaim γrn ∗ srvTrStopK γk := by
  unfold srvStop.raftPart
  iintro ⟨⟨Hc, #Hk⟩, Ht⟩
  iframe Hc
  iapply srvTrStopK_of s γk
  iframe Hk Ht

/-- **`Cleanup`'s pieces** (besides the apply thread's): the lessor's stop right, and with auth off
the auth store's closer at no resource. -/
theorem srvStop.cleanup_pieces (s : Loc) (E : apply.AEnv GF) :
    srvStop.cleanupPart (GF := GF) s E ⊢
      (∃ lp : Loc, srvLessorAddr s ↦□ lease.lessorIface lp ∗ lease.lessorStopTok lp) ∗
      □ (⌜E.authOn = false⌝ → ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        authCloser stl iprop(True)) := by
  unfold srvStop.cleanupPart
  iintro ⟨Hl, #Ha⟩
  iframe Hl
  iintro !> %hoff
  ihave Hco := Ha $$ %hoff
  iunfold srvCleanupOwn at Hco
  icases Hco with ⟨%stl, #Hstl, #Hok⟩
  iexists stl
  iframe Hstl
  iunfold authCloseOk at Hok
  iexact Hok

/-- **The census's readers**: out of compaction mode (the stop's scope), no compactor (the server's
`compactor` field `cp` is nil), and the store readers kept for the stop and the compactor's.
(R2c-2: until then the field's nil a premise.) -/
theorem srvStop.census_readers (s : Loc) (E : apply.AEnv GF) (cp : GoInterface)
    (hcmp : E.cmp = false) :
    srvStop.censusPart (GF := GF) s E ∗ srvCompactorAddr s ↦□ cp ⊢
      ⌜cp = GoInterface.nil⌝ ∗
        [∗list] _x ∈ List.replicate (srvKeepRdN E.γ + 1) (), mvcc.storeReader E.s E.γ := by
  unfold srvStop.censusPart
  iintro ⟨⟨Hrs, %cp', #Hcp, Hc⟩, #Hcp2⟩
  icombine Hcp Hcp2 gives %Heq
  subst Heq
  icases Hc with (⟨%Hnil, Hr⟩ | %Hne)
  · isplitr
    · ipureintro; exact Hnil
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe Hrs Hr
  · exact absurd Hne.2 (by rw [hcmp]; decide)

/-- **The image's inputs** at the data directory `dd` with no dedicated WAL directory
(`srvDataDir`): the storage registry's authority, and the raft wrapper's storage writing the WAL in
`<dd>/member/wal`. -/
theorem srvStop.image_inputs (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (γrn : RNNames) (dd : GoString) :
    srvStop.imagePart (GF := GF) s cfg γrn ∗ srvDataDir s dd ⊢
      (letI : MemStorReg GF := ⟨γrn.node.reg⟩; ∃ M : GMap Loc MemStorNamesRec, memStorRegAuth M) ∗
      ∃ st : GoInterface, rnStorageAddr (srvRAddr s) ↦□ st ∗
        ⌜walDirOf (storage.walOf st) = config.walDirOf dd ""⌝ := by
  unfold srvStop.imagePart
  iintro ⟨⟨Hreg, #Hdd, #Hwd, %st, #Hst, %Hw⟩, #Hdir⟩
  iunfold srvDataDir at Hdir
  icases Hdir with ⟨#Hdd', #Hwd'⟩
  icombine Hdd Hdd' gives %Heq1
  icombine Hwd Hwd' gives %Heq2
  iframe Hreg
  iexists st
  iframe Hst
  ipureintro
  have he : stringToGoString "" = [] := by simp [stringToGoString]
  rw [Hw, Heq1, Heq2, he]

/-- **The stop's slot where `start` and `run` take it** (2026-11-05, the restart plan's R2c-3; the
user's Q5 (a), adapted: `questions.md` D-d): what `NewServer` kept for the stop (`srvStop.keep`) at
the raft wrapper's names `γrn`, at some configuration `cfg` and transport key `γk`, the key the one
the raft environment's transport stop right `Er.ST` names (a fact of the construction, `srvErM`'s:
D1, until then `run.specStop`'s premise). A conjunct of `start`'s construction premise
(`isServerBuiltC`) and, R2c-4, of `run`'s (`isServerRunC`), so that no caller of `Start` hands it
separately. -/
def srvStop.slot (s : Loc) (E : apply.AEnv GF) (γrn : RNNames) (Er : RNEnv GF) : IProp GF :=
  iprop(∃ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γk : GName),
    srvStop.keep s cfg E γrn γk ∗ ⌜Er.ST = srvTrStopK γk⌝)

/-- **The slot from what `NewServer` kept** (R2c review F4): its `srvStop.keep`, at the transport
key the raft environment's stop right names. -/
theorem srvStop.slot_intro (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) (Er : RNEnv GF) (h : Er.ST = srvTrStopK γk) :
    srvStop.keep s cfg E γrn γk ⊢ srvStop.slot (GF := GF) s E γrn Er := by
  iintro H
  iunfold srvStop.slot
  iexists cfg, γk
  iframe H
  ipureintro; exact h

/-- **The configuration's data directory field** (persistent; R2c-4): the slot's `DataDir`, which
`start` records in the stop right (`srvStopRight`) so that the stop's image names it. -/
theorem srvStop.dataDirField (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) :
    srvStop.keep (GF := GF) s cfg E γrn γk ⊢
      srvCfgFieldAddr s go!"DataDir" ↦□ cfg.DataDir' ∗ srvStop.keep s cfg E γrn γk := by
  unfold srvStop.keep srvStop.imagePart
  iintro ⟨Hr, Hc, Hcs, Hreg, #Hdd, #Hwd, Hst⟩
  iframe Hdd
  iframe
  iexact Hwd

/-- **The server's data directory** (persistent; R2c-5, `questions.md` D2): with no dedicated WAL
directory, the slot's configuration fields are the data directory's record (`srvDataDir`), which
the stop request carries and the image names. -/
theorem srvStop.dataDir (s : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (E : apply.AEnv GF) (γrn : RNNames) (γk : GName) (dd : GoString) (hdd : cfg.DataDir' = dd)
    (hw : cfg.DedicatedWALDir' = (go!"" : GoString)) :
    srvStop.keep (GF := GF) s cfg E γrn γk ⊢ srvDataDir s dd ∗ srvStop.keep s cfg E γrn γk := by
  subst hdd
  have heq : (srvCfgFieldAddr s go!"DedicatedWALDir" ↦□ cfg.DedicatedWALDir' : IProp GF) =
      (srvCfgFieldAddr s go!"DedicatedWALDir" ↦□ (go!"" : GoString) : IProp GF) := by rw [hw]
  unfold srvStop.keep srvStop.imagePart
  iintro ⟨Hr, Hc, Hcs, Hreg, #Hdd, #Hwd, Hst⟩
  isplitr
  · iunfold srvDataDir
    iframe Hdd
    rw [← heq]
    iexact Hwd
  iframe
  iframe #

end slot

end EtcdGrove
end Perennial
