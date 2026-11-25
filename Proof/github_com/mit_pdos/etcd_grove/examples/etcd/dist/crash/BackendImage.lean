/- Lean-first (no Rocq counterpart).

# The backend's image across a crash (etcd-dist D6, task T10; DESIGN DRAFT)

`notes/etcd-dist-d6.md`, "T10 design". Definitions and law statements only (no proof, no axiom, no
`sorry`): what T10 proposes, for review before any proof.

* `bkImg`: the image facts of one backend data `D` at the run's names (the backend rows of
  `srvCrashImageAt`, with the membership row **weakened** to "the configuration at `i` or at `i + 1`":
  the server's hooks write a conf change's `confState` before the change's own batch-lock cycle moves the
  consistent index, so a commit in between stores the next configuration beside the old index).
* `bkPayload`: what the backend's crash record carries beside `dbCrashKeep` (C-I1): the image of each
  data a crash can leave (`Dl`, `Dn`, the announced commit).
* `kbAnnounce.law`, `kbLand.law`, `kbSync.law`: the three client laws the backend's commit invariant
  applies to a client payload `KB Dl Dn pd` at its three steps (the announce at the hook step, the commit
  point inside `dbCrashKeep_half`, the resync after a returned commit).
* `wal.crashImageR`, `srvCrashImageAtR`: the restatement of T4's `srvCrashImageAt` T10 needs (B2: the
  received-snapshot window; B3: no `bootLen ≤ i`; the weakened membership row).
* `memberImageRowsR`, `memberBackend.law`: T10's law for T7, in place of `memberImage.law`,
  `memberDbNamed.law` and T7's own `dbCrash` step (the record cannot sit in `memberKeepR`: the running
  backend needs it at every commit, so it lives in a crash-aware invariant, `KeepB`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.crash.MemberCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bkImage

open Iris Iris.BI Fs backend

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **The membership row, weakened** (T10 finding): the backend's stored `confState` is the
configuration at the stored index `i`, or at `i + 1` (a conf change's `SetConfState` runs before the
change's `LockInsideApply` moves the consistent index; a commit in between, from the backend's timer,
stores the new `confState` with the old index). -/
def confRowW (cl : Cluster) (i : w64) (D : Data) (m : Membership) : IProp GF :=
  iprop(⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝ ∨
    ∃ m' : Membership, confAt cl (uint.nat i + 1) m' ∗ ⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m'⌝)

/-- **The image facts of the backend data `D` at index `i`** (T10): a committed prefix `A` of the
server's log reaching `i`, `D`'s rest buckets and stored index (`imageRestAt`), its `Key` bucket mvcc's
image of the KV model of `A` (`mvccImage`), the image's state reachable (`imageStOk`), the membership at
`i` (`confAt`) and the stored `confState` (`confRowW`). `srvCrashImageAt`'s backend rows, without the
file and the snapshot counter. -/
def bkImg (γ : SrvRaft) (ρ : ReqNames) (i : w64) (A : List EntryModel) (D : Data) (m : Membership) :
    IProp GF :=
  iprop(srvRLogLb ρ.rd.raft A ∗
    ⌜uint.Z i = uint.Z ρ.rd.raft.ai0 + A.length ∧
      imageRestAt ρ.rd.kv γ.boot i (ρ.rd.raft.pre ++ A) D ∧
      imageStOk (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A)⌝ ∗
    (∃ u : Bool, mvcc.api.mvccImage D (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A) u) ∗
    confAt γ.cl (uint.nat i) m ∗ confRowW γ.cl i D m)

/-- `D` is an image at some index. -/
def bkImgAny (γ : SrvRaft) (ρ : ReqNames) (D : Data) : IProp GF :=
  iprop(∃ (i : w64) (A : List EntryModel) (m : Membership), bkImg γ ρ i A D m)

/-- **The crash payload beside the record `dbCrashKeep γb path i0 Dl Dn pd`** (T10): every data a crash
can leave (`dbCrash`'s `Dl`, `Dn`, the announced `pd`) is an image. -/
def bkPayload (γ : SrvRaft) (ρ : ReqNames) (Dl Dn : Data) (pd : Option Data) : IProp GF :=
  iprop(□ bkImgAny γ ρ Dl ∗ □ bkImgAny γ ρ Dn ∗ □ (∀ S, ⌜pd = some S⌝ → bkImgAny γ ρ S))

/-! ### The backend's client laws on a crash payload `KB` (generic; the backend applies them) -/

/-- **At the hook step** (`unsafeCommit`, after `OnPreCommitUnsafe`, before bbolt's `Commit`, where
C-I1's `dbCrashKeep_announce` is applied): the batch lock's view of the session's data `S` (`CV S`: the
lock's client resource `W` and hooks' resource `Pk` with the readers' quarter, the hook's keys and the
tracked buckets at `S`, backend-supplied) lets the client announce `S` in its payload. The server's proof
is mvcc's `mvccImage_commit.law` (proposed) plus the batch lock's image row (T10's row of
`batchLockInv`). -/
abbrev kbAnnounce.law (KB : Data → Data → Option Data → IProp GF) (CV : Data → IProp GF) : Prop :=
  ∀ (Dl Dn S : Data), ⊢ KB Dl Dn none -∗ CV S ==∗ KB Dl Dn (some S) ∗ CV S

/-- **At the commit point** (inside `dbCrashKeep_half`'s update, the data changed to the announced `S`):
the fallback moves to `Dn` and the announcement clears. Ghost-only. -/
abbrev kbLand.law (KB : Data → Data → Option Data → IProp GF) : Prop :=
  ∀ (Dl Dn S : Data), ⊢ KB Dl Dn (some S) -∗ KB Dn S none

/-- **After a returned commit** (a fresh write transaction at `Dn`: the derived resync
`dbCrashKeep_clear`; `dbCrashKeep_close`; `dbCrashKeep_new`, which makes the record `(Dn, Dn, none)`):
the payload drops the fallback. Ghost-only (the server's raises its durable-index floor here). -/
abbrev kbSync.law (KB : Data → Data → Option Data → IProp GF) : Prop :=
  ∀ (Dl Dn : Data) (pd : Option Data), ⊢ KB Dl Dn pd ==∗ KB Dn Dn none

/-! ### The restatement of T4's `srvCrashImageAt` T10 needs -/

/-- **`wal.crashImage` without `σ.b ≤ i`** (B2): the WAL's slot of a crash image; the snapshot's
position relative to the backend moves to the snapshot row (`srvCrashImageAtR`). -/
def wal.crashImageR (cl : Cluster) (S : RaftState) (σ : StorContents) : IProp GF :=
  iprop(⌜StorageHolds S σ ∧ walReadFacts σ⌝ ∗ walSnapCert cl σ ∗
    (∃ l', isCommittedLogLb cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝))

/-- **B2's row** (the received-snapshot window): the WAL's snapshot is at or below the backend's index,
with the removal counter at most one past the index; or it is above it (index `j`), its `.snap.db` was
saved (durably) in the member's snapshot directory, and either the install has not taken it (`c ≤ j`:
the directory's invariant still holds it, no removal fact covers it) or the install took it and the
crash undid the rename (`c = j + 1`; the rename onto `db` and its directory sync not durable): the file,
back under its name, is the image's own (`fileAt`, with its certificate). -/
def snapRowB2 (γ : SrvRaft) (dd : GoString) (σ : StorContents) (i : w64) (γd : GName) (c : Nat) :
    IProp GF :=
  iprop(⌜σ.b ≤ uint.nat i ∧ c ≤ uint.nat i + 1⌝ ∨
    ∃ j : w64, ⌜uint.nat j = σ.b ∧ uint.nat i < σ.b⌝ ∗ snapSaved γd j ∗
      (⌜c ≤ σ.b⌝ ∨ ⌜c = σ.b + 1⌝ ∗ ∃ Ds : Data,
        backend.fileAt (snap.snapDBPath (config.snapDirOf dd) j) Ds ∗ □ srvImageM γ.authOn γ j Ds))

/-- **`srvCrashImageAt` restated for T10** (a proposal for T4 / the lead; T4's own definition is not
edited): (B3) the row `γ.cl.bootLen ≤ uint.nat i` dropped; (B2) `wal.crashImageR` and the snapshot row's
`c ≤ i + 1` replaced by `snapRowB2`; the membership row `confRowW`. Everything else is
`srvCrashImageAt`'s, row for row. -/
def srvCrashImageAtR (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) (S : RaftState)
    (σ : StorContents) (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership)
    (M : GMap Loc MemStorNamesRec) : IProp GF :=
  iprop(nodeVacant γ.cl id ∗ raftState γ.cl id S ∗
    ⌜ρ.rd.raft.raft = γ ∧ ρ.rd.kv.c0 = W64 0⌝ ∗ srvRLogLb ρ.rd.raft A ∗
    ⌜uint.Z i = uint.Z ρ.rd.raft.ai0 + A.length ∧
      imageRestAt ρ.rd.kv γ.boot i (ρ.rd.raft.pre ++ A) D ∧
      imageStOk (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A)⌝ ∗
    (∃ u : Bool, mvcc.api.mvccImage D (kvModel ρ.rd.kv A) (crevOf ρ.rd.kv A) u) ∗
    confAt γ.cl (uint.nat i) m ∗ confRowW γ.cl i D m ∗
    wal.crashImageR γ.cl S σ ∗
    (letI : MemStorReg GF := ⟨γ.reg⟩; memStorRegAuth M) ∗
    srvFilesC dd id σ D ∗
    (∃ (γd γm : GName) (c : Nat),
      ⌜γ.snapLoc id = some γd⌝ ∗ snapRowB2 γ dd σ i γd c ∗
      snapDirInvH (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
        (fun j => monoNatLbOwn γm (uint.nat j + 1)) ∗
      monoNatAuthOwn γm 1 c))

end defs

section rows
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **The image rows T10 owes T7** (`memberCrash.memberImageRows` restated): the image facts
(`bkImg`), the backend file holding `D` under its name, and the snapshot counter's authority with B2's
row. -/
def memberImageRowsR (k : memberCrash.MemberKN GF) (dd : GoString) (σ : StorContents) (i : w64)
    (A : List EntryModel) (D : backend.Data) (m : Membership) : IProp GF :=
  iprop(bkImg k.γ k.ρo i A D m ∗ backend.fileHolds (config.backendPathOf dd) D ∗
    (∃ c : Nat, snapRowB2 k.γ dd σ i k.γd c ∗ monoNatAuthOwn k.γm 1 c))

end rows

section keep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **T10's law for T7** (replaces `memberImage.law`, `memberDbNamed.law` and T7's own `dbCrash`
step): the run's backend keep `KeepB` (T10's crash-aware invariant holding the record `dbCrashKeep`, its
payload `bkPayload`, the durable name of `db` and the snapshot counter's authority), the generation's
`crashed`, raft's durable outputs (`memberDurOut`, for `σ`) and the crash rest before any file was taken,
with the new generation's claim on `db` and shares of the snapshot directory's path and call permission:
the inode `i0` the crashed tree names `db`, taken out of the crash rest (bbolt's `dbCrash` inside, under
the crash premise), and the image rows at some index `i`. -/
abbrev memberBackend.law (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (KeepB : GooseLocalGS GF → memberCrash.MemberKN GF → IProp GF) : Prop :=
  ∀ (L L' : GooseLocalGS GF) (V' : Hist) (k : memberCrash.MemberKN GF) (Q : OsState → OsState → Prop)
    (S : RaftState) (σ : StorContents) (l : List LogEntry) (q qc : Qp),
    (∀ i0 st st', Q st st' → BoltCrashWhole (· = i0) st st') →
    ⊢ KeepB L k -∗ crashed (hC := L.goose_crashGS) -∗
      memberCrash.memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) k.γ id k.νk S σ l -∗
      crashRest Q (gooseOsGS (L := etcd_dist.atCtx L)) (gooseOsGS (L := etcd_dist.atCtx L')) [] false V' -∗
      osPathS (L := etcd_dist.atCtx L') k.h.R (config.snapDirOf cfg.DataDir') (DFrac.own q) k.J -∗
      osCallPerm (L := etcd_dist.atCtx L') (callKey k.h.R (config.snapDirOf cfg.DataDir')) qc -∗
      osNames (L := etcd_dist.atCtx L') k.J (.only [go!"db"]) (DFrac.own 1)
        (namesOf V' k.J (.only [go!"db"])) ={⊤}=∗
      ∃ (i0 : Ino) (i : w64) (A : List EntryModel) (D : backend.Data) (m : Membership),
        ⌜V'.now.entry k.J go!"db" = some (.file i0)⌝ ∗
        crashRest Q (gooseOsGS (L := etcd_dist.atCtx L)) (gooseOsGS (L := etcd_dist.atCtx L'))
          [i0] false V' ∗
        memberCrash.memberDurOut (hG := ⟨G, etcd_dist.atCtx L⟩) k.γ id k.νk S σ l ∗
        memberImageRowsR (hG := ⟨G, etcd_dist.atCtx L'⟩) k cfg.DataDir' σ i A D m

end keep

end bkImage
end EtcdGrove
end Perennial
