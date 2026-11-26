/- Lean-first (no Rocq counterpart).

# The server's keep vocabulary (etcd-dist B4, D-B4-4; `notes/etcd-dist-b4.md`, §9)

What a member's run keeps for a machine crash, at the server's level: the run's names (`SrvKN`), the
durable paths (`osSpineDur`, `osPathDur`), raft's durability (`srvDurKeep`), the WAL area (`srvWalKeep`), the
snapshot directory's invariant (`srvSnapKeepK`) and the names' pure facts (`srvKNOk`). Moved, names and
bodies verbatim, from the member's crash law (`examples/etcd/dist/crash/MemberCrash.lean`, where they were
`memberCrash.MemberKN`, `osSpineDur`, `osPathDur`, `memberDurKeep`, `memberWalKeep`, `memberSnapKeep` and
`memberKeepR`'s pure row), so that the server's crash-aware specs can name them; and the keep slot
(`SrvKeepPh`, `srvKeepPh`, the key `SrvKeepKey` with `srvKeyF`/`srvKeyR`, `srvKeepAt`, `srvKeepInv`), as §9
revised by Revision 1 (§R1.3) specifies. Definitions only.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrash
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCrashImage
public import Spec.go_etcd_io.raft.v3.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.FileDur
public import GooseLang.Ext.Fs.CrashTok
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Fs backend

/-! ## Durable paths -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The components `cs` lead durably from the directory `j` to `J`** (persistent): each component's claim
at a discarded fraction, naming the next directory, with the crash promise that every crash leaves the
name naming it. -/
def osSpineDur : Ino → List GoString → Ino → IProp GF
  | j, [], j' => iprop(⌜j = j'⌝)
  | j, c :: cs, j' => iprop(∃ (h : NamesH) (J : Ino), osNames j (.only [c]) DFrac.discard h ∗
      ⌜h.cur !! c = some (.dir J)⌝ ∗ nameCrash h j c (· = some (.dir J)) ∗ osSpineDur J cs j')

/-- **The path `p` names the directory `J` durably** (persistent; `osPathS` with a durable spine). -/
def osPathDur (R : Roots) (p : GoString) (J : Ino) : IProp GF :=
  iprop(∃ (r : GoString) (j0 : Ino) (cs : List GoString),
    ⌜RootsOk R ∧ (r, j0) ∈ R ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs⌝ ∗ osSpineDur j0 cs J)

theorem osSpineDur_nil (j j' : Ino) : osSpineDur (GF := GF) j [] j' = iprop(⌜j = j'⌝) := by
  simp only [osSpineDur]

theorem osSpineDur_cons (j : Ino) (c : GoString) (cs : List GoString) (j' : Ino) :
    osSpineDur (GF := GF) j (c :: cs) j' = iprop(∃ (h : NamesH) (J : Ino),
      osNames j (.only [c]) DFrac.discard h ∗ ⌜h.cur !! c = some (.dir J)⌝ ∗
      nameCrash h j c (· = some (.dir J)) ∗ osSpineDur J cs j') := by
  simp only [osSpineDur]

instance osNames_discard_persistent (j : Ino) (N : NameSet) (h : NamesH) :
    Persistent (osNames (GF := GF) j N DFrac.discard h) := by
  unfold osNames; split
  · infer_instance
  · unfold gElem; letI := (gooseOsGS (GF := GF)).osAllG; infer_instance

instance osSpineDur_persistent (j : Ino) (cs : List GoString) (j' : Ino) :
    Persistent (osSpineDur (GF := GF) j cs j') := by
  induction cs generalizing j with
  | nil => rw [osSpineDur_nil]; infer_instance
  | cons c cs ih =>
    rw [osSpineDur_cons]
    haveI : ∀ J, Persistent (osSpineDur (GF := GF) J cs j') := ih
    infer_instance

instance osPathDur_persistent (R : Roots) (p : GoString) (J : Ino) :
    Persistent (osPathDur (GF := GF) R p J) := by
  unfold osPathDur; infer_instance

end defs

/-! ## Raft's durability and the WAL area -/

section durDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- **What the member keeps of its raft durability across a crash** (D-T7-3): T2's crash-aware
invariant, its crash tokens (the invariant's and the node's arm's), and the graceful stop's token,
which the member never spends (it never stops its server), so T2's stop case is refuted. -/
def srvDurKeep (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) : IProp GF :=
  letI := srvStor (GF := GF) γn
  iprop(rnDurInvK γn id νk h ∗ token νk.tk ∗ nodeCrashTok γn.cl id νk.x ∗ token νk.ν.stop)

/-- **What the member keeps of its WAL area across a crash**: the area's invariant at the WAL names
`h.W` (`walInv`, at the server's codec and marshaller) with its crash token, and the shared mode's
invariant at the roots `h.R` (over `h`'s file system instances). -/
def srvWalKeep (h : WalH GF) : IProp GF :=
  letI := h.ext; letI := h.semOk; letI := h.has
  iprop(WalFs.walInv (W := h.W) walCodec walSrvMr h.R h.jr h.r ∗ WalFs.walCrashTok (W := h.W) ∗
    Fs.osSharedInv h.R)

end durDefs

/-! ## The run's names -/

section kn
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver in
/-- **The names a member's run keeps for its crash** (the restart case's witnesses). -/
structure SrvKN (GF : BundledGFunctors) where
  γ : SrvRaft
  ρo : ReqNames
  h : WalH GF
  νk : WalNamesK GF
  cid : w64
  γb : backend.DBNames
  i0 : Ino
  Dl : backend.Data
  Dn : backend.Data
  J : Ino
  γd : GName
  γm : GName
  /-- the data directory's root inode (the snapshot directory's spine starts there) -/
  jd : Ino

end kn

section keepDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

/-- The snapshot directory's invariant's parameters in the member's image (`srvCrashImageAt`'s row). -/
abbrev srvSnapKeepK (k : SrvKN GF) (dd : GoString) : IProp GF :=
  snapDirKeep (config.snapDirOf dd) k.γd (srvImageM k.γ.authOn k.γ)
    (fun j => monoNatLbOwn k.γm (uint.nat j + 1))

/-- **The run's names' pure facts** for member `id` of raft names `γ` (up to the request registry) with
data directory `dd`: the WAL directory and metadata, the snapshot directory's names, the program's
file-system context (B7), and the geometry (T8's, from the boot's roots): the data directory `dd` is a root
at `jd`, the WAL area `h.r` a root at `h.jr`, other than `dd`, the WAL directory below it, `snapDirOf dd`
the path `dd/member/snap`, and its index files' paths fit (`snapDir_split`'s premise). -/
def srvKNOk (γ : SrvRaft) (id : w64) (dd : GoString) (k : SrvKN GF) : Prop :=
  (∃ r : GName, k.γ = { γ with reg := r }) ∧ k.h.dir = srvWalDirOf dd ∧
    k.h.md = walMetaEnc id k.cid ∧ k.γ.snapLoc id = some k.γd ∧ (∃ c, theFs GF = some c) ∧
    (dd, k.jd) ∈ k.h.R ∧ (k.h.r, k.h.jr) ∈ k.h.R ∧ k.h.r ≠ dd ∧
    IsUnder k.h.r k.h.dir ∧
    config.snapDirOf dd = joinPath dd [go!"member", go!"snap"] ∧
    ∀ i, PathFits (snap.snapDBPath (config.snapDirOf dd) i)

/-! ## The keep slot (§9, as revised by Revision 1, §R1.3) -/

/-- The keep slot's phase: a first generation's (`node`: raft's state moved into `rnDurInvK`; `snap`: the
snapshot map moved into `snapDirKeep`; `be`: the backend's crash invariant added), a restart's (`open`: the
backend open, its crash invariant in place of the closed durable file), or a stopped run's. -/
inductive SrvKeepPh | first (node snap be : Bool) | restart («open» : Bool) | stopped

instance SrvKeepPh.countable : Pos.Countable SrvKeepPh :=
  .ofInjective (fun
      | .first n s e => Pos.Countable.encode ((0 : Nat), n, s, e)
      | .restart o => Pos.Countable.encode ((1 : Nat), o, false, false)
      | .stopped => Pos.Countable.encode ((2 : Nat), false, false, false))
    (by rintro (⟨a, b, c⟩ | a | _) (⟨d, e, f⟩ | d | _) h <;> have h := Pos.encode_inj h <;> simp_all)

/-- The phase variable (half in the slot, half with the code that moves it). -/
def srvKeepPh (γph : GName) (q : Qp) (ph : SrvKeepPh) : IProp GF := ghostVar γph q ph


/-- **The slot's key** (Revision 1, review D5 F-B3): which witnesses `k` a phase may hold. It is pure and fixed for
the generation, so the specs tie the slot's pieces to their binders without a ghost variable over `SrvKN`. -/
abbrev SrvKeepKey (GF : BundledGFunctors) := SrvKeepPh → SrvKN GF → Prop

/-- **A first start's key**: the pieces are this run's (`k.ρo = ρ`). -/
def srvKeyF (ρ : ReqNames) : SrvKeepKey GF := fun _ k => k.ρo = ρ

/-- **A restart's key**: the names the boot allocated from the image. They are raft's crash-aware durability `νk`,
the WAL `h`, the removal counter `γm` and the image's writer `ρo`. While the backend is closed and not yet opened
(`.restart false`), its file is at the image's data `D`. That constraint is phase-indexed: `.stopped` holds the data
the stop closed. -/
def srvKeyR (ρo : ReqNames) (νk : WalNamesK GF) (h : WalH GF) (γm : GName) (D : backend.Data) : SrvKeepKey GF :=
  fun ph k => k.ρo = ρo ∧ k.νk = νk ∧ k.h = h ∧ k.γm = γm ∧ (ph = .restart false → k.Dn = D)

/-- What the slot holds at phase `ph`, for member `id` of raft names `γ` with data directory `dd`, over the backend's
open and closed keeps `Kb`/`Kbc` (T10's: fixed definitions in the specs, never binders) and the key `kr`. -/
def srvKeepAt (γ : SrvRaft) (id : w64) (dd : GoString) (γd : GName)
    (Kb Kbc : SrvKN GF → IProp GF) (kr : SrvKeepKey GF) : SrvKeepPh → IProp GF
  | .first n s e => iprop(∃ (h : WalH GF) (νk : WalNamesK GF) (γm : GName),
      ⌜h.dir = srvWalDirOf dd⌝ ∗ srvWalKeep h ∗
      (if n then srvDurKeep γ id νk h
       else raftState γ.cl id RaftState.init ∗ ∃ x, nodeCrashTok γ.cl id x) ∗
      (if s then snapDirKeep (config.snapDirOf dd) γd (srvImageM γ.authOn γ)
                   (fun j => monoNatLbOwn γm (uint.nat j + 1))
       else ghostMapAuth γd 1 (∅ : GMap w64 Unit)) ∗
      -- (G3) from the backend's move on: the backend's crash keep and the durable spine, at one witness
      -- agreeing with the arms above
      (if e then ∃ k : SrvKN GF,
          ⌜srvKNOk γ id dd k ∧ kr (.first n s e) k ∧ k.h = h ∧ k.νk = νk ∧ k.γm = γm⌝ ∗
          osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ Kb k
       else True))
  | .restart o => iprop(∃ k : SrvKN GF, ⌜srvKNOk γ id dd k ∧ kr (.restart o) k⌝ ∗
      srvDurKeep k.γ id k.νk k.h ∗ srvWalKeep k.h ∗ srvSnapKeepK k dd ∗
      osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ (if o then Kb k else Kbc k))
  | .stopped => iprop(∃ k : SrvKN GF, ⌜srvKNOk γ id dd k ∧ kr .stopped k⌝ ∗
      srvDurKeep k.γ id k.νk k.h ∗ srvWalKeep k.h ∗ srvSnapKeepK k dd ∗
      osSpineDur k.jd [go!"member", go!"snap"] k.J ∗ Kbc k)


def srvKeepN : Namespace := nroot.@"srvKeep"

end keepDefs

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The slot (persistent), at the generation `L`. The specs pass the generation they run in (`hG.goose_localGS`,
review D5 F-A1), read at the Go context `lctx` of the section's `go.Semantics`/`Assumptions` (as `MemberGen`'s `atCtx`:
`L` itself when its context is `lctx`). -/
def srvKeepInv (γ : SrvRaft) (id : w64) (dd : GoString) (γd : GName) (Kb Kbc : SrvKN GF → IProp GF)
    (kr : SrvKeepKey GF) (γph : GName) (L : GooseLocalGS GF) : IProp GF :=
  letI : HeapGS HasLC.hasLC GF := ⟨G, { L with goose_go_local_context := lctx }⟩
  inv srvKeepN iprop(∃ ph, srvKeepPh γph (1 : Qp).half ph ∗ srvKeepAt γ id dd γd Kb Kbc kr ph)

end slot

end EtcdGrove
end Perennial
