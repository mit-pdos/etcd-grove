/- Lean-first (no Rocq counterpart).

# The vocabulary of `wal.Create`'s and `fileutil.TouchDirAll`'s specs over `fsExt` (W4)

`notes/wal-fsext-plan.md`, §3 ("Must change") and the "W4 implementation log". Untrusted.

* **`walAuMask`**: the outer mask of the WAL's client atomic updates. The WAL commits them inside
  the step of an `os` call (`osAU`, `LinuxFs/Proof/os/SharedAu.lean`), with the WAL invariant open:
  so everything but the extension's invariants and the WAL's (the old specs' `⊤` was the extension's
  state interpretation's freedom, which a proof layer does not have).
* **`walAreaOk`** (persistent): the WAL invariant of the area and the file system's invariants. Its old
  `durableResvD` (the `lib/durable` reservation) is gone (plan §3).
* **`walAreaRes jr`** (exclusive, the program's): its half of the area directory's claim on names `N`
  containing every WAL name not split out (`walSplitFrag Wn`) and every `nm.<sfx>` of one (the invariant holds the other half:
  `walInv_alloc`'s `harea`), and the
  whole claims of every directory reachable from a non-WAL name of `N` (`SubCover`). From it a WAL
  function takes the claims it writes in the area (`n.tmp`, `n.broken.*`, `n`), giving back the
  invariant's halves. `N` is cofinite (`NameSet`), so it cannot exclude the infinitely many cleanup
  names: they are split off it when known.
* **`osSubtree j b`** (`osSubtreeH j b h`, the claim's history `h`): the whole claim on the name `b`
  of `j`, and the whole claims of every directory under it: what `os.RemoveAll` of `j/b` needs, and
  what `TouchDirAll`/`CreateDirAll` of `j/b` work in (`MkdirAll`, the probe `.touch`, `ReadDir`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import LinuxFs.Proof.os.SharedAu
public import LinuxFs.Spec.os.RemoveAll
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- **The outer mask of the WAL's client atomic updates**: all but the extension's invariants and
the WAL invariant (an update commits inside an `os` call's step, the WAL invariant open). -/
def walAuMask : CoPset := osAuMask \ ↑walN

/-- The WAL's invariant is in the `os` updates' mask. -/
theorem walN_sub_au : (↑walN : CoPset) ⊆ osAuMask := by
  have h1 : (↑walN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  have h2 : (↑walN : CoPset) ## ↑osShN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2
    ⟨LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h1 p ⟨hp, hn⟩⟩, fun hn => h2 p ⟨hp, hn⟩⟩

/-- **`J'` is a directory under `J` through the claims `cl`**: each step a name of a directory whose
whole claim (`except []`) is in `cl` holding the next directory. -/
inductive ClReach (cl : List Claim) : Ino → Ino → Prop
  | refl (J : Ino) : ClReach cl J J
  | step (J J' J'' : Ino) (h : NamesH) (b : GoString) :
      (J, NameSet.except [], h) ∈ cl → h.cur !! b = some (.dir J') → ClReach cl J' J'' →
      ClReach cl J J''

/-- **The claims `cl` cover the subtree of the entry `e`**: every directory under it has its whole
claim in `cl`. -/
def SubCover (cl : List Claim) (e : Option Node) : Prop :=
  ∀ J, e = some (.dir J) → ∀ J', ClReach cl J J' → ∃ h, (J', NameSet.except [], h) ∈ cl

/-- The name `n.tmp` of `Create`'s temporary directory (`filepath.Clean(dir) + ".tmp"`, S/wal.go:112). -/
def tmpName (nm : GoString) : GoString := nm ++ go!".tmp"

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The whole of the name `b` of `j` (its claim's history `h`), and of everything under it.** -/
def osSubtreeH (j : Ino) (b : GoString) (h : NamesH) : IProp GF :=
  iprop(∃ (cl : List Claim), osNames (L := L) j (.only [b]) (DFrac.own 1) h ∗
    osClaims L (cl.map (fun c => (c, DFrac.own 1))) ∗ ⌜SubCover cl (h.cur !! b)⌝)

/-- **The whole of the name `b` of `j`, and of everything under it.** -/
def osSubtree (j : Ino) (b : GoString) : IProp GF :=
  iprop(∃ (h : NamesH), osSubtreeH (L := L) j b h)

/-- **The WAL area `r` (the directory `jr` under the roots `R`), shared** (persistent): the WAL
invariant and the file system's invariants; and the receipts' bound (`ReceiptBoundLe GF (2 ^ 62)`,
fixed by the adequacy theorem that allocates the area, `notes/bounds-plan.md`'s rule 1), which an open
handle turns into its pipeline count's bound (`walOpenWF` holds `⧗ pc`, one receipt per file its
pipeline has handed over since `Open`/`Create`: `pc + 1 < 2 ^ 62`, what `cut`'s Go `int` count and its
signed `count % 2` need). And a law of the marshaller parameter `Mr` (ledger 2026-11-14): every hard
state's encoding is below `2 ^ 32` bytes (raft's `HardState` is three varints, at most 33 bytes;
discharged at C6 from raftpb's encoder), so that `cut`'s header records fit (`cut.spec`'s `2 ^ 42`,
with the metadata's bound the open handle carries, `walOpenWF`). -/
def walAreaOk (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : IProp GF :=
  iprop(walInv (L := L) (W := W) C Mr R jr r ∗ osInv (L := L) ∗ osSharedInv (L := L) R ∗
    ⌜ReceiptBoundLe GF (2 ^ 62)⌝ ∗ ⌜∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32⌝)

instance walAreaOk_persistent (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    Persistent (walAreaOk (L := L) (W := W) C Mr R jr r) := by
  unfold walAreaOk; infer_instance

/-- **The marshaller's law** (`walAreaOk`'s): a hard state's encoding is below `2 ^ 32` bytes. -/
theorem walAreaOk_encState (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    ⊢@{IProp GF} walAreaOk (L := L) (W := W) C Mr R jr r -∗
      ⌜∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32⌝ := by
  unfold walAreaOk
  iintro ⟨-, -, -, -, %h⟩
  ipureintro; exact h

/-- The claims of a list tagged with the name `b` (the program's claims under `b`, `walAreaRes`). -/
def clOf (cl : List (GoString × Claim)) (b : GoString) : List Claim :=
  (cl.filter (fun c => decide (c.1 = b))).map (·.2)

/-- **A temporary directory's entry, as `Create` can work with it** (`walAreaRes`): nothing, or a
directory whose every whole claim among `cl` (the claims under it) holds only files. -/
def TmpOk (cl : List Claim) (e : Option Node) : Prop :=
  e = none ∨ ∃ J, e = some (.dir J) ∧ ∀ hJ, (J, NameSet.except [], hJ) ∈ cl → FilesOnly hJ.cur

/-- **The program's part of the WAL area's directory `jr`** (exclusive): its half of the claim on
names `N` containing every WAL name not split out (`Wn`, `walSplitFrag`: the registered WALs' names, each
in its own claim, `walNamesRes`; G-spine, W1 log, fourteenth session) and every name `nm.<sfx>` of a WAL
name (`Create`'s `nm.tmp`, the cleanup's `nm.broken.<time>`; the invariant holds the other half), and, for each non-WAL name `b` of `N`, the whole
claims of every directory under it (`SubCover`; each claim tagged with the name it is under, so that a
function working on `b`'s subtree takes and gives back `b`'s claims only: W4 log, eleventh session); a
WAL name's temporary directory `nm.tmp` (a leftover of a `Create` a crash interrupted) holds nothing or a
directory of files only (`TmpOk`: the WAL creates nothing else there), so that `Create`'s
`os.RemoveAll(nm.tmp)` (`os.RemoveAll.specDirS`) applies. -/
def walAreaRes (jr : Ino) : IProp GF :=
  iprop(∃ (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString),
    osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗ walSplitFrag (W := W) Wn ∗
    ⌜∀ nm, walNameOk nm → N.Mem nm ∨ nm ∈ Wn⌝ ∗
    ⌜∀ nm sfx, walNameOk nm → N.Mem (nm ++ go!"." ++ sfx)⌝ ∗
    osClaims L (cl.map (fun c => (c.2, DFrac.own 1))) ∗
    ⌜∀ b, N.Mem b → ¬ walNameOk b → SubCover (clOf cl b) (h.cur !! b)⌝ ∗
    ⌜∀ nm, walNameOk nm → TmpOk (clOf cl (tmpName nm)) (h.cur !! tmpName nm)⌝)

end res

end WalFs
end EtcdGrove
end Perennial

end
