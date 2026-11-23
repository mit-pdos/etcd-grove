/- Lean-first (no Rocq counterpart).

# The vocabulary of `wal.Create`'s and `fileutil.TouchDirAll`'s specs over `fsExt` (W4)

`notes/wal-fsext-plan.md`, §3 ("Must change") and the "W4 implementation log". Untrusted.

* **`walAuMask`**: the outer mask of the WAL's client atomic updates. The WAL commits them inside
  the step of an `os` call (`osAU`, `Proof/os/SharedAu.lean`), with the WAL invariant open:
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

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import Proof.os.SharedAu
public import Spec.os.RemoveAll
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

-- `ClReach`, `SubCover`: moved to `Spec/os/RemoveAll.lean` (os.RemoveAll.specSubS takes them).

/-- **A name `nm.broken.<sfx>` of a WAL name** (W4 session 4): where `Create`'s cleanup renames a WAL
being created (`cleanupWAL`), whose directory's claims stay the invariant's; `walAreaRes` asks nothing
of what is under it. -/
def BrokenSlot (b : GoString) : Prop := ∃ nm sfx, walNameOk nm ∧ b = nm ++ go!".broken." ++ sfx

/-- The name `n.tmp` of `Create`'s temporary directory (`filepath.Clean(dir) + ".tmp"`, S/wal.go:112). -/
def tmpName (nm : GoString) : GoString := nm ++ go!".tmp"

/-- Two names cut at their first `.`. -/
theorem dot_cut {a b x y : GoString} (ha : W8 46 ∉ a) (hb : W8 46 ∉ b)
    (h : a ++ W8 46 :: x = b ++ W8 46 :: y) : a = b ∧ x = y := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons c b => simp at h; exact absurd (h.1 ▸ List.mem_cons_self ..) hb
  | cons c a ih =>
    cases b with
    | nil => simp at h; exact absurd (h.1 ▸ List.mem_cons_self ..) ha
    | cons c' b =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨e1, e2⟩ := ih (fun hm => ha (List.mem_cons_of_mem _ hm))
        (fun hm => hb (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [e1], e2⟩

/-- A WAL name's temporary directory is no broken name. -/
theorem tmpName_not_broken {nm : GoString} (hnm : walNameOk nm) : ¬ BrokenSlot (tmpName nm) := by
  rintro ⟨nm', sfx, hnm', he⟩
  unfold tmpName at he
  have e1 : nm ++ go!".tmp" = nm ++ W8 46 :: go!"tmp" := rfl
  have e2 : nm' ++ go!".broken." ++ sfx = nm' ++ W8 46 :: (go!"broken." ++ sfx) := by
    simp [List.append_assoc]
  rw [e1, e2] at he
  have := (dot_cut hnm.2.2 hnm'.2.2 he).2
  simp at this

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
with the metadata's bound the open handle carries, `walOpenWF`). And the dispenser of the call permission
above the roots (`osAboveInv`: `Create`'s `TouchDirAll` stats and syncs the area's ancestors). -/
def walAreaOk (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : IProp GF :=
  iprop(walInv (L := L) (W := W) C Mr R jr r ∗ osInv (L := L) ∗ osSharedInv (L := L) R ∗
    ⌜ReceiptBoundLe GF (2 ^ 62)⌝ ∗ ⌜∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32⌝ ∗
    osAboveInv (L := L))

instance walAreaOk_persistent (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    Persistent (walAreaOk (L := L) (W := W) C Mr R jr r) := by
  unfold walAreaOk; infer_instance

/-- **The marshaller's law** (`walAreaOk`'s): a hard state's encoding is below `2 ^ 32` bytes. -/
theorem walAreaOk_encState (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    ⊢@{IProp GF} walAreaOk (L := L) (W := W) C Mr R jr r -∗
      ⌜∀ hs : HardStateM, (Mr.encState hs).length < 2 ^ 32⌝ := by
  unfold walAreaOk
  iintro ⟨-, -, -, -, %h, -⟩
  ipureintro; exact h

/-- The ghost names' roots are the area's (`walInv`'s). -/
theorem walAreaOk_roots (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    ⊢@{IProp GF} walAreaOk (L := L) (W := W) C Mr R jr r -∗ ⌜W.roots = R⌝ := by
  unfold walAreaOk
  iintro ⟨Hi, -⟩
  iapply walInv_roots $$ Hi

/-- The claims of a list tagged with the name `b` (the program's claims under `b`, `walAreaRes`). -/
def clOf (cl : List (GoString × Claim)) (b : GoString) : List Claim :=
  (cl.filter (fun c => decide (c.1 = b))).map (·.2)

/-- **The program's claims of the area** (`walAreaRes`), each whole and tagged with the name it is
under. (Until 2026-11-22 with the probe files of the temporary directories', `tmpClTouch`, which
`CreateDirAll.specTmp`'s truncation of a leftover `.touch` needed: ledger 2026-11-22.) -/
def areaCls (cl : List (GoString × Claim)) : IProp GF :=
  iprop(osClaims L (cl.map (fun c => (c.2, DFrac.own 1))))

/-- **The program's part of the WAL area's directory `jr`** (exclusive): its half of the claim on
names `N` containing every WAL name not split out (`Wn`, `walSplitFrag`: the registered WALs' names, each
in its own claim, `walNamesRes`; G-spine, W1 log, fourteenth session) and every name `nm.<sfx>` of a WAL
name (`Create`'s `nm.tmp`, the cleanup's `nm.broken.<time>`; the invariant holds the other half), and, for each non-WAL name `b` of `N`, the whole
claims of every directory under it (`SubCover`, but under a `BrokenSlot`, where the cleanup moves a WAL
being created aside; each claim tagged with the name it is under, so that a
function working on `b`'s subtree takes and gives back `b`'s claims only: W4 log, eleventh session); under
a WAL name's temporary directory `nm.tmp` (a leftover of a `Create` a crash interrupted, holding anything)
the claims hold no cycle (`ClRanked`), so that `Create`'s `os.RemoveAll(nm.tmp)` (`os.RemoveAll.specSubS`)
applies. (Until 2026-11-22 `TmpOk`, a directory of files only, and its `.touch`'s file: ledger 2026-11-22.) -/
def walAreaRes (jr : Ino) : IProp GF :=
  iprop(∃ (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString),
    osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗ walSplitFrag (W := W) Wn ∗
    ⌜∀ nm, walNameOk nm → N.Mem nm ∨ nm ∈ Wn⌝ ∗
    ⌜∀ nm sfx, walNameOk nm → N.Mem (nm ++ go!"." ++ sfx)⌝ ∗
    areaCls (L := L) cl ∗
    ⌜∀ b, N.Mem b → ¬ walNameOk b → ¬ BrokenSlot b → SubCover (clOf cl b) (h.cur !! b)⌝ ∗
    ⌜∀ nm, walNameOk nm → ClRanked (clOf cl (tmpName nm))⌝)

end res

end WalFs
end EtcdGrove
end Perennial

end
