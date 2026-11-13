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
  containing every WAL name and every `nm.<sfx>` of one (the invariant holds the other half:
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
invariant and the file system's invariants. -/
def walAreaOk (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) : IProp GF :=
  iprop(walInv (L := L) (W := W) C Mr R jr r ∗ osInv (L := L) ∗ osSharedInv (L := L) R)

instance walAreaOk_persistent (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) :
    Persistent (walAreaOk (L := L) (W := W) C Mr R jr r) := by
  unfold walAreaOk; infer_instance

/-- **The program's part of the WAL area's directory `jr`** (exclusive): its half of the claim on
names `N` containing every WAL name and every name `nm.<sfx>` of one (`Create`'s `nm.tmp`, the cleanup's
`nm.broken.<time>`; the invariant holds the other half), and the whole claims of every directory under
a non-WAL name of `N`. -/
def walAreaRes (jr : Ino) : IProp GF :=
  iprop(∃ (N : NameSet) (h : NamesH) (cl : List Claim),
    osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗ ⌜∀ nm, walNameOk nm → N.Mem nm⌝ ∗
    ⌜∀ nm sfx, walNameOk nm → N.Mem (nm ++ go!"." ++ sfx)⌝ ∗
    osClaims L (cl.map (fun c => (c, DFrac.own 1))) ∗
    ⌜∀ b, N.Mem b → ¬ walNameOk b → SubCover cl (h.cur !! b)⌝)

end res

end WalFs
end EtcdGrove
end Perennial

end
