/- Lean-first (no Rocq counterpart).

# The WAL name `Create` works on, free in the program's part of the area (W4, `notes/wal-units/fresh.md`)

`walAreaResFree jr nm`: `walAreaRes jr` with `nm` in the program's area claim, nothing there, and `nm` not
registered (no WAL's name). What `Exist(r/nm)` answering `false` leaves, the lock token held
(`wal.Exist.wp_core`); what `Create` starts from, in place of reading the absence off its client's update
(`walInv_absent`), so that its update may start from any view of `r/nm` (`wal.Create.spec`'s `Pv`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **`walAreaRes jr` with the WAL name `nm` free** (see the file header): `nm` is in the program's
area claim, holds nothing there, and is not registered (`walSplitFrag`). `Create` needs the three: the
first two for its `RemoveAll` and its rename onto `nm`, the third for its commit (with the lock token's
pending registration `none`, every present WAL's name is registered, so the real state has no WAL in
`r/nm`, whatever the client's view of it). -/
def walAreaResFree (jr : Ino) (nm : GoString) : IProp GF :=
  iprop(∃ (N : NameSet) (h : NamesH) (cl : List (GoString × Claim)) (Wn : List GoString),
    osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗ walSplitFrag (W := W) Wn ∗
    ⌜∀ nm, walNameOk nm → N.Mem nm ∨ nm ∈ Wn⌝ ∗
    ⌜∀ nm sfx, walNameOk nm → N.Mem (nm ++ go!"." ++ sfx)⌝ ∗
    areaCls (L := L) cl ∗
    ⌜∀ b, N.Mem b → ¬ walNameOk b → ¬ BrokenSlot b → SubCover (clOf cl b) (h.cur !! b)⌝ ∗
    ⌜∀ nm, walNameOk nm → ClRanked (clOf cl (tmpName nm))⌝ ∗
    ⌜N.Mem nm ∧ h.cur !! nm = none ∧ nm ∉ Wn⌝)

/-- `walAreaResFree` forgets the free name. -/
theorem walAreaResFree_res (jr : Ino) (nm : GoString) :
    walAreaResFree (L := L) (W := W) jr nm ⊢ walAreaRes (L := L) (W := W) jr := by
  unfold walAreaResFree walAreaRes
  iintro ⟨%N, %h, %cl, %Wn, Hn, Hs, %a1, %a2, Hc, %a3, %a4, -⟩
  iexists N, h, cl, Wn
  iframe
  ipureintro; exact ⟨a1, a2, a3, a4⟩

end res

end WalFs
end EtcdGrove
end Perennial

end
