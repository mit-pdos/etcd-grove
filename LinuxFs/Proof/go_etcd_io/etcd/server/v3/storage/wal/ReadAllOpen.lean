/- Lean-first (no Rocq counterpart).

# `ReadAll`'s success: the ghost handle `append` (W3/W5 of `notes/wal-fsext-plan.md`, twenty-fifth session)

At `ReadAll`'s success return (S/wal.go:684) the ghost handle's mode goes from `opening s` to `append`
(`walHandleP_set` on the handles' authority in `walInvBody`, as `walInv_failOpening` sets it to
`failed`), split into what the specs hand out: the write handle's mode and lock token (`walOpenW`,
which `walOpenWF` holds) and the purge right (`walPurgeW`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The ghost handle's mode set to `append`, on the invariant's contents. -/
theorem walInvBody_appendOpening (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (w : Loc) (dir : GoString) (sn : w64 × w64) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walOpening (W := W) w dir sn ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walOpenW (W := W) w dir ∗ walPurgeW (W := W) w dir := by
  iintro Hb Ho
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases (walGhost_handleAuth (W := W) s).1 $$ Hg with ⟨Ha, Hg⟩
  unfold walOpening
  imod walHandleP_set (W := W) w dir (.opening sn) .append $$ Ha Ho with ⟨Ha, Ho⟩
  ihave Hg := Hg $$ Ha
  unfold walHandleP
  icases Ho with ⟨%γ, #Hd, Hm, Hp, Hl⟩
  imodintro
  isplitl [Hg Hrest]
  · iexists Ls, cl, n, F
    iframe
  unfold walOpenW walHandleSt walPurgeW
  isplitl [Hm Hl]
  · iframe Hl
    iexists γ
    iframe Hd Hm
  · iexists γ
    iframe Hd Hp

/-- **`ReadAll` succeeded: the ghost handle `append`** (see the file header). -/
theorem walInv_appendOpening (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (w : Loc) (dir : GoString) (sn : w64 × w64) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walOpening (W := W) w dir sn ={⊤}=∗ notCrashed (hC := L.goose_crashGS) ∗
        (walOpenW (W := W) w dir ∗ walPurgeW (W := W) w dir) := by
  iintro #Hinv Hnc Ho
  iapply walInv_step C Mr R jr r (walOpening (W := W) w dir sn)
    iprop(walOpenW (W := W) w dir ∗ walPurgeW (W := W) w dir) ⊤
    CoPset.subseteq_top (fun s => by
      iintro Hb Ho
      imod walInvBody_appendOpening C Mr R jr r s w dir sn $$ Hb Ho with ⟨Hb, Ho⟩
      imodintro
      iframe)
    $$ Hinv Hnc Ho

end iris

end WalFs
end EtcdGrove
end Perennial

end
