/- Lean-first (no Rocq counterpart).

# Minting and changing the WAL layer's handles (W3/W5 of `notes/wal-fsext-plan.md`)

The handles' authority (`walHandleAuth`, sealed in `Ghost.lean`) sits in `walGhost`, in `walInvBody`;
its laws are here, over `import all` of `Ghost.lean` (the sealed bodies stay sealed to the WAL's
clients):

* `walHandle_alloc`: a fresh ghost name for a handle of `w` in `dir`, in mode `m`, with its purge
  right (as the extension's private `absHandle_alloc`).
* `walHandleP_mint`: with the lock token as an open handle holds it (`walLockedTok`), the handle
  (`walHandleP`); `walOpening_mint`, the mode `opening s` (`openAtIndex`'s write mode: `Open`).
* `walHandleP_set`: a handle's mode changed (`ReadAll`: `opening` to `append` or `failed`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section ghost
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- **A new handle** of `w` in `dir` in mode `m`, under a fresh ghost name, with its purge right. -/
theorem walHandle_alloc (w : Loc) (dir : GoString) (m : WalMode) :
    ⊢@{IProp GF} walHandleAuth (W := W) ==∗ walHandleAuth (W := W) ∗
      ∃ γ : GName, walHandleDir (W := W) w dir γ ∗ (letI := walAllG (W := W); γ ↪[W.γh] m) ∗
        (letI := walAllG (W := W); γ ↪[W.γhp] ()) := by
  letI := walAllG (W := W)
  unfold walHandleAuth walHandleDir
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩
  obtain ⟨h1, h2, h3⟩ := Hf n (Nat.le_refl n)
  imod ghost_map_insert n m h1 $$ HA with ⟨HA, Hm⟩
  imod ghost_map_insert_persist n (w, dir) h2 $$ HD with ⟨HD, #Hdir⟩
  imod ghost_map_insert n () h3 $$ HP with ⟨HP, Hpt⟩
  imodintro
  isplitl [HA HD HP]
  · iexists (n + 1), (Hh.insert n m), (Hd.insert n (w, dir)), (Hp.insert n ())
    iframe HA HD HP
    ipureintro
    intro k hk
    have hne : n ≠ k := by omega
    obtain ⟨h1', h2', h3'⟩ := Hf k (by omega)
    exact ⟨by rw [GMap.lookup_insert_ne _ _ hne]; exact h1',
      by rw [GMap.lookup_insert_ne _ _ hne]; exact h2',
      by rw [GMap.lookup_insert_ne _ _ hne]; exact h3'⟩
  · iexists n; iframe Hdir Hm Hpt

/-- **A new handle with the lock token** (`walHandleP`, mode `m`). -/
theorem walHandleP_mint (w : Loc) (dir : GoString) (m : WalMode) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walLockedTok (W := W) ==∗
      walHandleAuth (W := W) ∗ walHandleP (W := W) w dir m := by
  iintro Ha Hl
  imod walHandle_alloc w dir m $$ Ha with ⟨Ha, ⟨%γ, #Hd, Hm, Hp⟩⟩
  imodintro
  iframe Ha
  unfold walHandleP
  iexists γ
  iframe Hd Hm Hp Hl

/-- **The handle `Open` mints** (mode `opening s`). -/
theorem walOpening_mint (w : Loc) (dir : GoString) (s : w64 × w64) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walLockedTok (W := W) ==∗
      walHandleAuth (W := W) ∗ walOpening (W := W) w dir s := by
  unfold walOpening
  exact walHandleP_mint w dir (.opening s)

/-- **A handle's mode changed**, its purge right and lock token kept. -/
theorem walHandleP_set (w : Loc) (dir : GoString) (m m' : WalMode) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walHandleP (W := W) w dir m ==∗
      walHandleAuth (W := W) ∗ walHandleP (W := W) w dir m' := by
  letI := walAllG (W := W)
  unfold walHandleAuth walHandleP
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩ ⟨%γ, #Hdir, Hm, Hpt, Hl⟩
  icases ghost_map_lookup $$ HA Hm with %Hlk
  imod ghost_map_update m' $$ HA Hm with ⟨HA, Hm⟩
  imodintro
  isplitl [HA HD HP]
  · iexists n, (Hh.insert γ m'), Hd, Hp
    iframe HA HD HP
    ipureintro
    intro k hk
    obtain ⟨h1, h2, h3⟩ := Hf k hk
    have hne : γ ≠ k := by
      rintro rfl
      have : Hh !! γ = some m := Hlk
      rw [h1] at this; cases this
    exact ⟨by rw [GMap.lookup_insert_ne _ _ hne]; exact h1, h2, h3⟩
  · iexists γ; iframe Hdir Hm Hpt Hl

/-- **An append-mode handle as the client's** (`Create`'s handle): `walOpenW` and the purge right. -/
theorem walHandleP_openW (w : Loc) (dir : GoString) :
    walHandleP (W := W) w dir .append ⊢ walOpenW (W := W) w dir ∗ walPurgeW (W := W) w dir := by
  unfold walHandleP walOpenW walPurgeW walHandleSt
  iintro ⟨%γ, #Hd, Hm, Hp, Hl⟩
  iframe Hl
  isplitl [Hm]
  · iexists γ; iframe Hd Hm
  · iexists γ; iframe Hd Hp

/-- The handles' authority is `walGhost`'s: taking it out and putting it back. -/
theorem walGhost_handleAuth (s : AbsDiskState) :
    walGhost (W := W) s ⊣⊢ walHandleAuth (W := W) ∗
      (walHandleAuth (W := W) -∗ walGhost (W := W) s) := by
  constructor
  · unfold walGhost
    iintro ⟨Hs, HP, Hh, %hk⟩
    iframe Hh
    iintro Hh
    iframe Hs HP Hh
    ipureintro; exact hk
  · iintro ⟨Hh, Hw⟩
    iapply Hw $$ Hh

end ghost

end WalFs
end EtcdGrove
end Perennial
