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

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost
import all Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section ghost
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- **A new handle** of `w` in `dir` (incarnation `i`) in mode `m`, under a fresh ghost name, with its
purge right. -/
theorem walHandle_alloc (w : Loc) (dir : GoString) (i : Nat) (m : WalMode) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walIncLb (W := W) dir i ==∗ walHandleAuth (W := W) ∗
      ∃ γ : GName, walHandleDirI (W := W) w dir i γ ∗ (letI := walAllG (W := W); γ ↪[W.γh] m) ∗
        (letI := walAllG (W := W); γ ↪[W.γhp] ()) := by
  letI := walAllG (W := W)
  unfold walHandleAuth walHandleDirI
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩ #Hil
  obtain ⟨h1, h2, h3⟩ := Hf n (Nat.le_refl n)
  imod ghost_map_insert n m h1 $$ HA with ⟨HA, Hm⟩
  imod ghost_map_insert_persist n (w, dir, i) h2 $$ HD with ⟨HD, #Hdir⟩
  imod ghost_map_insert n () h3 $$ HP with ⟨HP, Hpt⟩
  imodintro
  isplitl [HA HD HP]
  · iexists (n + 1), (Hh.insert n m), (Hd.insert n (w, dir, i)), (Hp.insert n ())
    iframe HA HD HP
    ipureintro
    intro k hk
    have hne : n ≠ k := by omega
    obtain ⟨h1', h2', h3'⟩ := Hf k (by omega)
    exact ⟨by rw [GMap.lookup_insert_ne _ _ hne]; exact h1',
      by rw [GMap.lookup_insert_ne _ _ hne]; exact h2',
      by rw [GMap.lookup_insert_ne _ _ hne]; exact h3'⟩
  · iexists n; iframe Hdir Hm Hpt Hil

/-- **A new handle with the lock token** (`walHandleP`, mode `m`). -/
theorem walHandleP_mint (w : Loc) (dir : GoString) (m : WalMode) (I : GMap GoString Nat) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walLockedTokI (W := W) I -∗
      walIncLb (W := W) dir (incOf I dir) ==∗
      walHandleAuth (W := W) ∗ walHandleP (W := W) w dir m := by
  iintro Ha Hl #Hil
  imod walHandle_alloc w dir (incOf I dir) m $$ Ha Hil with ⟨Ha, ⟨%γ, #Hd, Hm, Hp⟩⟩
  imodintro
  iframe Ha
  unfold walHandleP
  iexists γ, incOf I dir, I
  iframe Hd Hm Hp Hl
  ipureintro; rfl

/-- **A new handle with the lock token at the incarnations `I`**: the handle at `incOf I dir`. -/
theorem walHandleP_mintI (w : Loc) (dir : GoString) (m : WalMode) (I : GMap GoString Nat) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walLockedTokI (W := W) I -∗
      walIncLb (W := W) dir (incOf I dir) ==∗
      walHandleAuth (W := W) ∗ walHandlePI (W := W) w dir (incOf I dir) m := by
  iintro Ha Hl #Hil
  imod walHandle_alloc w dir (incOf I dir) m $$ Ha Hil with ⟨Ha, ⟨%γ, #Hd, Hm, Hp⟩⟩
  imodintro
  iframe Ha
  unfold walHandlePI
  iexists γ, I
  iframe Hd Hm Hp Hl
  ipureintro; rfl

/-- **The handle `Open` mints** (mode `opening s`). -/
theorem walOpening_mint (w : Loc) (dir : GoString) (s : w64 × w64) (I : GMap GoString Nat) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walLockedTokI (W := W) I -∗
      walIncLb (W := W) dir (incOf I dir) ==∗
      walHandleAuth (W := W) ∗ walOpening (W := W) w dir s (incOf I dir) := by
  unfold walOpening
  exact walHandleP_mintI w dir (.opening s) I

/-- **A handle's mode changed**, its purge right and lock token kept. -/
theorem walHandleP_set (w : Loc) (dir : GoString) (m m' : WalMode) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walHandleP (W := W) w dir m ==∗
      walHandleAuth (W := W) ∗ walHandleP (W := W) w dir m' := by
  letI := walAllG (W := W)
  unfold walHandleAuth walHandleP
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩ ⟨%γ, %i, %I, #Hdir, Hm, Hpt, Hl, %hi⟩
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
  · iexists γ, i, I; iframe Hdir Hm Hpt Hl; ipureintro; exact hi

/-- `walHandleP_set` at the incarnation `i` (kept). -/
theorem walHandlePI_set (w : Loc) (dir : GoString) (i : Nat) (m m' : WalMode) :
    ⊢@{IProp GF} walHandleAuth (W := W) -∗ walHandlePI (W := W) w dir i m ==∗
      walHandleAuth (W := W) ∗ walHandlePI (W := W) w dir i m' := by
  letI := walAllG (W := W)
  unfold walHandleAuth walHandlePI
  iintro ⟨%n, %Hh, %Hd, %Hp, HA, HD, HP, %Hf⟩ ⟨%γ, %I, #Hdir, Hm, Hpt, Hl, %hi⟩
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
  · iexists γ, I; iframe Hdir Hm Hpt Hl; ipureintro; exact hi

/-- **An append-mode handle as the client's** (`Create`'s handle): `walOpenW` and the purge right. -/
theorem walHandleP_openW (w : Loc) (dir : GoString) :
    walHandleP (W := W) w dir .append ⊢ walOpenW (W := W) w dir ∗ walPurgeW (W := W) w dir := by
  unfold walHandleP walOpenW walOpenWI walPurgeW walHandleStI walHandleDir
  iintro ⟨%γ, %i, %I, #Hd, Hm, Hp, Hl, %hi⟩
  isplitl [Hm Hl]
  · iexists i, I; iframe Hl; isplitl; · iexists γ; iframe Hd Hm
    ipureintro; exact hi
  · iexists γ; iframe Hp; iexists i; iexact Hd

/-- `walHandleP_openW` at the handle's incarnation. -/
theorem walHandlePI_openWI (w : Loc) (dir : GoString) (i : Nat) :
    walHandlePI (W := W) w dir i .append ⊢ walOpenWI (W := W) w dir i ∗ walPurgeW (W := W) w dir := by
  unfold walHandlePI walOpenWI walPurgeW walHandleStI walHandleDir
  iintro ⟨%γ, %I, #Hd, Hm, Hp, Hl, %hi⟩
  isplitl [Hm Hl]
  · iexists I; iframe Hl; isplitl; · iexists γ; iframe Hd Hm
    ipureintro; exact hi
  · iexists γ; iframe Hp; iexists i; iexact Hd

variable {hlc : HasLC} [GooseExts] [GooseInterp] [G : GooseGlobalGS hlc GF]

/-- The handles' authority is `walGhost`'s: taking it out and putting it back. -/
theorem walGhost_handleAuth (s : AbsDiskState) :
    walGhost (W := W) s ⊣⊢ walHandleAuth (W := W) ∗
      (walHandleAuth (W := W) -∗ walGhost (W := W) s) := by
  constructor
  · unfold walGhost walGhostI
    iintro ⟨%I, Hs, HP, ⟨Hh, Hlk⟩, %hk, #Hst⟩
    iframe Hh
    iintro Hh
    iexists I
    iframe Hs HP Hh Hlk Hst
    ipureintro; exact hk
  · iintro ⟨Hh, Hw⟩
    iapply Hw $$ Hh

end ghost

end WalFs
end EtcdGrove
end Perennial
