/- Lean-first (no Rocq counterpart).

# Registering and removing an open handle's tail (`notes/wal-fsext-plan.md`, W1 log, eleventh session)

The tails' authority is halved between the invariant (`walTailsAuth`, in `walTailsRes`) and the lock
holder (`walTailsFrag`). A holder registers its WAL's tail (`ReadAll`, `Create`) by combining both
halves into the whole authority, inserting the key and splitting back (`walTails_register`); `Close`
removes it the same way (`walTails_unregister`). `walTailsRes_register` is the registration inside the
invariant's part: a fresh ghost variable for the tail, its invariant half in the map, the program's
half and the key returned, with the holder's half `walTailsFrag {dir ↦ γ}`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section ghost
variable {GF : BundledGFunctors} [W : WalGS GF]

/-- **A tail registered**: the key `dir ↦ γ` inserted into both halves of the tails' authority. -/
theorem walTails_register (T : GMap GoString GName) (dir : GoString) (γ : GName) (hT : T !! dir = none) :
    ⊢@{IProp GF} walTailsAuth (W := W) T -∗ walTailsFrag (W := W) T ==∗
      walTailsAuth (W := W) (<[dir := γ]> T) ∗ walTailsFrag (W := W) (<[dir := γ]> T) ∗
        walTailKey (W := W) dir γ := by
  unfold walTailsAuth walTailsFrag walTailKey
  letI := walAllG (W := W)
  iintro Ha Hf
  ihave Hw := (ghostMapAuth_halves (GF := GF) W.γt T).2 $$ [Ha Hf]
  · iframe Ha Hf
  imod ghost_map_insert (GF := GF) dir γ hT $$ Hw with ⟨Hw, Hk⟩
  icases (ghostMapAuth_halves (GF := GF) W.γt (<[dir := γ]> T)).1 $$ Hw with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf Hk

/-- **A tail removed** (`Close`): the key deleted from both halves. -/
theorem walTails_unregister (T : GMap GoString GName) (dir : GoString) (γ : GName) :
    ⊢@{IProp GF} walTailsAuth (W := W) T -∗ walTailsFrag (W := W) T -∗ walTailKey (W := W) dir γ ==∗
      walTailsAuth (W := W) (GMap.delete dir T) ∗ walTailsFrag (W := W) (GMap.delete dir T) := by
  unfold walTailsAuth walTailsFrag walTailKey
  letI := walAllG (W := W)
  iintro Ha Hf Hk
  ihave Hw := (ghostMapAuth_halves (GF := GF) W.γt T).2 $$ [Ha Hf]
  · iframe Ha Hf
  imod ghost_map_delete (GF := GF) $$ Hw Hk with Hw
  icases (ghostMapAuth_halves (GF := GF) W.γt (GMap.delete dir T)).1 $$ Hw with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf

end ghost

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A holder with no tail registers its WAL's tail** in the invariant's part (`ReadAll`): the WAL
`d` in `dir` with its layout `lay`, last segment `g`, F-Z and the record boundary; a fresh ghost
variable `γ` of the shared tail, half in the invariant's map. -/
theorem walTailsRes_register (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (d : WalDur) (lay : WalLay) (g : SegG)
    (hp : s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
      TailBound C Mr d lay) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) ∅ ==∗ ∃ γ : GName,
      walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) (<[dir := γ]> ∅) ∗ walTailKey (W := W) dir γ ∗
        (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino))) := by
  unfold walTailsRes
  letI := walAllG (W := W)
  iintro ⟨%T, Ha, %Ho, %Hi, Hm, HL⟩ Hf
  icases walTails_agree (W := W) T ∅ $$ Ha Hf with %hT
  subst hT
  imod (ghostVar_alloc (GF := GF) (tailG d lay g.ino (F !! g.ino))) with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (GF := GF) γ 1 (tailG d lay g.ino (F !! g.ino))).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod walTails_register (W := W) ∅ dir γ (GMap.lookup_empty _) $$ Ha Hf with ⟨Ha, Hf, Hk⟩
  imodintro
  iexists γ
  iframe Hf Hk Hv2
  iexists <[dir := γ]> ∅
  ihave HL := walLentRes_reg (W := W) ∅ Ls dir γ (GMap.lookup_empty _)
    (fun la hla => by rw [hp.2.1] at hla; cases hla; exact hp.2.2.2.1) $$ HL
  iframe Ha HL
  isplitr
  · ipureintro
    intro i hi
    exact absurd (Ho.none_of_empty i) hi
  isplitr
  · ipureintro
    intro k d' lay' hk hd' hl'
    exact Hi k d' lay' (GMap.lookup_empty _) hd' hl'
  iapply (BigSepM.bigSepM_insert (Φ := fun (dir' : GoString) (γ' : GName) => iprop(∃ (d : WalDur)
      (lay : WalLay) (g : SegG), ⌜s.wal !! dir' = some d ∧ Ls !! dir' = some lay ∧
        lay.segs.getLast? = some g ∧ TailZ0 lay ∧ TailBound C Mr d lay⌝ ∗
      ghostVar γ' (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) (GMap.lookup_empty _)).2
  iframe Hm
  iexists d, lay, g
  iframe Hv1
  ipureintro; exact ⟨hp.1, hp.2.1, hp.2.2.1, Or.inl hp.2.2.2.1, hp.2.2.2.2⟩

/-- **A holder with no tail registers its WAL's tail, not yet zeroed** (I3b, `wal-tc15`; `ReadAll`
after a crash): as `walTailsRes_register`, under `TailZ0` (F-Z, or nothing written past the start's
frames) in place of F-Z; the holder gets the pending token `walPendTok dir γ |old|` in place of the
key, which goes into the invariant (`walLentRes_regPend`), until the fdatasync after `ZeroToEnd`
(`walLentRes_unpend`). -/
theorem walTailsRes_registerPend (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState) (Ls : GMap GoString WalLay)
    (F : GMap Ino SegFl) (dir : GoString) (d : WalDur) (lay : WalLay) (g : SegG)
    (hp : s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧
      TailBound C Mr d lay) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailsFrag (W := W) ∅ ==∗ ∃ γ : GName,
      ⌜TailZ0 lay⌝ ∗ walTailsRes (W := W) C Mr s Ls F ∗ walTailsFrag (W := W) (<[dir := γ]> ∅) ∗
        walPendTok (W := W) dir γ lay.old.length ∗
        (letI := walAllG (W := W); ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino))) := by
  unfold walTailsRes
  letI := walAllG (W := W)
  iintro ⟨%T, Ha, %Ho, %Hi, Hm, HL⟩ Hf
  icases walTails_agree (W := W) T ∅ $$ Ha Hf with %hT
  subst hT
  imod (ghostVar_alloc (GF := GF) (tailG d lay g.ino (F !! g.ino))) with ⟨%γ, Hv⟩
  icases (ghostVar_split_half (GF := GF) γ 1 (tailG d lay g.ino (F !! g.ino))).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod walTails_register (W := W) ∅ dir γ (GMap.lookup_empty _) $$ Ha Hf with ⟨Ha, Hf, Hk⟩
  icases walLentRes_idle (W := W) ∅ Ls $$ HL with ⟨%hI, HL⟩
  have hz0 : TailZ0 lay := hI dir lay (GMap.lookup_empty _) hp.2.1
  imod walLentRes_regPend (W := W) ∅ Ls dir γ lay (GMap.lookup_empty _) hp.2.1 $$ Hk HL with ⟨Hl, HL⟩
  imodintro
  iexists γ
  iframe Hf Hl Hv2
  isplitr
  · ipureintro; exact hz0
  iexists <[dir := γ]> ∅
  iframe Ha HL
  isplitr
  · ipureintro
    intro i hi
    exact absurd (Ho.none_of_empty i) hi
  isplitr
  · ipureintro
    intro k d' lay' hk hd' hl'
    exact Hi k d' lay' (GMap.lookup_empty _) hd' hl'
  iapply (BigSepM.bigSepM_insert (Φ := fun (dir' : GoString) (γ' : GName) => iprop(∃ (d : WalDur)
      (lay : WalLay) (g : SegG), ⌜s.wal !! dir' = some d ∧ Ls !! dir' = some lay ∧
        lay.segs.getLast? = some g ∧ TailZ0 lay ∧ TailBound C Mr d lay⌝ ∗
      ghostVar γ' (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) (GMap.lookup_empty _)).2
  iframe Hm
  iexists d, lay, g
  iframe Hv1
  ipureintro; exact ⟨hp.1, hp.2.1, hp.2.2.1, hz0, hp.2.2.2⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
