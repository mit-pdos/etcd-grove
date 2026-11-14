/- Lean-first (no Rocq counterpart).

# A cut's directory fsync: the alternative layout dropped (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

After `cut`'s rename (`walCut_osAUnc`: the WAL directory's claim logged the rename at `x`, the new
segment `i` at the `.wal` name `bt`; the WAL's crash condition with the old layout as its alternative;
the pending-cut flag `some dir`), `fileutil.Fsync(w.dirFile)` (`os.File.Sync.specDirS`) gives
`osCommitLb n` with `x < n`. Every crash then keeps the rename, so the new segment is named and the
alternative is impossible (`crashOk_dirSync`): the flag goes back to `none` (`DirKeysOk … none`).

* `walTailsRes_lookup`: the tail record of `dir` names its layout's last segment.
* `dirKeysOk_cutSynced` (pure): `DirKeysOk` at the raised bound with no cut pending.
* `walInvBody_cutSynced`: the step on the invariant's contents, with the program's fraction of the
  WAL directory's claim (agreeing with the invariant's half: the history ends with the rename), the
  directory's key, the tail record (its tail the new segment) and the commit bound. The program opens
  `walInv` around it (`wp_notCrashed_acc`, as `Create`'s parent fsync).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutAu
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **No cut pending once the rename is committed** (`x < n`): the cut WAL's alternative, if any, is
dropped (`crashOk_dirSync`: its segments a strict prefix of the layout's, which ends with the new
segment `g0`, so `g0` is not among them); the others as before, at the bigger bound. -/
theorem dirKeysOk_cutSynced {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n0 n : Nat}
    {K : GMap GoString (Ino × List GoString)} {dir : GoString} {d : WalDur} {lay : WalLay}
    {g0 : SegG} {X : List GoString} {hj : NamesH} {x : Nat} {e : LogEntry} {c : Ents}
    {bt : GoString}
    (hn : n0 ≤ n) (hx : x < n)
    (hok : WalsOk C Mr R jr s Ls cl n0) (hk : DirKeysOk C Mr jr s Ls cl n0 K (some dir))
    (hK : K !! dir = some (lay.j, X)) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hg0 : lay.segs.getLast? = some g0)
    (hcl : (lay.j, NameSet.except X, hj.log x e c) ∈ cl)
    (hw : e.op.Writes lay.j bt) (hwal : walNameP bt = true) (hc : c !! bt = some (.file g0.ino)) :
    DirKeysOk C Mr jr s Ls cl n K none := by
  refine ⟨hk.1, fun dir' d' lay' hd' hl' _ => ?_, hk.2.2⟩
  by_cases he : dir' = dir
  · rw [he, hd] at hd'
    cases hd'
    rw [he, hl] at hl'
    cases hl'
    obtain ⟨lay1, -, -, hl1, -, -, -, -, -, alt, halt, hcr⟩ := hok.1 dir d hd
    rw [hl] at hl1
    cases hl1
    obtain ⟨-, -, -, -, -, hX, -⟩ := hk.1 dir lay.j X hK
    have hbtX : bt ∉ X := fun h => by rw [hX bt h] at hwal; cases hwal
    cases alt with
    | none => exact crashOkA_mono hn hcr
    | some lay0 =>
      have hA := halt lay0 rfl
      have hi : g0.ino ∉ lay0.segs.map (·.ino) := by
        intro hm
        obtain ⟨g', hg', hgi⟩ := List.mem_map.1 hm
        obtain ⟨-, -, -, -, ⟨t, ht⟩, hlen⟩ := hA
        have htne : t ≠ [] := by
          intro h0; rw [h0, List.append_nil] at ht; rw [ht] at hlen; exact Nat.lt_irrefl _ hlen
        have hg0t : g0 ∈ t := by
          rw [← ht, List.getLast?_append] at hg0
          cases hlt : t.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hlt) htne
          | some a =>
            rw [hlt, Option.some_or] at hg0
            cases hg0
            exact List.mem_of_getLast? hlt
        have hnd := ((segsAll_nodup_iff Ls).1 hok.2.2.1).1 dir lay hl
        rw [← ht, List.map_append] at hnd
        exact (List.nodup_append.1 hnd).2.2 _ (List.mem_map_of_mem hg') _
          (List.mem_map_of_mem hg0t) hgi
      exact (crashOkA_none_iff C Mr d lay cl n).2
        (crashOk_dirSync C Mr d lay lay0 cl n X hj x e c bt g0.ino hA (crashOkA_mono hn hcr) hcl
          hx hw hbtX hwal hc hi)
  · exact crashOkA_mono hn (hk.2.1 dir' d' lay' hd' hl' (fun h => he (Option.some.inj h).symm))

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The tail record of `dir`** names the WAL, its layout and the layout's last segment. -/
theorem walTailsRes_lookup (C : WalCodec) (Mr : WalMarshal) (s : AbsDiskState)
    (Ls : GMap GoString WalLay) (F : GMap Ino SegFl) (dir : GoString) (γ : GName) (tg : TailG) :
    ⊢ walTailsRes (W := W) C Mr s Ls F -∗ walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗
      ⌜∃ (d : WalDur) (lay : WalLay) (g0 : SegG), s.wal !! dir = some d ∧ Ls !! dir = some lay ∧
          lay.segs.getLast? = some g0 ∧ tg = tailG d lay g0.ino (F !! g0.ino)⌝ ∗
        walTailsRes (W := W) C Mr s Ls F ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg := by
  letI := walAllG (W := W)
  unfold walTailsRes tailVar
  iintro ⟨%T, HTa, %HTo, HTm⟩ Hk Hv
  icases walTailKey_lookup T dir γ $$ HTa Hk with %HT
  ihave ⟨Hent, HTm⟩ := (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).1 $$ HTm
  icases Hent with ⟨%d, %lay, %g0, %hp, Hv'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Htg
  isplitr
  · ipureintro; exact ⟨d, lay, g0, hp.1, hp.2.1, hp.2.2.1, Htg⟩
  iframe Hk Hv
  iexists T
  iframe HTa
  isplitr
  · ipureintro; exact HTo
  iapply (BigSepM.bigSepM_delete (Φ := fun (dir : GoString) (γ : GName) =>
    iprop(∃ (d : WalDur) (lay : WalLay) (g : SegG),
      ⌜s.wal !! dir = some d ∧ Ls !! dir = some lay ∧ lay.segs.getLast? = some g ∧ TailZeros lay ∧
        TailBound C Mr d lay⌝ ∗
      ghostVar γ (1 : Qp).half (tailG d lay g.ino (F !! g.ino)))) HT).2
  iframe HTm
  iexists d, lay, g0
  iframe Hv'
  ipureintro; exact hp

/-- **The directory's fsync after a cut's rename** (see the file header): the program's fraction of
the WAL directory's claim, whose history ends with the rename (logged at `x`, writing the `.wal` name
`bt`, which then held the new segment `i`), the directory's key, the tail record (its tail `i`), the
pending-cut flag and the commit bound `n > x`: the flag back to `none`. -/
theorem walInvBody_cutSynced (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (x : Nat)
    (e : LogEntry) (c : Ents) (bt : GoString) (i : Ino) (dq : DFrac) (γ : GName) (tg : TailG)
    (n : Nat) (hx : x < n) (hw : e.op.Writes j bt) (hwal : walNameP bt = true)
    (hc : c !! bt = some (.file i)) (hti : tg.2.2.2.2.1 = i) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) dq (hj.log x e c) -∗ walTailKey (W := W) dir γ -∗
      tailVar (W := W) γ tg -∗ walCutFrag (W := W) (some dir) -∗ osCommitLb (L := L) n ==∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ osNames (L := L) j (.except X) dq (hj.log x e c) ∗
        walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗ walCutFrag (W := W) none := by
  iintro Hb #Hkey Hq Hk Hv Hcf #Hc
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, Hcr, Htl, %Han, %Hnm,
    Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hkey with %HK
  icases walCut_agree cp (some dir) $$ Hcp Hcf with %Hcpe
  subst Hcpe
  obtain ⟨lay1, hj1, hl1, hj1j, hjjr, -, honce, -, -⟩ := Hdko.1 dir j X HK
  subst hj1j
  obtain ⟨l1, l2, hcl, -, -⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  icases osNames_agree lay1.j (.except X) _ _ hj1 _ $$ Hα Hq with %Hhj
  subst Hhj
  ihave Hcl0 := (osClaims_split _ _ _ _).2 $$ [Hl1 Hα Hl2]
  · iframe Hl1 Hα Hl2
  icases walTailsRes_lookup C Mr s Ls F dir γ tg $$ Htl Hk Hv with ⟨%Ht, Htl, Hk, Hv⟩
  obtain ⟨d, lay, g0, hd, hl, hg0, htg⟩ := Ht
  rw [hl1] at hl
  cases hl
  have hgi : g0.ino = i := by rw [← hti, htg]; rfl
  subst hgi
  imod walCut_set (some dir) (some dir) none $$ Hcp Hcf with ⟨Hcp, Hcf⟩
  imodintro
  iframe Hq Hk Hv Hcf
  iexists Ls, l1 ++ (lay1.j, NameSet.except X, hj.log x e c) :: l2, max n0 n, F
  iframe Hg Hcl0 Hlays Htl Hpk
  isplitr
  · ipureintro; exact Har
  isplitr
  · rcases Nat.le_total n0 n with hle | hle
    · rw [Nat.max_eq_right hle]; iexact Hc
    · rw [Nat.max_eq_left hle]; iexact Hcm
  isplitr
  · ipureintro; exact walsOk_mono (Nat.le_max_left _ _) Hok
  isplitr
  · ipureintro; exact Hco
  iframe Hcr
  isplitr
  · ipureintro; exact ⟨absentNone_mono (Nat.le_max_left _ _) Han.1, Han.2⟩
  isplitr
  · ipureintro; exact walsNamed_mono (Nat.le_max_left _ _) Hnm
  isplitl [Hdk Hcp]
  · iexists K, none
    iframe Hdk Hcp
    ipureintro
    exact dirKeysOk_cutSynced (Nat.le_max_left _ _) (Nat.lt_of_lt_of_le hx (Nat.le_max_right _ _))
      Hok Hdko HK hd hl1 hg0 (hj := hj) (List.mem_append_right _ (List.mem_cons_self ..)) hw hwal hc
  iframe Hnms; ipureintro
  exact ⟨walsAt_mid hjjr HAt, Hbd⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
