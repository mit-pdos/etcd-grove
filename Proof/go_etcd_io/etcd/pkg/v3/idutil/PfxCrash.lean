/-
**A prefix's ids' invariant across a crash** (T10 B6 (b), 2026-11-26; ledger 2026-11-26, "B6 (b)"). The
old generation's `idPfxInv` holds its ids' map at the names `γip` the cluster's claims point to
(`gen`); the restarted generation gets its own at the same names: every id of the map becomes an
earlier incarnation's (`idIssueCrashStart`), the old invariant's ids' map is cancelled by depositing the
old record's authority (`idIssueDeadD`, which refutes any later step of the old generation,
`wp_IdIssue_live`), and the new invariant gets a fresh, empty generators' map.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs
public import GooseLang.Ext.IdIssue.Crash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

open Iris.Std in
/-- **The prefix's ids' invariant at the restarted generation** (`L'`), from the old generation's
(`L`) and the issue record's crash rest, which it consumes (its authority cancels the old ids' map). -/
theorem idPfxInv_crash (L L' : GooseLocalGS GF) (gen : GName) (p : w64) :
    ⊢ idPfxInv (hG := ⟨Gg, L⟩) gen p -∗
      idIssueCrashStart (gooseIdIssueGS (L := L)) (gooseIdIssueGS (L := L')) ={⊤}=∗
      idPfxInv (hG := ⟨Gg, L'⟩) gen p := by
  iintro #Hpi Hc
  iunfold idPfxInv at Hpi
  icases Hpi with ⟨%γip, %γgp, #Hp, #Hinv⟩
  iinv Hinv with Hb Hclose
  iunfold idPfxBody at Hb
  icases Hb with ⟨HGpp, >HIpd⟩
  iunfold idIssueCrashStart at Hc
  icases Hc with ⟨%Mg, HA, #HE⟩
  icases HIpd with (⟨%Ip, HIp, #HIps⟩ | Hd)
  rotate_left
  · -- already cancelled: two authorities of the old record
    rw [idIssueDeadD_eq]
    iunfold idIssueDeadAt at Hd
    icases Hd with ⟨%Mg', HA'⟩
    letI := (gooseIdIssueGS (L := L)).idIssueAllG
    ihave %H := ghostMapAuth_valid_2 _ 1 1 Mg Mg' $$ HA HA'
    exact absurd H.1 (by decide)
  -- every id of the map is in the old record
  ihave %Hall : ⌜∀ id, (Ip !! id).isSome → (Mg !! id).isSome⌝ $$ [HA]
  · iapply (pure_forall (PROP := IProp GF)
      (φ := fun id => (Ip !! id).isSome → (Mg !! id).isSome)).2
    iintro %id
    cases hI : Ip !! id with
    | none => ipureintro; simp
    | some ig =>
      icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := Ip)
        (Φ := fun id ig => iprop(idPfxIdFact (hG := ⟨Gg, L⟩) γgp id ig ∗ id ↪[γip]□ ig)) hI).1
        $$ HIps with ⟨⟨#Hf, -⟩, -⟩
      iunfold idPfxIdFact at Hf
      letI := (gooseIdIssueGS (L := L)).idIssueAllG
      icases Hf with (⟨#Hf, -⟩ | #Hf)
      · rw [idIssueFragD_eq id ig.2]
        iunfold idIssueFrag idIssueFragAt idIssueElemAt at Hf
        ihave %Hl := ghost_map_lookup $$ HA Hf
        ipureintro; intro _; simp [show Mg.lookup id = _ from Hl]
      · rw [idIssuePastD_eq id]
        iunfold idIssuePast idIssuePastAt idIssueElemAt at Hf
        ihave %Hl := ghost_map_lookup $$ HA Hf
        ipureintro; intro _; simp [show Mg.lookup id = _ from Hl]
  -- the new generation's generators' map, fresh
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Nat)) with ⟨%γgp', Hg⟩
  -- the map's facts at the restarted generation: every id an earlier incarnation's
  ihave #HIps' : iprop([∗map] id ↦ ig ∈ Ip,
      idPfxIdFact (hG := ⟨Gg, L'⟩) γgp' id ig ∗ id ↪[γip]□ ig) $$ []
  · iapply (BigSepM.bigSepM_forall (PROP := IProp GF)).2
    iintro %id %ig %hI
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := Ip)
      (Φ := fun id ig => iprop(idPfxIdFact (hG := ⟨Gg, L⟩) γgp id ig ∗ id ↪[γip]□ ig)) hI).1
      $$ HIps with ⟨⟨-, #Hel⟩, -⟩
    iframe Hel
    have hs : (Mg !! id).isSome := Hall id (by simp [hI])
    have hc : idIssueCrash Mg !! id = some none := by
      cases hm : Mg !! id with
      | none => simp [hm] at hs
      | some w =>
        show (Mg !! id).map (fun _ => (none : Option Loc)) = some none
        rw [hm]; rfl
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (m := idIssueCrash Mg)
      (Φ := fun i v => idIssueElemAt (gooseIdIssueGS (L := L')) i v) hc).1 $$ HE with ⟨#Hpast, -⟩
    iunfold idPfxIdFact
    iright
    rw [idIssuePastD_eq id]
    iunfold idIssuePast idIssuePastAt
    iexact Hpast
  -- the new generation's invariant: the same ids' map, every id past, and the fresh generators' map
  imod (inv_alloc idPfxN (⊤ \ ↑idPfxN) (idPfxBody (hG := ⟨Gg, L'⟩) γip γgp')) $$ [HIp Hg] with #Hinv'
  · inext
    iunfold idPfxBody
    isplitl [Hg]
    · iexists ∅
      iframe Hg
      iapply BigSepM.bigSepM_empty.2; itrivial
    · ileft
      iexists Ip
      iframe HIp HIps'
  -- the old ids' map cancelled
  imod Hclose $$ [HGpp HA] with -
  · inext
    iunfold idPfxBody
    iframe HGpp
    iright
    rw [idIssueDeadD_eq]
    iunfold idIssueDeadAt
    iexists Mg
    iexact HA
  imodintro
  iunfold idPfxInv
  iexists γip, γgp'
  iframe Hp Hinv'

end crash

end EtcdGrove
end Perennial
