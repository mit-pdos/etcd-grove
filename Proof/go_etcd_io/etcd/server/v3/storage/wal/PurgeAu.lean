/- Lean-first (no Rocq counterpart).

# A purge's removal: its update for `os.Remove.specFileSncN` (unit `locks`, session 9)

`walPurge_osAUnc`: the atomic update a purge round gives `os.Remove.specFileSncN` for the removal of the
segment named `bt` (inode `i`) of the WAL directory `j` (the claim `(j, .except X, hj)`: the program's half,
lent by the handle, and the invariant's; the key `walDirKey dir j X`), while the WAL's handle is lent to the
round (`walOpenWF`: its tail record `tg`, its locked range `b`, its record of what is out `o`, the lock
token's `walCutFrag none`). The program keeps a quarter of its half of the claim in the update (`walPurgeP`),
to agree with the invariant's at the opening; the call gets the other quarter. `walCut_osAUnc`'s shape.

* *Opening* (with the generation's `notCrashed`): opens `walInv`, finds the key's claim (`DirKeysOk`), agrees
  with the program's, hands out the invariant's half with the quarter.
* *Abort*, or a commit with no effect: closed again; the program's resources back.
* *Commit* (the unlink logged at `x` by a call begun at `s0`): no cut pending; the tail record gives the WAL
  `d` and its layout `lay` (`tg`'s cuts are `lay`'s); the locked range is at most `d.unl` (`LksOk`); `bt` is the
  first segment's name, not the last (`purge_first_seg`: the smallest `.wal` name, with a larger one), so the
  removed segment ends at or before `b ≤ d.unl` (`LkRel_purge`); the caller's repeatable commit
  (`walPurgeAcc`) moves the client's state with `p := d.unl` and the read position to the next segment's
  start; the invariant moves to `purSt` (`purgeCommit_pure`, `walTailsRes_purge`, `laysResF_purge`,
  `walParked_purge`), the claim replaced by its logged successor (`purgeClaim`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeAuLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllGive
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeSafe

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **What a purge holds for a removal's update**: the directory's key, the tail's key and the handle's half of
its tail record, a quarter of the WAL claim (the call has another), the handle's record of what is out, the
lock token's pending-cut flag (`none`), the handle's half of the locked range (`b`), and the caller's commit
token `Pc`. -/
def walPurgeP (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (γ : GName) (tg : TailG)
    (γt : GName) (b : Nat) (o : WalOut) (Pc : IProp GF) : IProp GF :=
  iprop(walDirKey (W := W) dir (incOf I dir) j X ∗ walIncQ (W := W) I ∗ walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗
    osNames j (.except X) (DFrac.own qQuarter) hj ∗ walOutFrag (W := W) o ∗ walCutFrag (W := W) none ∗
    walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) (<[dir := b]> (∅ : GMap GoString Nat)) ∗
    Pc)

/-- **What a purge gets from a removal's update**: with no effect, what it held; after the commit (logged at
`x` by a call begun at `s0`), the claim's new history (a quarter), the rest as it held it. -/
def walPurgeQ (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (γ : GName) (tg : TailG)
    (γt : GName) (b : Nat) (o : WalOut) (Pc : IProp GF) (bt : GoString) (i : Ino) :
    Option (Nat × Nat) → IProp GF
  | none => walPurgeP (W := W) dir I j X hj γ tg γt b o Pc
  | some (x, s0) => walPurgeP (W := W) dir I j X (purgeClaim j X hj bt i x s0).2.2 γ tg γt b o Pc

/-- **A purge's update for `os.Remove.specFileSncN`** (see the file header). The premises, over the handle's
view: `bt` names `i` in the claim, the smallest `.wal` name, not the only one; its sequence `sq` below
`2^64`; the handle's locked range `b` (`LkRel`, `walDirLks`'s), `bt` neither the tail's name `nm0` nor a
locked segment's (the purger's lock on `i` excludes the latter: `walDirLks_purge`), so the segment ends at
or before `b` (`LkRel_purge`). -/
theorem walPurge_osAUnc (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (I : GMap GoString Nat) (j : Ino) (X : List GoString) (hj : NamesH) (γ : GName) (tg : TailG) (γt : GName)
    (b : Nat) (o : WalOut) (Pc : IProp GF) (inc : Nat) (bt : GoString) (i : Ino) (sq ix : Nat)
    (nm0 : GoString) (ls : List (GoString × Ino))
    (hoD : (j, NameSet.except X) ∈ o.D)
    (hcur : hj.cur !! bt = some (.file i)) (hbtw : walNameP bt = true)
    (hfirst : ∀ b' n, hj.cur !! b' = some n → walNameP b' = true → b' = bt ∨ go.GoStringLt bt b')
    (hlast : ∃ b' n, hj.cur !! b' = some n ∧ walNameP b' = true ∧ go.GoStringLt bt b')
    (hbt : bt = walFileName sq ix) (hsq : sq < 2 ^ 64) (hlk : LkRel hj tg.2.2.1 nm0 ls b)
    (h0 : bt ≠ nm0) (hnl : bt ∉ ls.map (·.1)) :
    ⊢ walInv (W := W) walCodec Mr R jr r -∗ walPurgeAcc (W := W) dir inc Pc -∗
      walPurgeP (W := W) dir I j X hj γ tg γt b o Pc -∗
      osAUnc (osNames j (.except X) (DFrac.own ((1 : Qp).half + qQuarter)) hj)
        (rmFileOutN j (.except X) bt i hj (DFrac.own ((1 : Qp).half + qQuarter)))
        (walPurgeQ (W := W) dir I j X hj γ tg γt b o Pc bt i) := by
  iintro #Hinv #Hacc HP
  iapply osAUnc_coiter _ _ _ (walPurgeP (W := W) dir I j X hj γ tg γt b o Pc) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod walInv_open walCodec Mr R jr r osAuMask walN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  rw [show osAuMask \ (↑walN : CoPset) = walAuMask from rfl]
  icases Hb with ⟨%s, Hb⟩
  unfold walPurgeP
  icases HP with ⟨#Hkey, HIq, Hk, Hv, Hq, Ho, Hcf, Htf, HPc⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, ⟨%CR, Hcra, %Hcro⟩,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookupI K dir j X I $$ Hdk Hkey HIq with %HK
  obtain ⟨lay1, hj1, hl1, hj1j, hjjr, hXw, honce, hcoh, hexcl⟩ := Hdko.1 dir j X HK
  obtain ⟨l1, l2, hcl, hn1, hn2⟩ := honce
  subst hcl
  icases (osClaims_split _ _ _ _).1 $$ Hcl0 with ⟨Hl1, Hα, Hl2⟩
  icases osNames_agree j (.except X) _ _ hj1 hj $$ Hα Hq with %Hhj
  subst Hhj
  ihave Hw := (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).2 $$ [Hα Hq]
  · iframe Hα Hq
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ walAuMask from
    Std.LawfulSet.empty_subset)) with Hcl'
  imodintro
  iframe Hw Hnc
  isplit
  · -- abort
    iintro Hw
    icases (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).1 $$ Hw with ⟨Hα, Hq⟩
    imod Hcl'
    imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
    · iexists s
      iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
      iframe Hg Hcm Hlays Htl Hpk
      isplitr
      · ipureintro; exact Har
      isplitl [Hl1 Hα Hl2]
      · iapply (osClaims_split _ _ _ _).2
        iframe Hl1 Hα Hl2
      isplitr
      · ipureintro; exact Hok
      isplitr
      · ipureintro; exact Hco
      isplitl [Hcra]
      · iexists CR
        iframe Hcra
        ipureintro; exact Hcro
      isplitr
      · ipureintro; exact Han
      isplitr
      · ipureintro; exact Hnm
      isplitl [Hdk Hcp]
      · iexists K, cp
        iframe Hdk Hcp
        ipureintro; exact Hdko
      iframe Hnms; ipureintro; exact ⟨HAt, Hbd⟩
    imodintro
    dsimp only
    iframe Hkey HIq Hk Hv Hq Ho Hcf Htf HPc
  · iintro %oc Hβ
    rcases oc with _ | ⟨x, s0⟩
    · -- no effect: as the abort
      unfold rmFileOutN
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Hw⟩
      icases (osNames_frac j (.except X) (1 : Qp).half qQuarter hj1).1 $$ Hw with ⟨Hα, Hq⟩
      imod Hcl'
      imod Hcl $$ [Hg Hl1 Hα Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists s
        iexists Ls, l1 ++ (j, NameSet.except X, hj1) :: l2, n, F
        iframe Hg Hcm Hlays Htl Hpk
        isplitr
        · ipureintro; exact Har
        isplitl [Hl1 Hα Hl2]
        · iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hα Hl2
        isplitr
        · ipureintro; exact Hok
        isplitr
        · ipureintro; exact Hco
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; exact Hcro
        isplitr
        · ipureintro; exact Han
        isplitr
        · ipureintro; exact Hnm
        isplitl [Hdk Hcp]
        · iexists K, cp
          iframe Hdk Hcp
          ipureintro; exact Hdko
        iframe Hnms; ipureintro; exact ⟨HAt, Hbd⟩
      imodintro
      dsimp only [walPurgeQ, walPurgeP]
      iframe Hkey HIq Hk Hv Hq Ho Hcf Htf HPc
    · imod Hcl'
      unfold rmFileOutN
      simp only [logOut, claimOut]
      icases Hβ with ⟨⟨%hls, Hlog⟩, Hwn⟩
      unfold osLogged
      icases Hlog with ⟨%hsx, -, -⟩
      simp only [rmFileEnt] at hsx
      icases (osNames_frac j (.except X) (1 : Qp).half qQuarter _).1 $$ Hwn with ⟨Hαn, Hqn⟩
      -- no cut pending
      icases walCut_agree cp none $$ Hcp Hcf with %Hcpn
      subst Hcpn
      -- the tail record: the WAL and its layout
      icases walTailsRes_lookupR walCodec Mr s Ls F dir γ tg $$ Htl Hk Hv with ⟨%hlk, Htl, Hk, Hv⟩
      obtain ⟨d, lay, gl, hd, hl, -, htg⟩ := hlk
      rw [hl1] at hl; cases hl
      have hcuts : tg.2.2.1 = lay1.cuts := by rw [htg]; rfl
      -- the locked range: at most `unl`
      icases walGhost_lksAgree s _ _ $$ Hg Htf with ⟨%hlks, Hg, Htf⟩
      obtain ⟨d1, hd1, hbu⟩ := hlks dir b (GMap.lookup_insert_eq _ _ _)
      rw [hd] at hd1; cases hd1
      -- the static relation, over the claim's names
      obtain ⟨la, nm, hja, hla, -, -, -, ⟨Xa, hXa, hma, -⟩, habs, -⟩ := Hok.1 dir d hd
      rw [hl1] at hla
      cases hla
      rw [hj1j] at hma
      have hjae := walClaim_eq hexcl hXa hma
      simp only [Prod.mk.injEq, true_and] at hjae
      rw [hjae.2] at habs
      have hclm : (j, NameSet.except X, hj1) ∈ l1 ++ (j, NameSet.except X, hj1) :: l2 :=
        List.mem_append_right _ (List.mem_cons_self ..)
      have hsn : SegsNamed lay1.segs hj1.cur :=
        (Hnm dir lay1 hl1).1 hj1 ⟨X, hXw, by rw [hj1j]; exact hclm, by rw [hj1j]; exact hcoh⟩
      have hnd : (walInos hj1.cur).Nodup := by
        rw [habs.names.1]; exact segsAll_nodup_segs Hok.2.2.1 hl1
      obtain ⟨g0, gs, hs, hgs, hi, hsqf⟩ := purge_first_seg habs hsn hnd hcur hbtw hfirst hlast hbt hsq
        (by rw [← hcuts]; exact hlk.2.1)
      subst hi
      have hp : segStart lay1.cuts (lay1.first + 1) ≤ d.unl := by
        have hb := (LkRel_purge hlk (by rw [hcuts]; exact habs.cuts.2.1) hcur hbtw h0 hnl hbt hsq).2
        rw [← hsqf, ← hcuts]; exact Nat.le_trans hb hbu
      have hlen := habs.cuts.2.2
      rw [hs] at hlen
      have hgl : 1 ≤ gs.length := List.length_pos_iff.2 hgs
      simp only [List.length_cons] at hlen
      have hcutk : d.cut ≤ segStart lay1.cuts (lay1.first + 1) := by
        rw [habs.cut.1]; exact segStart_le_succ habs.cuts.2.1 (by omega)
      obtain ⟨hok', hco', hcro', han', hnm', hdko', -, -⟩ := purgeCommit_pure walCodec_ok (x := x) (s0 := s0)
        Hok Hco Hcro Han.1 Hnm Hdko HK hd hl1 hs hgs ⟨l1, l2, rfl, hn1, hn2⟩ hcur hbtw hp hls hsx
      -- the client's commit
      iunfold walPurgeAcc at Hacc
      ihave Hac := Hacc $$ HPc
      unfold atomic_acc
      imod Hac with Hac
      isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hac
      icases Hac with ⟨%dc, Hdc, Hucl⟩
      unfold walDiskAtI walDirIsI
      icases Hdc with ⟨%M, %Iq, HM, HIq, %HMd, %hIq⟩
      icases walOwn_agree s M $$ Hg HM with %HMs
      icases Hucl with ⟨-, Hcommit⟩
      isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
      obtain ⟨d0, hM0, hle0⟩ := (walOptLe_some_iff _ _).1 HMd
      have hle : walDurLe dc d := by
        have h1 := HMs dir
        rw [hM0, hd] at h1
        obtain ⟨ds, hds, hle1⟩ := (walOptLe_some_iff _ _).1 h1
        cases hds
        exact walDurLe_trans hle0 hle1
      imod walGhost_upd s (purSt s dir d.unl (segStart lay1.cuts (lay1.first + 1))) M (absLe_purSt _ _ _ _)
        (walKeysInArea_upd s dir _) (fun _ hn => hn.upd (fun _ => rfl))
        (unlMono_upd s dir _ (fun _ => Nat.le_refl _)) $$ Hg HM with ⟨-, Hg, HM, -⟩
      imod Hcommit $$ %d.unl %(segStart lay1.cuts (lay1.first + 1)) [HM HIq] with HPc
      · isplitr
        · ipureintro
          refine ⟨by rw [hle.2.2.2.1]; exact hcutk, hp, Nat.le_of_eq hle.2.1.symm⟩
        · iexists (purSt s dir d.unl (segStart lay1.cuts (lay1.first + 1))).wal, Iq
          iframe HM HIq
          ipureintro
          rw [purSt_self hd]
          exact ⟨walDurLe_purD hle _ _, hIq⟩
      -- the invariant's resources at the new state
      have hpd := purSt_self (p := d.unl) (k := segStart lay1.cuts (lay1.first + 1)) hd
      ihave Htl := walTailsRes_purge walCodec Mr s (purSt s dir d.unl (segStart lay1.cuts (lay1.first + 1)))
        Ls F dir lay1 g0 gs hl1 hs hgs (fun k d' hk => ?_) (fun k d' hk => ?_) $$ Htl
      · by_cases e : k = dir
        · subst e; rw [hd] at hk; cases hk; exact ⟨_, hpd, rfl, rfl⟩
        · exact ⟨d', by rw [purSt_ne e]; exact hk, rfl, rfl⟩
      · by_cases e : k = dir
        · subst e; rw [hpd] at hk; cases hk; exact ⟨d, hd, rfl, rfl⟩
        · exact ⟨d', by rw [← purSt_ne e]; exact hk, rfl, rfl⟩
      ihave Hlays := laysResF_purge F Ls dir lay1 g0 gs hl1 hs $$ Hlays
      icases walParked_purge Ls l1 l2 (j, NameSet.except X, hj1) (purgeClaim j X hj1 bt g0.ino x s0) dir lay1
        g0 gs F o hl1 hs ⟨rfl, rfl⟩ hoD (fun b' n' _ h => purgeNames_sub h) $$ Hpk Ho with ⟨Hpk, Ho⟩
      ihave Hnms := walNamesRes_congr R jr r Ls s (purSt s dir d.unl (segStart lay1.cuts (lay1.first + 1)))
        (namedSub_upd s dir _ (fun _ => rfl)) $$ Hnms
      ihave Hnms := walNamesRes_insert _ _ _ _ dir lay1 (purgeLayP lay1 g0) hl1 rfl rfl $$ Hnms
      imod Hcl $$ [Hg Hl1 Hαn Hl2 Hlays Hcra Htl Hpk Hdk Hcp Hnms]
      · iexists (purSt s dir d.unl (segStart lay1.cuts (lay1.first + 1)))
        iexists <[dir := purgeLayP lay1 g0]> Ls,
          replClaim (j, NameSet.except X, hj1) (purgeClaim j X hj1 bt g0.ino x s0)
            (l1 ++ (j, NameSet.except X, hj1) :: l2), n, F
        iframe Hg Hcm Hlays Htl
        isplitr
        · ipureintro; rw [purSt_area]; exact Har
        isplitl [Hl1 Hαn Hl2]
        · rw [replClaim_split hn1 hn2]
          iapply (osClaims_split _ _ _ _).2
          iframe Hl1 Hl2
          dsimp only [purgeClaim, purgeNames]
          iexact Hαn
        isplitr
        · ipureintro; exact hok'
        isplitr
        · ipureintro; exact hco'
        isplitl [Hcra]
        · iexists CR
          iframe Hcra
          ipureintro; exact hcro'
        isplitr
        · ipureintro
          exact ⟨han', fun dd hdd => Han.2 dd (by rw [← purSt_dirs s dir d.unl
            (segStart lay1.cuts (lay1.first + 1))]; exact hdd)⟩
        isplitr
        · ipureintro; exact hnm'
        isplitl [Hpk]
        · rw [replClaim_split hn1 hn2]; iexact Hpk
        isplitl [Hdk Hcp]
        · iexists K, none
          iframe Hdk Hcp
          ipureintro; exact hdko'
        isplitr
        · ipureintro
          exact walsAt_repl HAt hl1 rfl rfl (by simpa [purgeClaim] using hjjr)
        iframe Hnms; ipureintro
        exact ⟨walsBounded_upd Hbd.1 (fun _ => rfl) (fun _ => rfl), Hbd.2.upd⟩
      imodintro
      dsimp only [walPurgeQ, walPurgeP, purgeClaim, purgeNames]
      iframe Hkey HIq Hk Hv Hqn Ho Hcf Htf HPc
end au

end WalFs
end EtcdGrove
end Perennial

end
