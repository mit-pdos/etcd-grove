/- Lean-first (no Rocq counterpart).

# `wal.Exist`'s ghost steps (W12, `notes/wal-fsext-plan.md`)

`Exist(dir)` reads the WAL directory `dir = r/nm` with `ReadDir`. It linearizes at a ghost step before
the read (`walInv_existStart`): the client's update, run on the invariant's contents (any `A` with
its `hA`: the update committed unchanged, `walInvBody_existAU`), and what the area holds at `nm`, from
the program's half of the area claim (as `walInvBody_areaAt`):
* no WAL: nothing at `nm` (`AbsentNone`), so `ReadDir` fails;
* a WAL: its directory `J` at `nm` (`WalsAt`); the lock taken (`walParked_lock`) and the program's half
  of the directory's claim `(J, .except X, hj)` taken out of the parked state (`walParked_takeClaim`),
  for `ReadDir` to read through; a `.wal` name is in `J` (a segment's, `WalsNamed`, `WalAbsD.nonempty`).
After the read (a WAL present), a second ghost step (`walInv_existEnd`) puts the claim back and
releases the lock: the WAL is still there (a past state's, `absLe`), at `nm` with the same directory
`J` (`WalsAt`), whose claim among the invariant's is the program's (`osClaims_keys`), once (three
halves are invalid).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenPinTake
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ExistPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.NameSplit

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The client's update committed unchanged** at a step of the invariant's contents: the client's
lower bound `o` below the real state. -/
theorem walInvBody_existAU (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (Q : Option WalDur → IProp GF) :
    ⊢ (AU <{ ∃∃ o : Option WalDur, walDirIs (W := W) dir o }> @ walAuMask, ∅
        <{ walDirIs (W := W) dir o, COMM Q o }>) -∗
      walInvBody (L := L) (W := W) C Mr R jr r s ={⊤ \ ↑walN}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ ∃ o, Q o ∗ ⌜walOptLe o (s.wal !! dir)⌝ := by
  iintro Hau Hb
  have hsub : walAuMask ⊆ (⊤ : CoPset) \ ↑walN := by
    intro p hp
    exact LawfulSet.mem_diff.2 ⟨CoPset.mem_full, (LawfulSet.mem_diff.1 hp).2⟩
  imod (fupd_mask_subseteq hsub) with Hmc
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%o, Hab0, Hcla⟩
  icases Hcla with ⟨-, Hco⟩
  unfold walDirIs
  icases Hab0 with ⟨%M, HM, %HMd⟩
  iunfold walInvBody at Hb
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases walOwn_agree s M $$ Hg HM with %HMs
  imod Hco $$ [HM] with HQ
  · iexists M; iframe HM; ipureintro; exact HMd
  imod Hmc with -
  imodintro
  isplitl [Hg Hrest]
  · iunfold walInvBody; iexists Ls, cl, n, F; iframe
  iexists o
  iframe HQ
  ipureintro
  exact walOptLe_trans HMd (HMs dir)

/-- **What the area holds at the WAL's name `nm`, and the WAL directory's claim pinned** (see the file
header): the contents unchanged, the program's half of the area claim and its split names back. No WAL:
`nm` is not split (`split_absent`), so the program's area claim holds it, absent. A WAL: its name is
split (the lock's `walNamesFrag none`), and its name claim and the area's spine are lent for the read
(`walNamesRes_lendAt`); the WAL's key records its directory for the end step. -/
theorem walInvBody_existPin (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm : GoString) (N : NameSet) (h : NamesH) (Wn : List GoString)
    {Em : CoPset} (hin : InArea r dir nm) (hN : N.Mem nm ∨ nm ∈ Wn) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h -∗ walSplitFrag (W := W) Wn -∗
      walUnlockedTok (W := W) ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
      walSplitFrag (W := W) Wn ∗
      ((⌜s.wal !! dir = none ∧ N.Mem nm ∧ h.cur !! nm = none⌝ ∗ walUnlockedTok (W := W)) ∨
       (⌜s.wal !! dir ≠ none⌝ ∗ ∃ (J : Ino) (X : List GoString) (hj : NamesH) (q1 q2 : Qp) (hn : NamesH),
          ⌜hn.cur !! nm = some (.dir J) ∧ (∀ b ∈ X, walNameP b = false) ∧
            ∃ b, walNameP b = true ∧ (hj.cur !! b).isSome⌝ ∗
          osNames (L := L) jr (.only [nm]) (DFrac.own q1) hn ∗ osPathS (L := L) R r (DFrac.own q2) jr ∗
          walDirKey (W := W) dir J X ∗ walLockedTok (W := W) ∗
          (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
          walOutFrag (W := W) (WalOut.empty.addClaim (J, .except X)) ∗
          osNames (L := L) J (.except X) (DFrac.own (1 : Qp).half) hj)) := by
  iintro Hb #Hsi H Hsf Hu
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, HCR, Ht, %hab,
    %hwn, Hpk, Hdk, %hAt, Hnms, %Hbd⟩
  icases walNamesRes_splitOk (L := L) (W := W) R jr r Ls Wn $$ Hnms Hsf with ⟨Hnms, Hsf, %hW⟩
  have hin' : InArea s.area dir nm := by rw [hr]; exact hin
  cases hsd : s.wal !! dir with
  | none =>
    have hN' : N.Mem nm := hN.resolve_right (split_absent hwo hW hin' hsd)
    imod osClaims_keys R jr N _ h _ (nameSet_ne_empty hN') hE $$ Hsi H Hcl with ⟨H, Hcl, %hkeys⟩
    obtain ⟨N1, h1, hm1, hN1⟩ := hwc nm hin.1
    obtain ⟨rfl, rfl⟩ := hkeys ((jr, N1, h1), _) (List.mem_map_of_mem hm1) rfl nm hN' hN1
    have hnone : h1.cur !! nm = none := (hab.1 dir nm hin' hsd).1 N1 h1 hm1 hN'
    imodintro
    iframe H Hsf
    isplitr [Hu]
    · iexists Ls, cl, n, F
      iframe
      ipureintro; exact ⟨hr, hwo, hwc, hab, hwn, hAt, Hbd⟩
    ileft
    iframe Hu
    ipureintro; exact ⟨rfl, hN', hnone⟩
  | some d =>
    obtain ⟨lay, nm', hj, hl, hin2, -, hnm', hc, habs, -⟩ := hwo.1 dir d hsd
    have e : nm' = nm := List.append_cancel_left (hin2.2.symm.trans hin'.2)
    subst e
    obtain ⟨X, hX, hcX, hcoh⟩ := hc
    have hsn : SegsNamed lay.segs hj.cur := (hwn dir lay hl).1 hj ⟨X, hX, hcX, hcoh⟩
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ habs.nonempty
    obtain ⟨hgw, hgj⟩ := hsn.1 g hg
    icases Hdk with ⟨%K, %cp, HKa, Hca, %HDK⟩
    imod walDirKeys_pin C Mr jr s Ls cl n K cp dir lay X hj HDK hl hX hcX $$ HKa
      with ⟨%K', HKa, %HDK', #Hkey⟩
    imod walParked_lock (L := L) (W := W) Ls cl F $$ Hpk Hu with ⟨Hpk, Hl, Ho, Htf, Hnf, -⟩
    imod walParked_takeClaim (L := L) (W := W) Ls cl F WalOut.empty (lay.j, .except X, hj) hcX
      ⟨dir, lay, hl, rfl, X, rfl, hX⟩ (by simp [WalOut.empty]) $$ Hpk Ho with ⟨Hpk, Ho, HJ⟩
    icases walNamesRes_lendAt (L := L) (W := W) R jr r Ls dir lay nm' hl hnm' $$ Hnms Hnf
      with ⟨Hnms, Hnf, %q1, %q2, %hn, Hn1, Hsp, %hlend⟩
    imodintro
    iframe H Hsf
    isplitr [Hl Ho Htf Hnf HJ Hn1 Hsp]
    · iexists Ls, cl, n, F
      iframe Hg Hcl Hn HF HCR Ht Hpk Hnms
      isplitr; · ipureintro; exact hr
      isplitr; · ipureintro; exact hwo
      isplitr; · ipureintro; exact hwc
      isplitr; · ipureintro; exact hab
      isplitr; · ipureintro; exact hwn
      isplitl [HKa Hca]
      · iexists K', cp; iframe HKa Hca; ipureintro; exact HDK'
      ipureintro; exact ⟨hAt, Hbd⟩
    iright
    isplitr
    · ipureintro; simp
    iexists lay.j, X, hj, q1, q2, hn
    iframe Hn1 Hsp Hkey Hl Htf Hnf Ho HJ
    ipureintro
    exact ⟨hlend.2, hX, g.name, hgw, by rw [hgj]; rfl⟩

/-- **The WAL directory's claim put back, the lock released** (see the file header): the WAL's key
names its directory `J` and the names `X` its claim leaves out, whose claim among the invariant's is
the program's (`osClaims_keys`), once (three halves are invalid). -/
theorem walInvBody_existUnpin (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (J : Ino) (X : List GoString) (hj : NamesH) {Em : CoPset}
    (hX : ∀ b ∈ X, walNameP b = false) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      walDirKey (W := W) dir J X -∗
      walLockedTok (W := W) -∗ (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) -∗
      walOutFrag (W := W) (WalOut.empty.addClaim (J, .except X)) -∗
      osNames (L := L) J (.except X) (DFrac.own (1 : Qp).half) hj ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ walUnlockedTok (W := W) := by
  classical
  iintro Hb #Hsi #Hk Hl Htf Ho HJ
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %hr, Hcl, Hn, HF, %hwo, %hwc, HCR, Ht, %hab,
    %hwn, Hpk, ⟨%K, %cp, HKa, Hca, %HDK⟩, %hAt, Hnms, %Hbd⟩
  icases walDirKey_lookup (W := W) K dir J X $$ HKa Hk with %hK
  obtain ⟨lay1, hj', -, -, -, -, ho1, -, -⟩ := HDK.1 dir J X hK
  have hcX' : (J, NameSet.except X, hj') ∈ cl := by
    obtain ⟨l1, l2, e, -, -⟩ := ho1; rw [e]; simp
  have hXe : NameSet.except X ≠ .only [] := by simp
  imod osClaims_keys R J (.except X) _ hj _ hXe hE $$ Hsi HJ Hcl with ⟨HJ, Hcl, %hk2⟩
  have hb0X : (NameSet.except X).Mem go!"a.wal" := except_mem_of_walNameP hX walNameP_ex
  have hsame : ∀ c ∈ cl, c.1 = J → c.2.1 = .except X → c = (J, .except X, hj) := by
    intro c hc hcJ hcN
    have hb0c : c.2.1.Mem go!"a.wal" := by rw [hcN]; exact hb0X
    obtain ⟨e1, e2⟩ := hk2 (c, _) (List.mem_map_of_mem hc) hcJ go!"a.wal" hb0X hb0c
    obtain ⟨c1, c2, c3⟩ := c
    simp only at hcJ e1 e2
    rw [hcJ, e1, e2]
  have hcm : (J, NameSet.except X, hj) ∈ cl := by
    have := hsame _ hcX' rfl rfl; rw [← this]; exact hcX'
  obtain ⟨l1, l2, rfl, hl1⟩ := List.split_first hcm
  icases (osClaims_split (L := L) l1 l2 (J, NameSet.except X, hj) _).1 $$ Hcl with ⟨H1, Hc0, H2⟩
  by_cases hl2 : (J, NameSet.except X, hj) ∈ l2
  · obtain ⟨m1, m2, rfl, -⟩ := List.split_first hl2
    icases (osClaims_split (L := L) m1 m2 (J, NameSet.except X, hj) _).1 $$ H2 with ⟨-, Hc1, -⟩
    iexfalso
    iapply osNames_three_halves J (.except X) hj hj hj hXe $$ HJ Hc0 Hc1
  have hkey : ∀ c' ∈ l1 ++ l2, (c'.1, c'.2.1) ≠ ((J, NameSet.except X, hj).1, (J, NameSet.except X, hj).2.1) := by
    intro c' hc' he
    simp only [Prod.mk.injEq] at he
    have hc'm : c' ∈ l1 ++ (J, NameSet.except X, hj) :: l2 := by
      rcases List.mem_append.1 hc' with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
    have := hsame c' hc'm he.1 he.2
    subst this
    rcases List.mem_append.1 hc' with h' | h'
    · exact hl1 h'
    · exact hl2 h'
  ihave Hcl := (osClaims_split (L := L) l1 l2 (J, NameSet.except X, hj) _).2 $$ [H1 Hc0 H2]
  · iframe H1 Hc0 H2
  imod walParked_putClaim (L := L) (W := W) Ls l1 l2 F _ (J, NameSet.except X, hj) hkey
    $$ Hpk Ho HJ with ⟨Hpk, Ho⟩
  have hoe : (WalOut.empty.addClaim (J, NameSet.except X)).delClaim (J, NameSet.except X) =
      WalOut.empty := by simp [WalOut.empty, WalOut.addClaim, WalOut.delClaim]
  ihave Ho := walOutFrag_eq' (W := W) WalOut.empty $$ Ho %hoe
  icases Htf with ⟨Htf, Hnf⟩
  imod walParked_unlock (L := L) (W := W) Ls _ F $$ Hpk Hl Ho Htf Hnf with ⟨Hpk, Hu⟩
  imodintro
  iframe Hu
  iexists Ls, l1 ++ (J, NameSet.except X, hj) :: l2, n, F
  iframe Hg Hcl Hn HF HCR Ht Hpk Hnms
  isplitr; · ipureintro; exact hr
  isplitr; · ipureintro; exact hwo
  isplitr; · ipureintro; exact hwc
  isplitr; · ipureintro; exact hab
  isplitr; · ipureintro; exact hwn
  isplitl [HKa Hca]
  · iexists K, cp; iframe HKa Hca; ipureintro; exact HDK
  ipureintro; exact ⟨hAt, Hbd⟩

/-- **`Exist`'s start step** (see the file header), at a program step: the update `A` run (`hA`),
what the area holds at `nm`, the claim pinned and the name claim lent if a WAL is there. -/
theorem walInv_existStart (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm : GoString) (N : NameSet) (h : NamesH) (Wn : List GoString) (A : IProp GF)
    (Lin : Option WalDur → IProp GF)
    (hA : ∀ s, ⊢ A -∗ walInvBody (L := L) (W := W) C Mr R jr r s ={⊤ \ ↑walN}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ Lin (s.wal !! dir))
    (hin : InArea r dir nm) (hN : N.Mem nm ∨ nm ∈ Wn) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ A -∗
      osNames (L := L) jr N (DFrac.own (1 : Qp).half) h -∗ walSplitFrag (W := W) Wn -∗
      walUnlockedTok (W := W) ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
      walSplitFrag (W := W) Wn ∗ ∃ od, Lin od ∗
      ((⌜od = none ∧ N.Mem nm ∧ h.cur !! nm = none⌝ ∗ walUnlockedTok (W := W)) ∨
       (⌜od ≠ none⌝ ∗ ∃ (J : Ino) (X : List GoString) (hj : NamesH) (q1 q2 : Qp) (hn : NamesH),
          ⌜hn.cur !! nm = some (.dir J) ∧ (∀ b ∈ X, walNameP b = false) ∧
            ∃ b, walNameP b = true ∧ (hj.cur !! b).isSome⌝ ∗
          osNames (L := L) jr (.only [nm]) (DFrac.own q1) hn ∗ osPathS (L := L) R r (DFrac.own q2) jr ∗
          walDirKey (W := W) dir J X ∗ walLockedTok (W := W) ∗
          (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
          walOutFrag (W := W) (WalOut.empty.addClaim (J, .except X)) ∗
          osNames (L := L) J (.except X) (DFrac.own (1 : Qp).half) hj)) := by
  iintro #Hinv #Hsi Hnc HA H Hsf Hu
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ A ∗ osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗
      walSplitFrag (W := W) Wn ∗ walUnlockedTok (W := W))
    iprop(osNames (L := L) jr N (DFrac.own (1 : Qp).half) h ∗ walSplitFrag (W := W) Wn ∗
      ∃ od, Lin od ∗
      ((⌜od = none ∧ N.Mem nm ∧ h.cur !! nm = none⌝ ∗ walUnlockedTok (W := W)) ∨
       (⌜od ≠ none⌝ ∗ ∃ (J : Ino) (X : List GoString) (hj : NamesH) (q1 q2 : Qp) (hn : NamesH),
          ⌜hn.cur !! nm = some (.dir J) ∧ (∀ b ∈ X, walNameP b = false) ∧
            ∃ b, walNameP b = true ∧ (hj.cur !! b).isSome⌝ ∗
          osNames (L := L) jr (.only [nm]) (DFrac.own q1) hn ∗ osPathS (L := L) R r (DFrac.own q2) jr ∗
          walDirKey (W := W) dir J X ∗ walLockedTok (W := W) ∗
          (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
          walOutFrag (W := W) (WalOut.empty.addClaim (J, .except X)) ∗
          osNames (L := L) J (.except X) (DFrac.own (1 : Qp).half) hj)))
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, HA, H, Hsf, Hu⟩
      imod hA s $$ HA Hb with ⟨Hb, HL⟩
      imod walInvBody_existPin C Mr R jr r s dir nm N h Wn hin hN walN_osShN_top $$ Hb Hsi H Hsf Hu
        with ⟨Hb, H, Hsf, Hc⟩
      imodintro
      iframe Hb H Hsf
      iexists s.wal !! dir
      iframe HL
      iexact Hc)
    $$ Hinv Hnc [HA H Hsf Hu]
  iframe HA H Hsf Hu; iexact Hsi

/-- **`Exist`'s end step** (a WAL present; see the file header), at a program step. -/
theorem walInv_existEnd (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (J : Ino) (X : List GoString) (hj : NamesH) (hX : ∀ b ∈ X, walNameP b = false) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walDirKey (W := W) dir J X -∗
      walLockedTok (W := W) -∗ (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) -∗
      walOutFrag (W := W) (WalOut.empty.addClaim (J, .except X)) -∗
      osNames (L := L) J (.except X) (DFrac.own (1 : Qp).half) hj ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv #Hsi Hnc #Hk Hl Htf Ho HJ
  iapply walInv_step C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walDirKey (W := W) dir J X ∗ walLockedTok (W := W) ∗
      (walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) ∗
      walOutFrag (W := W) (WalOut.empty.addClaim (J, .except X)) ∗
      osNames (L := L) J (.except X) (DFrac.own (1 : Qp).half) hj)
    iprop(walUnlockedTok (W := W))
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, #Hk, Hl, Htf, Ho, HJ⟩
      iapply walInvBody_existUnpin C Mr R jr r s dir J X hj hX walN_osShN_top $$ Hb Hsi Hk Hl Htf Ho HJ)
    $$ Hinv Hnc [Hl Htf Ho HJ]
  iframe Hl Htf Ho HJ
  isplitl []
  · iexact Hsi
  iexact Hk

end iris

end WalFs
end EtcdGrove
end Perennial

end
