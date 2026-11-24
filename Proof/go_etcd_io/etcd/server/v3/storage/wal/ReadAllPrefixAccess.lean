/- Open the WAL invariant around the reservation or return of one closed
segment. The file probe runs with the invariant closed. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllRegCommit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllGive
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPrefixPin
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllPrefixDecode
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenUnpin

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove.WalFs
open Iris Iris.BI Iris.ProofMode Fs WalEnc
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- A directory claim identifies the current layout both before opening a
prefix file and after its deferred close. The caller retains the tail
registration and can change the outstanding file reservation inside the view. -/
theorem walInvBody_probe (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH)
    (T : GMap GoString GName) (Lk : GMap GoString Nat) (P Q : IProp GF)
    (useView : ∀ (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
      (d : WalDur) (lay : WalLay), Ls !! dir = some lay → WalAbsD C Mr d lay hj0.cur →
      SegsNamed lay.segs hj0.cur → ((segsAll Ls).map (·.ino)).Nodup →
      (lay.segs.map (·.ino)).Nodup → TailsOnly T Ls F →
      ⊢ walParked (L := L) (W := W) Ls cl F -∗ laysResF (L := L) F Ls -∗ P ==∗
        walParked (L := L) (W := W) Ls cl F ∗ laysResF (L := L) F Ls ∗ Q) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) T Lk -∗ P ==∗ walInvBody (L := L) (W := W) C Mr R jr r s ∗
        osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗ walTailsFrag (W := W) T Lk ∗ Q := by
  iintro Hb #Hk Hn Hf HP
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hk with %hK
  obtain ⟨lay, hj, hl, hlj, -, hXw, hOnce, -, hOther⟩ := Hdko.1 dir j X hK
  obtain ⟨d, hd⟩ : ∃ d, s.wal !! dir = some d := by
    cases h : s.wal !! dir with
    | none => rw [HW.2.1 dir h] at hl; cases hl
    | some d => exact ⟨d, rfl⟩
  obtain ⟨lay1, nm, hj', hl1, -, -, -, hWDC, habs, -⟩ := HW.1 dir d hd
  rw [hl] at hl1; cases hl1
  have hjj : hj' = hj := by
    obtain ⟨X', hX', hmem, -⟩ := hWDC
    by_cases hc : (lay.j, NameSet.except X', hj') = (j, NameSet.except X, hj)
    · simp only [Prod.mk.injEq] at hc; exact hc.2.2
    · exact absurd (exceptMem_dotWal hX') (hOther _ hmem hc hlj go!".wal" walNameP_dotWal)
  subst hjj
  obtain ⟨l1, l2, hcl, -, -⟩ := hOnce
  icases osClaims_agree (L := L) cl (j, NameSet.except X, hj') (by rw [hcl]; simp) hj0 $$ [Hcl Hn] with
    ⟨%h0, Hcl, Hn⟩
  · iframe Hcl Hn
  simp only at h0
  subst h0
  have hsn : SegsNamed lay.segs hj0.cur := (HNm dir lay hl).1 hj0 hWDC
  have hnd : (lay.segs.map (·.ino)).Nodup := segsAll_nodup_segs HW.2.2.1 hl
  icases walTailsRes_only (W := W) C Mr s Ls F T $$ Htl Hf with ⟨%ht, Htl, Hf⟩
  imod useView Ls cl F d lay hl habs hsn HW.2.2.1 hnd ht $$ Hpk Hlays HP with ⟨Hpk, Hlays, HQ⟩
  imodintro; iframe Hn Hf HQ
  iexists Ls, cl, n, F
  iframe Hg Hcm HCR Htl Hpk Hnms Hcl Hlays
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact HW
  isplitr
  · ipureintro; exact HWC
  isplitr
  · ipureintro; exact Hab
  isplitr
  · ipureintro; exact HNm
  isplitl [Hdk Hcp]
  · iexists K, cp; iframe Hdk Hcp; ipureintro; exact Hdko
  isplitr
  · ipureintro; exact HAt
  ipureintro; exact Hbd

/-- The segment being probed is present, outside the selected suffix and
distinct from the only file on which a tail operation can be in flight. -/
private theorem probe_layout {M : WalMarshal} {d : WalDur} {lay : WalLay} {hj : NamesH}
    {gs : List SegG} {k i : Nat} {name : GoString}
    (hab : WalAbsD walCodec M d lay hj.cur) (hsn : SegsNamed lay.segs hj.cur)
    (hnd : (lay.segs.map (·.ino)).Nodup) (hi : i < k) (hk : k < (walNames hj.cur).length)
    (hg : (walNames hj.cur)[i]? = some name) (hdrop : (walNames hj.cur).drop k = gs.map (·.name))
    (hnm : ∀ g ∈ gs, hj.cur !! g.name = some (.file g.ino)) :
    ∃ g sel, lay.segs[i]? = some g ∧ lay.segs[k]? = some sel ∧ g.name = name ∧
      (walNames hj.cur)[k]? = some sel.name ∧ hj.cur !! name = some (.file g.ino) ∧
      g.ino ∉ gs.map (·.ino) ∧
      (∀ last, lay.segs.getLast? = some last → last.ino ≠ g.ino) := by
  have hnames := walNames_segs hsn hab.names.1 hnd hab.names.2
  have hs : k < lay.segs.length := by simpa [hnames] using hk
  have hi' : i < lay.segs.length := by omega
  let g := lay.segs[i]
  let sel := lay.segs[k]
  have hg' : lay.segs[i]? = some g := List.getElem?_eq_getElem hi'
  have hs' : lay.segs[k]? = some sel := List.getElem?_eq_getElem hs
  have hname : g.name = name := by simpa [hnames, List.getElem?_map, hg'] using hg
  have he : (lay.segs.drop k).map (·.name) = gs.map (·.name) := by
    rw [List.map_drop, ← hnames]; exact hdrop
  have hn := prefix_ino_not_selected lay.segs k i g hnd hi hg'
  refine ⟨g, sel, hg', hs', hname, by simp [hnames, List.getElem?_map, hs'], ?_, ?_, ?_⟩
  · rw [← hname]; exact (hsn.1 g (List.mem_of_getElem? hg')).2
  · rw [segs_drop_inos he hsn hnm]; exact hn
  · intro last hl eq
    apply hn
    rw [← eq]
    exact List.mem_map_of_mem (List.mem_of_getLast? (by rw [List.getLast?_drop, if_neg (by omega)]; exact hl))

private theorem probe_idle {Ls : GMap GoString WalLay} {F : GMap Ino SegFl} {dir : GoString}
    {γ : GName} {lay : WalLay} {g : SegG} (hl : Ls !! dir = some lay)
    (h : TailsOnly (<[dir := γ]> (∅ : GMap GoString GName)) Ls F)
    (hne : ∀ last, lay.segs.getLast? = some last → last.ino ≠ g.ino) : F !! g.ino = none := by
  apply Classical.byContradiction
  intro hf
  obtain ⟨dir', γ', lay', last, hT, hl', hg', he⟩ := h g.ino hf
  have hd : dir = dir' := by
    by_cases hh : dir = dir'
    · exact hh
    · rw [GMap.lookup_insert_ne _ _ hh] at hT; cases hT
  subst hd
  rw [hl] at hl'
  cases hl'
  exact hne last hg' he

/-- Reserve the actual bytes for a single iteration of snapshotPrefix. -/
theorem walInvBody_takeProbe (M : WalMarshal) (U : WalUnmarshal) (hU : U.Ok M)
    (R : Roots) (jr : Ino) (r : GoString) (s : AbsDiskState) (dir : GoString)
    (j : Ino) (X : List GoString) (hj : NamesH) (T : GMap GoString GName) (Lk : GMap GoString Nat)
    (gs : List SegG) (o : WalOut) (k i : Nat) (name : GoString) (index : w64)
    (ho : o.O = gs.map (·.ino)) (hi : i < k) (hk : k < (walNames hj.cur).length)
    (hn : (walNames hj.cur)[i]? = some name) (hdrop : (walNames hj.cur).drop k = gs.map (·.name))
    (hnm : ∀ g ∈ gs, hj.cur !! g.name = some (.file g.ino))
    (hhead : ∀ nm, (walNames hj.cur)[k]? = some nm → ∀ sq ix,
      nm = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat index) :
    ⊢ walInvBody (L := L) (W := W) walCodec M R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗ walTailsFrag (W := W) T Lk -∗
      walOutFrag (W := W) o ==∗ walInvBody (L := L) (W := W) walCodec M R jr r s ∗
        osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj ∗ walTailsFrag (W := W) T Lk ∗
        ∃ g : SegG, ⌜g.name = name ∧ hj.cur !! name = some (.file g.ino) ∧ g.om.size = g.bs.length ∧
          NameOk g.name ∧ g.name.length ≤ 255 ∧ walNameP g.name = true ∧
          ProbeBelow walCodec U (uint.nat index) [segImg g] 0 0#32⌝ ∗
          walOutFrag (W := W) (o.addSeg g.ino) ∗ segRes (L := L) g := by
  apply walInvBody_probe
  intro Ls cl F d lay hl hab hsn hnd hnd' _
  obtain ⟨g, sel, hg, hs, he, hsel, hcur, hno, _⟩ := probe_layout hab hsn hnd' hi hk hn hdrop hnm
  have hm := List.mem_of_getElem? hg
  obtain ⟨sq, ix, hname, _, _⟩ := hab.nameBound i g hg
  iintro Hp Hl Ho
  imod readAll_takeProbe Ls cl F o g (mem_segsAll hl hm) (by rw [ho]; exact hno) $$ Hp Hl Ho
    with ⟨Hp, Hl, Ho, Hg, -⟩
  imodintro; iframe Hp Hl; iexists g; iframe Ho Hg
  ipureintro
  exact ⟨he, hcur, (hab.metas g hm).1, hname ▸ walFileName_nameOk sq ix,
    by rw [hname, walFileName_length]; decide, (hsn.1 g hm).1,
    readAll_probe_before_selected walCodec_ok hU hab hi hg hs (hhead sel.name hsel)⟩


/-- The only inode on which a change can be in flight is the registered tail.
The directory agreement and the file's metadata recover the current layout's
parked resource after the read-only probe. -/
theorem walInvBody_putProbe (M : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH)
    (γ : GName) (Lk : GMap GoString Nat) (gs : List SegG) (o : WalOut) (k i : Nat)
    (name : GoString) (prev : SegG) (ho : o.O = gs.map (·.ino)) (hi : i < k)
    (hk : k < (walNames hj.cur).length) (hn : (walNames hj.cur)[i]? = some name)
    (hdrop : (walNames hj.cur).drop k = gs.map (·.name))
    (hnm : ∀ g ∈ gs, hj.cur !! g.name = some (.file g.ino))
    (hino : hj.cur !! name = some (.file prev.ino)) (hsize : prev.om.size = prev.bs.length) :
    ⊢ walInvBody (L := L) (W := W) walCodec M R jr r s -∗ walDirKey (W := W) dir j X -∗
      osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walTailsFrag (W := W) (<[dir := γ]> ∅) Lk -∗
      (walOutFrag (W := W) (o.addSeg prev.ino) ∗ segRes (L := L) prev) ==∗
        walInvBody (L := L) (W := W) walCodec M R jr r s ∗
        osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj ∗
        walTailsFrag (W := W) (<[dir := γ]> ∅) Lk ∗ walOutFrag (W := W) o := by
  apply walInvBody_probe
  intro Ls cl F d lay hl hab hsn hnd hnd' hT
  obtain ⟨g, _, hg, _, _, _, hcur, hno, hlast⟩ := probe_layout hab hsn hnd' hi hk hn hdrop hnm
  rw [hino] at hcur
  have he : g.ino = prev.ino := by injection hcur with h; injection h with h; exact h.symm
  have hm := List.mem_of_getElem? hg
  have hf := probe_idle hl hT hlast
  have hidle : segResF (L := L) F g = segRes (L := L) g := by simp [segResF, hf]
  iintro Hp Hl ⟨Ho, Hprev⟩
  iunfold laysResF at Hl
  icases BigSepL.bigSepL_mem_acc (Φ := fun x => segResF (L := L) F x) (mem_segsAll hl hm) $$ Hl
    with ⟨Hi, Hback⟩
  ihave Hi : segRes (L := L) g $$ [Hi]
  · rw [← hidle]; iexact Hi
  iunfold segRes at Hprev
  icases Hprev with ⟨Hm, Hb⟩
  icases segRes_meta (L := L) g prev.ino (DFrac.own (1 : Qp).half) prev.om $$ [Hi Hm] with
    ⟨%hmeta, Hi, Hm⟩
  · iframe Hi Hm
  ihave Hprev : segResP (L := L) g $$ [Hm Hb]
  · iapply segResP_congr prev g he ((hab.metas g hm).1.symm.trans ((congrArg OsMeta.size (hmeta he)).trans hsize))
    iapply segRes_segResP; unfold segRes; iframe Hm Hb
  ihave Ho : walOutFrag (W := W) (o.addSeg g.ino) $$ [Ho]
  · rw [he]; iexact Ho
  imod walParked_putSeg (L := L) (W := W) Ls cl F _ g (mem_segsAll hl hm) hnd hf $$ Hp Ho Hprev
    with ⟨Hp, Ho⟩
  imodintro; iframe Hp
  isplitl [Hi Hback]
  · unfold laysResF; iapply Hback; rw [hidle]; iexact Hi
  iapply walOutFrag_eq' (W := W) o $$ Ho
  ipureintro
  have hnot : g.ino ∉ o.O := ho ▸ hno
  cases o with
  | mk O D T =>
    simp only [WalOut.addSeg, WalOut.delSeg, List.filter_cons, ne_eq, not_true_eq_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, WalOut.mk.injEq, and_self, and_true]
    apply List.filter_eq_self.2
    intro x hx; simp only [decide_eq_true_eq]; exact fun e => hnot (e ▸ hx)

end Perennial.EtcdGrove.WalFs
