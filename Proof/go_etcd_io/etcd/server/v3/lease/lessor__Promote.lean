/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Promote.lean` (prove-ps2-promote, 2026-11-21;
a names-only trust-boundary axiom until then: float arithmetic, a float-to-integer conversion and
`sort.Sort` over `Remaining()`). Under the write lock (the guard): a fresh `demotec`, a close-once
channel (its invariant and token allocated at the `make`), swapped into the lessor's `demotec`
invariant (`promote_swap`: the old channel's token, if any, dropped); every lease of the map
refreshed, registered with the expiry notifier (a fresh item) and its checkpoint scheduled
(`leaseMeta`); then, with `leaseRevokeRate` or more leases, `unsafeLeases`, the sort of
`leasesByExpiry` (`sorter_byExpiry`, with the level-0 token), and a pass over the sorted leases:
`Remaining()` of each (the token again), and for each lease past the window's target the float
arithmetic (Perennial's uninterpreted `FloatOps`) and the float-to-`Duration` conversion (any
value), and the same refresh, registration and scheduling, through the lease's `leaseMeta` in the
lock's map (each lease of the slice is in the map).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Promote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__unsafeLeases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Remaining
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__refresh
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__RegisterOrUpdate
public import Proof.go_etcd_io.etcd.server.v3.lease.SortByExpiry
public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The new `demotec` `c` swapped into the lessor's `demotec` invariant** (`Promote`, under the
write lock, with the lock's half of its ghost variable `γd`): the variable set to `c` (both
halves), `c`'s close token put in; the old channel's token, if any, dropped (that channel is never
closed: two `Promote`s with no `Demote` between them). -/
theorem promote_swap (γd γt : GName) (dc c : GoChan) :
    £ 1 ∗ ghostVar (GF := GF) γd (1 : Qp).half dc ∗ inv demoteOuterN (demoteOuter γd) ∗
      onceRecv c γt ∗ token γt ⊢ |={⊤}=> ghostVar γd (1 : Qp).half c := by
  iintro ⟨Hlc, Hv, #Hout, #Hrecv, Htok⟩
  iinv Hout with Ho Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑demoteOuterN) $$ Hlc Ho with Ho
  iunfold demoteOuter at Ho
  icases Ho with ⟨%dc', Hv', -⟩
  imod ghostVar_update_halves c _ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Htok] with -
  · inext; iunfold demoteOuter; iexists c; iframe Hv'; iright; iexists γt; iframe Hrecv Htok
  imodintro
  iexact Hv

theorem lease.lessor.Promote.wp_proof
    (hUL : lease.lessor.unsafeLeases.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».anyLessSpec (GF := GF) (hG := hG))
    (hLen : lease.leasesByExpiry.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.leasesByExpiry.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.leasesByExpiry.Swap.spec (GF := GF) (hG := hG))
    (hRem : lease.Lease.Remaining.spec (GF := GF) (hG := hG))
    (hRefresh : lease.Lease.refresh.spec (GF := GF) (hG := hG))
    (hReg : lease.LeaseExpiredNotifier.RegisterOrUpdate.spec (GF := GF) (hG := hG))
    (hSched : lease.lessor.scheduleCheckpointIfNeeded.spec (GF := GF) (hG := hG)) :
    lease.lessor.Promote.spec (GF := GF) (hG := hG) := by
  intro lp γl d
  wp_start as ⟨#Hinv, #Hcfg, Htt, %Hb, %Hrb⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx, Hhist⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt, #Hstr⟩
  imod (notif_wopen lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot] with ⟨Hnp, Hnot, Hntk⟩
  (try wp_auto)
  -- the fresh `demotec`: a close-once channel, swapped into the lessor's invariant
  wp_apply +noauto chan.wp_make1 (V := Unit) as %c %γc ⟨#Hch, -, Hown⟩
  imod (token_alloc (GF := GF)) with ⟨%γt, Htok⟩
  imod (inv_alloc onceChanN ⊤ (onceChanInv γc γt)) $$ [Hown] with #Hci
  · inext; iunfold onceChanInv; iexists .Idle; dsimp only; iframe Hown
  ihave #Hrecv : onceRecv (GF := GF) c γt $$ []
  · iunfold onceRecv; iexists γc; iframe Hch Hci
  iunfold demoteTie at Hdt
  icases Hdt with ⟨%γr, #Hpr, Hgv, #Hout⟩
  wp_auto_lc 1
  iapply fupd_wp
  imod promote_swap γr.2.2.2.2.2.2.1 γt dc c $$ [$Hlc1 $Hgv $Hout $Hrecv $Htok] with Hgv
  imodintro
  (try wp_auto)
  ipersist le
  ipersist extend
  -- every lease refreshed, registered with the notifier, its checkpoint scheduled
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (_keys : List w64) (_p : Int) =>
      iprop(∃ x : Loc, "l" ∷ l_ptr ↦ x ∗
        "Hmeta" ∷ ([∗map] id ↦ l ∈ M, leaseMeta (GF := GF) id l 1) ∗
        "Hnp" ∷ lF go!"leaseExpiredNotifier" lp ↦ np ∗ "Hnot" ∷ notifierAt np 1 ∗
        "Hcp" ∷ lF go!"cp" lp ↦ func.nil ∗
        "Hh" ∷ (∃ (h' : GoSlice) (hx' : List (Loc × w64)), lF go!"leaseCheckpointHeap" lp ↦ h' ∗
          queueAt h' hx' 1))) $$ HM
  iintro %keys -
  isplitl [l Hmeta Hnp Hnot Hcp Hh Hhq]
  · iexists _; iframe; iexists h, hx; iframe
  isplitr
  · imodintro
    iintro %p %k %o ⟨-, %Ho⟩ HP
    iNamed HP
    icases Hh with ⟨%h1, %hx1, Hh, Hhq⟩
    wp_auto
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x 1) Ho).1 $$ Hmeta
      with ⟨Hml, Hmeta⟩
    iunfold leaseMeta at Hml
    icases Hml with ⟨#HID, ⟨%t, #Httl⟩, #Hrc, ⟨%r, Hrem⟩, ⟨%e, Hexp⟩, #HexG⟩
    wp_apply (hRefresh o d r t (DFrac.own 1) DFrac.discard e) $$
      [$Hpkg $Hrem $Httl $Hexp $HexG] as ⟨Hrem, -, %e', Hexp⟩
    (try wp_auto)
    iStructNamed «$r0»
    ipersist id
    iunfold notifierAt at Hnot
    icases Hnot with ⟨%Mn, Hnot⟩
    wp_apply (hReg np «$r0_ptr» _ (W64 0) Mn) $$ [$Hpkg $Hnot id time index] as Hnot
    · ileft; iunfold lwtAt; iframe; iframe #
    (try wp_auto)
    wp_apply (hSched lp o func.nil h1 hx1 k r t (DFrac.own 1) (DFrac.own 1) DFrac.discard) $$
      [$Hpkg $Hcfg $Hcp $Hh $Hhq $HID $Hrem $Httl] as ⟨Hcp, Hh, Hrem, -⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists o
    iframe
    iapply Hmeta
    iunfold leaseMeta
    iframe HID Hrc HexG
    isplitr
    · iexists t; iexact Httl
    isplitl [Hrem]
    · iexists r; iexact Hrem
    iexists e'; iexact Hexp
  iintro HP HM
  iNamed HP
  icases Hh with ⟨%h1, %hx1, Hh, Hhq⟩
  wp_auto
  ihave #Hcfg' := Hcfg
  iunfold lessorCfg at Hcfg'
  icases Hcfg' with ⟨%mt, %cpp, %cl, %ci, %lg, %rr, -, -, -, -, -, -, -, #Hrr, %Hrr0⟩
  wp_apply (wp_map_len_lt lm M (DFrac.own 1)) $$ [$HM] as ⟨HM, %Hmlt⟩
  (try wp_auto)
  by_cases hlt : sint.Z (W64 (GMap.size M)) < sint.Z rr
  · -- fewer leases than the revoke rate: no pile-up, return
    simp only [hlt, decide_true]
    (try wp_auto)
    imod (notif_wclose lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot $Hntk] with ⟨Hnp, Hnot⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
        Hmeta Hbl Hgv Hhist]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iunfold lessorExtra
      iexists c, np, h1, hx1, bl
      iframe
      iframe Hstr
      iunfold demoteTie
      iexists γr
      iframe Hpr Hout Hgv
    (try wp_auto)
    iapply HΦ $$ Htt
  simp only [hlt, decide_false]
  (try wp_auto)
  -- the leases, sorted by their remaining time
  ihave %Hszlt := preceipt_lt _ $$ Hsz
  wp_apply (hUL lp lm M 1) $$ [$Hpkg $Hlm $HM] as %sl %ls ⟨Hlm, HM, Hsl, %Hls0⟩
  obtain ⟨Hnd, Hpairs⟩ := Hls0
  have Hlen : ls.length = GMap.size M := by
    rw [GMap.size_eq_length M (ls.map Prod.snd) Hnd, List.length_map]
    intro k
    constructor
    · intro hk
      obtain ⟨⟨l, k'⟩, hmem, rfl⟩ := List.mem_map.1 hk
      rw [(Hpairs k' l).1 hmem]; rfl
    · intro hk
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hk
      exact List.mem_map.2 ⟨(l, k), (Hpairs k l).2 hl, rfl⟩
  ihave #Hobjs : [∗list] x ∈ ls, isLeaseObj (GF := GF) γl x.1 $$ [Hls]
  · iapply (lease.bigSepM_pairs (P := fun _ l => isLeaseObj (GF := GF) γl l) M ls Hpairs)
    iexact Hls
  (try wp_auto)
  ihave #Hpsort : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #HobjsF : [∗list] p ∈ ls.map Prod.fst, isLeaseObj (GF := GF) γl p $$ [Hobjs]
  · rw [BigSepL.bigSepL_map]; iexact Hobjs
  ihave #Hsorter := lease.sorter_byExpiry hLen hLess hSwap γl sl ls Hb $$ [$Hpkg $HobjsF]
  wp_apply (hSort (Loc × w64) _ (lease.sorterR sl ls) ls) $$ [Hsl Htt] as %ls' HR
  · iframe #
    unfold lease.sorterR
    iframe
    ipureintro
    refine ⟨List.Perm.refl ls, ?_⟩
    omega
  unfold lease.sorterR
  icases HR with ⟨⟨Hsl, Htt, %Hp⟩, %Hp'⟩
  have Hlen' : ls'.length = GMap.size M := by rw [← Hlen]; exact Hp.length_eq
  ihave #Hobjs' : [∗list] x ∈ ls', isLeaseObj (GF := GF) γl x.1 $$ [Hobjs]
  · iapply (BigSepL.bigSepL_perm (PROP := IProp GF) (Φ := fun (x : Loc × w64) => isLeaseObj (GF := GF) γl x.1)
      Hp.symm).1
    iexact Hobjs
  have Hpairs' : ∀ (id : w64) (l : Loc), (l, id) ∈ ls' ↔ M.lookup id = some l := fun id l =>
    Hp.mem_iff.trans (Hpairs id l)
  (try wp_auto)
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen'] at Hsll
  have Hsz1 : 0 < GMap.size M := by
    have h1 : sint.Z (W64 (GMap.size M)) = GMap.size M := by word
    omega
  obtain ⟨a0, Ha0⟩ : ∃ a0, ls'[0]? = some a0 :=
    ⟨_, List.getElem?_eq_getElem (by omega : 0 < ls'.length)⟩
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by word
  simp only [Hb0, and_self, ↓reduceIte]
  wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) (ls'.map Prod.fst) (DFrac.own 1) a0.1 (by word))
    $$ [$Hsl] as Hsl
  · ipureintro; rw [List.getElem?_map]; show (ls'[0]?).map _ = _; rw [Ha0]; rfl
  ihave #Ho0 := BigSepL.bigSepL_lookup Ha0 $$ Hobjs'
  wp_apply (hRem γl a0.1) $$ [$Hpkg $Ho0 $Htt] as %rem0 Htt
  · ipureintro; exact Hb
  (try wp_auto)
  ipersist targetExpiresPerSecond
  -- the pass over the sorted leases
  ihave IH : iprop(∃ (n : w64) (bw nw : _root_.Perennial.time.Duration) (ex : w64) (lv : Loc),
      "i" ∷ i_ptr ↦ n ∗ "baseWindow" ∷ baseWindow_ptr ↦ bw ∗ "nextWindow" ∷ nextWindow_ptr ↦ nw ∗
      "expires" ∷ expires_ptr ↦ ex ∗ "l" ∷ l_ptr ↦ lv ∗
      "Hh" ∷ (∃ (h' : GoSlice) (hx' : List (Loc × w64)), lF go!"leaseCheckpointHeap" lp ↦ h' ∗
        queueAt h' hx' 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i baseWindow nextWindow expires l Hh Hhq]
  · iexists W64 0, _, _, _, _
    iframe
    isplitl
    · iexists h1, hx1; iframe
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · -- the lease at `n`
    have Hlt : sint.nat n < ls'.length := by word
    obtain ⟨a, Ha⟩ : ∃ a, ls'[sint.nat n]? = some a := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index sl (sint.Z n) (ls'.map Prod.fst) (DFrac.own 1) a.1 Hn) $$ [$Hsl] as Hsl
    · ipureintro; rw [List.getElem?_map]; show (ls'[sint.nat n]?).map _ = _; rw [Ha]; rfl
    ihave #Hoa := BigSepL.bigSepL_lookup Ha $$ Hobjs'
    (try wp_auto)
    wp_apply (hRem γl a.1) $$ [$Hpkg $Hoa $Htt] as %rem Htt
    · ipureintro; exact Hb
    (try wp_auto)
    wp_if_destruct
    · -- past the window: a new window from this lease
      wp_for_post
      iframe
      iexists n + W64 1, rem, rem + W64 1000000000, W64 1, a.1
      iframe
      ipureintro; word
    wp_if_destruct
    · -- within the window's target
      wp_for_post
      iframe
      iexists n + W64 1, bw, nw, ex + W64 1, a.1
      iframe
      ipureintro; word
    (try wp_auto)
    -- piled up: `delay` (IEEE 754 float steps), a float converted to a `Duration` (any value),
    -- then the same refresh
    wp_apply wp_float64_div as %_ -
    (try wp_auto)
    wp_apply wp_float64_mul as %_ -
    (try wp_auto)
    wp_apply wp_float64_sub as %_ -
    (try wp_auto)
    wp_apply wp_ArbitraryInt as %x -
    (try wp_auto)
    have hM : M.lookup a.2 = some a.1 := (Hpairs' a.2 a.1).1 (List.mem_of_getElem? Ha)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x 1) hM).1 $$ Hmeta
      with ⟨Hml, Hmeta⟩
    iunfold leaseMeta at Hml
    icases Hml with ⟨#HID, ⟨%t, #Httl⟩, #Hrc, ⟨%r, Hrem⟩, ⟨%e, Hexp⟩, #HexG⟩
    icases Hh with ⟨%h2, %hx2, Hh, Hhq⟩
    wp_apply (hRefresh a.1 _ r t (DFrac.own 1) DFrac.discard e) $$
      [$Hpkg $Hrem $Httl $Hexp $HexG] as ⟨Hrem, -, %e', Hexp⟩
    (try wp_auto)
    iStructNamed «$r0»
    ipersist id
    iunfold notifierAt at Hnot
    icases Hnot with ⟨%Mn, Hnot⟩
    wp_apply (hReg np «$r0_ptr» _ (W64 0) Mn) $$ [$Hpkg $Hnot id time index] as Hnot
    · ileft; iunfold lwtAt; iframe; iframe #
    (try wp_auto)
    wp_apply (hSched lp a.1 func.nil h2 hx2 a.2 r t (DFrac.own 1) (DFrac.own 1) DFrac.discard) $$
      [$Hpkg $Hcfg $Hcp $Hh $Hhq $HID $Hrem $Httl] as ⟨Hcp, Hh, Hrem, -⟩
    (try wp_auto)
    ihave Hmeta := Hmeta $$ [Hrem Hexp]
    · iunfold leaseMeta
      iframe HID Hrc HexG
      isplitr
      · iexists t; iexact Httl
      isplitl [Hrem]
      · iexists r; iexact Hrem
      iexists e'; iexact Hexp
    wp_for_post
    iframe
    iexists n + W64 1, bw, _, ex + W64 1, a.1
    iframe
    ipureintro; word
  · -- the pass done: unlock (deferred) and return
    (try wp_auto)
    icases Hh with ⟨%h2, %hx2, Hh, Hhq⟩
    imod (notif_wclose lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot $Hntk] with ⟨Hnp, Hnot⟩
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
        Hmeta Hbl Hgv Hhist]
    · iframe #
      inext
      iunfold lessorMu
      iexists lm, im, M, I, rd0, L
      iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      iunfold lessorExtra
      iexists c, np, h2, hx2, bl
      iframe
      iframe Hstr
      iunfold demoteTie
      iexists γr
      iframe Hpr Hout Hgv
    (try wp_auto)
    iapply HΦ $$ Htt

end proof

end EtcdGrove
end Perennial
