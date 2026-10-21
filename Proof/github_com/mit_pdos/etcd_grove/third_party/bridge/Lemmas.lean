/-
**The bridge's ghost-state lemmas** (`Defs.lean`'s protocol): a registered connection is not a fresh
allocation; a share of `b.blackholec` handed out at a registration and given back at a removal.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A location owned whole is not also persistently pointed to (a local workaround: Perennial has
no validity lemma for typed points-to; `Loc`'s is a heap points-to). -/
theorem loc_own_discard (l v w : Loc) : (l ↦ v : IProp GF) ∗ l ↦□ w ⊢ False := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Heq
  subst Heq
  ihave H := ((typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own 1)
    DFrac.discard).2 $$ [H1 H2]
  · iframe
  ihave H := typedPointsto_split $$ H
  rw [typedPointstoDef_heap] at *
  ihave %Hv := heapPointsto_valid $$ H
  exfalso
  have := DFrac.valid_own_op_discard.1 Hv
  simp at this

/-- The shares of a map with a new entry. -/
theorem sharesPts_insert (b : Loc) (ch : GoChan) (shares : GMap Loc (Qp × GName)) (c : Loc)
    (x : Qp × GName) (h : shares.lookup c = none) :
    sharesPts (GF := GF) b ch (shares.insert c x) ⊣⊢
      bF b go!"blackholec" ↦{DFrac.own x.1} ch ∗ sharesPts b ch shares := by
  unfold sharesPts
  exact BigSepM.bigSepM_insert h

/-- The shares of a map without one of its entries. -/
theorem sharesPts_delete (b : Loc) (ch : GoChan) (shares : GMap Loc (Qp × GName)) (c : Loc)
    (x : Qp × GName) (h : shares.lookup c = some x) :
    sharesPts (GF := GF) b ch shares ⊣⊢
      bF b go!"blackholec" ↦{DFrac.own x.1} ch ∗ sharesPts b ch (shares.delete c) := by
  unfold sharesPts
  exact BigSepM.bigSepM_delete h

/-- **Handing out a share** at a registration: the lock's fraction `q` in halves, one for the new
entry `c ↦ (q/2, γt)`. -/
theorem share_out (b : Loc) (ch : GoChan) (shares : GMap Loc (Qp × GName)) (q : Qp) (c : Loc)
    (γt : GName) (h : shares.lookup c = none) :
    bF b go!"blackholec" ↦{DFrac.own q} ch ∗
      (bF b go!"blackholec" ↦{DFrac.own q} ch ∗ sharesPts b ch shares -∗
        bF b go!"blackholec" ↦ ch) ⊢
    bF b go!"blackholec" ↦{DFrac.own q.half} ch ∗
      (bF b go!"blackholec" ↦{DFrac.own q.half} ch ∗ sharesPts b ch (shares.insert c (q.half, γt)) -∗
        bF b go!"blackholec" ↦ ch) ∗
      (bF b go!"blackholec" ↦{DFrac.own q.half} ch : IProp GF) := by
  have e := typedPointsto_frac_add (GF := GF) (bF b go!"blackholec") ch q.half q.half
  rw [Qp.half_add_half] at e
  iintro ⟨Hq, Hw⟩
  icases e.1 $$ Hq with ⟨Hq1, Hq2⟩
  iframe Hq1 Hq2
  iintro ⟨Hh, Hsh⟩
  icases (sharesPts_insert b ch shares c (q.half, γt) h).1 $$ Hsh with ⟨He, Hsh⟩
  iapply Hw
  iframe Hsh
  iapply e.2
  iframe

/-- **Taking a share back** at a removal of the entry `c ↦ x`: the lock's fraction grows by it. -/
theorem share_in (b : Loc) (ch : GoChan) (shares : GMap Loc (Qp × GName)) (q : Qp) (c : Loc)
    (x : Qp × GName) (h : shares.lookup c = some x) :
    bF b go!"blackholec" ↦{DFrac.own q} ch ∗
      (bF b go!"blackholec" ↦{DFrac.own q} ch ∗ sharesPts b ch shares -∗
        bF b go!"blackholec" ↦ ch) ∗
      bF b go!"blackholec" ↦{DFrac.own x.1} ch ⊢
    bF b go!"blackholec" ↦{DFrac.own (q + x.1)} ch ∗
      (bF b go!"blackholec" ↦{DFrac.own (q + x.1)} ch ∗ sharesPts b ch (shares.delete c) -∗
        (bF b go!"blackholec" ↦ ch : IProp GF)) := by
  have e := typedPointsto_frac_add (GF := GF) (bF b go!"blackholec") ch q x.1
  iintro ⟨Hq, Hw, Hx⟩
  isplitl [Hq Hx]
  · iapply e.2
    iframe
  iintro ⟨Hqx, Hsh⟩
  icases e.1 $$ Hqx with ⟨Hq, Hx⟩
  iapply Hw
  iframe Hq
  iapply (sharesPts_delete b ch shares c x h).2
  iframe

/-- **The field whole**, once no share is out. -/
theorem share_all (b : Loc) (ch : GoChan) (q : Qp) :
    bF b go!"blackholec" ↦{DFrac.own q} ch ∗
      (bF b go!"blackholec" ↦{DFrac.own q} ch ∗ sharesPts b ch ∅ -∗
        bF b go!"blackholec" ↦ ch) ⊢
    (bF b go!"blackholec" ↦ ch : IProp GF) := by
  iintro ⟨Hq, Hw⟩
  iapply Hw
  iframe Hq
  unfold sharesPts
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- The closer's view of a broadcast channel, and anyone's. -/
theorem ownBroadcastChan_Pending_Unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF) :
    ownBroadcastChan ch γ Q .Pending ⊢
      ownBroadcastChan ch γ Q .Pending ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro Hp
  icases ownBroadcastChan_open _ _ _ _ $$ Hp with ⟨%γch, #Hint, Hp⟩
  isplitl [Hp]
  · iapply ownBroadcastChan_close ch γ Q .Pending γch
    iframe #; iexact Hp
  · iapply ownBroadcastChan_close ch γ Q .Unknown γch
    iframe #

/-- The `i`-th key of a list without duplicates is not among the keys before it. -/
theorem not_mem_take_of_getElem? {α : Type} (l : List α) (n : Nat) (a : α) (hnd : l.Nodup)
    (h : l[n]? = some a) : a ∉ l.take n := by
  intro hm
  obtain ⟨j, hj, hja⟩ := List.getElem_of_mem hm
  obtain ⟨hn, e2⟩ := List.getElem?_eq_some_iff.1 h
  have hj' : j < n := by simp at hj; omega
  have hjl : j < l.length := by omega
  have e1 : l[j] = a := by rw [← hja]; simp
  have := (List.Nodup.getElem_inj hnd (hi := hjl) (hj := hn)).1 (e1.trans e2.symm)
  omega

/-- **Draining the map**, under the mutex (`Unblackhole`'s and `DropConnections`'s loop): a
`for range` over the map's registered connections whose body behaves as `c.Close()` (returning
the connection's deposit, with the loop's resource `R`: its variable) gives every share back: the
shares are then none. -/
theorem wp_drain (b : Loc) (m : GoMap) (body : GoFunc) (conns : GMap Loc Unit)
    (shares : GMap Loc (Qp × GName)) (q : Qp) (bhc : GoChan) (R : IProp GF) (Φ : val → IProp GF)
    (Hdom : ∀ c, (conns !! c).isSome = (shares !! c).isSome) :
    (□ ∀ (c : Loc) (q' : Qp) (γt : GName), connOk b c q' γt -∗ R -∗
        WP (App (App (Val #body) (Val #c)) (Val #())) {{ v, ⌜v = executeVal⌝ ∗ doneQ b q' γt ∗ R }}) -∗
    R -∗ m ↦$ conns -∗
    bF b go!"blackholec" ↦{DFrac.own q} bhc -∗
    (bF b go!"blackholec" ↦{DFrac.own q} bhc ∗ sharesPts b bhc shares -∗ bF b go!"blackholec" ↦ bhc) -∗
    ([∗map] c ↦ x ∈ shares, connOk b c x.1 x.2 ∗ token x.2) -∗
    (∀ q' : Qp, R -∗ m ↦$ conns -∗ bF b go!"blackholec" ↦{DFrac.own q'} bhc -∗
      (bF b go!"blackholec" ↦{DFrac.own q'} bhc ∗ sharesPts b bhc ∅ -∗ bF b go!"blackholec" ↦ bhc) -∗
      Φ executeVal) -∗
    WP (App (App (Val (map.forRange (go.GoType.PointerType bridge.bridgeConn.ty)
      (go.GoType.StructType []))) (Val #m)) (Val #body)) {{ Φ }} := by
  iintro #Hbody HR Hm Hbh Hwand Hregs HΦ
  iapply (wp_map_for_range (V := Unit) (fun (keys : List Loc) (i : Int) => iprop(
      ∃ (q' : Qp) (sh : GMap Loc (Qp × GName)),
        ⌜0 ≤ i ∧ ∀ c, sh !! c = if c ∈ keys.take i.toNat then none else shares !! c⌝ ∗
        bF b go!"blackholec" ↦{DFrac.own q'} bhc ∗
        (bF b go!"blackholec" ↦{DFrac.own q'} bhc ∗ sharesPts b bhc sh -∗
          bF b go!"blackholec" ↦ bhc) ∗
        ([∗map] c ↦ x ∈ sh, connOk b c x.1 x.2 ∗ token x.2) ∗ R))
    body _ _ m conns (DFrac.own 1) Φ) $$ Hm
  iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
  isplitl [Hbh Hwand Hregs HR]
  · iexists q, shares
    iframe
    ipureintro
    exact ⟨by omega, fun c => by simp⟩
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hk, %Hv⟩ ⟨%q', %sh, ⟨%Hi0, %Hsh⟩, Hbh, Hwand, Hregs, HR⟩
    have hsome : (shares !! key).isSome := by rw [← Hdom, Hv]; rfl
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    have hnt : key ∉ keys.take i.toNat := not_mem_take_of_getElem? keys i.toNat key Hnd Hk
    have hshk : sh !! key = some x := by rw [Hsh, ite_eq_right_iff.mpr (fun h => absurd h hnt), hx]
    icases (BigSepM.bigSepM_delete (Φ := fun c (x : Qp × GName) =>
      iprop(connOk (GF := GF) b c x.1 x.2 ∗ token x.2)) hshk).1 $$ Hregs with ⟨⟨#Hc, Htok⟩, Hregs⟩
    iapply wp_fupd
    iapply wp_wand $$ (Hbody $$ %key %x.1 %x.2 Hc HR)
    iintro %bv ⟨%Hbv, #HQ, HR⟩
    subst Hbv
    iunfold doneQ at HQ
    iinv HQ with Hi Hclose
    imod Hi with (Ht | ⟨%ch, Hx⟩)
    · iexfalso
      iapply token_exclusive x.2 $$ Ht Htok
    imod Hclose $$ [Htok] with -
    · inext; ileft; iexact Htok
    icombine Hbh Hx gives %Heq
    subst Heq
    icases share_in b bhc sh q' key x hshk $$ [Hbh Hwand Hx] with ⟨Hbh, Hwand⟩
    · iframe
    imodintro
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists q' + x.1, sh.delete key
    isplitr
    · ipureintro
      refine ⟨by omega, fun c => ?_⟩
      have htk : (i + 1).toNat = i.toNat + 1 := by omega
      rw [htk, List.take_succ, Hk]
      by_cases hc : c = key
      · subst hc
        simp
      · rw [GMap.lookup_delete_ne _ (Ne.symm hc), Hsh]
        simp [hc]
    iframe
  · iintro ⟨%q', %sh, ⟨%Hi0, %Hsh⟩, Hbh, Hwand, Hregs, HR⟩ Hm
    have hall : keys.take (GMap.size conns : Int).toNat = keys := by
      rw [Int.toNat_natCast, ← Hsize]; exact List.take_length
    have hsh : sh = ∅ := by
      apply GMap.ext
      intro c
      rw [Hsh, hall, GMap.lookup_empty]
      by_cases hc : c ∈ keys
      · simp [hc]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hc)]
        have h1 : (conns !! c).isSome = false := by
          rcases h : (conns !! c) with _ | _
          · rfl
          · exact absurd ((Hmem c).2 (by simp [h])) hc
        rw [Hdom] at h1
        exact Option.not_isSome_iff_eq_none.mp (by simp [h1])
    subst hsh
    iapply HΦ $$ HR Hm Hbh Hwand

/-- The registered connections, persistently, from the mutex's entries. -/
theorem regs_connOk (b : Loc) (shares : GMap Loc (Qp × GName)) :
    ([∗map] c ↦ x ∈ shares, connOk b c x.1 x.2 ∗ token x.2) ⊢
      ([∗map] c ↦ x ∈ shares, connOk b c x.1 x.2 ∗ token x.2) ∗
      □ ([∗map] c ↦ x ∈ shares, connOk (GF := GF) b c x.1 x.2) := by
  rw [BigSepM.bigSepM_sep_eq (Φ := fun c (x : Qp × GName) => connOk (GF := GF) b c x.1 x.2)
    (Ψ := fun _ (x : Qp × GName) => (token x.2 : IProp GF))]
  iintro ⟨#Hc, Ht⟩
  isplitl [Ht]
  · iframe
    iexact Hc
  · imodintro
    iexact Hc

/-- **Closing every registered connection**, under the mutex (`serveListen`'s deferred loop): a
`for range` over the map whose body behaves as `c.Close()` on a registered connection (with the
loop's resource `R`). -/
theorem wp_close_all (b : Loc) (m : GoMap) (body : GoFunc) (conns : GMap Loc Unit)
    (shares : GMap Loc (Qp × GName)) (R : IProp GF) (Φ : val → IProp GF)
    (Hdom : ∀ c, (conns !! c).isSome = (shares !! c).isSome) :
    (□ ∀ (c : Loc) (q' : Qp) (γt : GName), connOk b c q' γt -∗ R -∗
        WP (App (App (Val #body) (Val #c)) (Val #())) {{ v, ⌜v = executeVal⌝ ∗ R }}) -∗
    (□ [∗map] c ↦ x ∈ shares, connOk b c x.1 x.2) -∗
    R -∗ m ↦$ conns -∗
    (R -∗ m ↦$ conns -∗ Φ executeVal) -∗
    WP (App (App (Val (map.forRange (go.GoType.PointerType bridge.bridgeConn.ty)
      (go.GoType.StructType []))) (Val #m)) (Val #body)) {{ Φ }} := by
  iintro #Hbody #Hcs HR Hm HΦ
  iapply (wp_map_for_range (V := Unit) (fun (_ : List Loc) (_ : Int) => R)
    body _ _ m conns (DFrac.own 1) Φ) $$ Hm
  iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
  isplitl [HR]
  · iexact HR
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hk, %Hv⟩ HR
    have hsome : (shares !! key).isSome := by rw [← Hdom, Hv]; rfl
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    ihave #Hc := BigSepM.bigSepM_lookup (Φ := fun c (x : Qp × GName) =>
      iprop(connOk (GF := GF) b c x.1 x.2)) hx $$ Hcs
    iapply wp_wand $$ (Hbody $$ %key %x.1 %x.2 Hc HR)
    iintro %bv ⟨%Hbv, HR⟩
    subst Hbv
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexact HR
  · iintro HR Hm
    iapply HΦ $$ HR Hm

section wg
variable [package_sem : sync.Assumptions]

/-- **`b.wg.Add(1)` for a `serveConn`**, by `serveListen` (running: its half of the flag),
depositing its thread token: a receipt. -/
theorem wp_bridgeWg_Add (b : Loc) (γ : BridgeNames) (Hbound : threadBound GF + 1 ≤ 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (bF b go!"wg") γ.wg bridgeWGN ∗
        inv bridgeWgInvN (wgInv γ) ∗ slRunning γ ∗ threadTok }}
      (App (Val (bF b go!"wg" @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add"))
        (Val #(W64 1)))
    {{ RET #(); wgRunning γ ∗ slRunning γ }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hsl, Htok⟩ HΦ
  iapply sync.WaitGroup.wp_Add (bF b go!"wg") (W64 1) γ.wg bridgeWGN $$ [] [Hsl Htok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro bridgeWG_mask
  iintro Hmask
  inext
  iunfold wgInv at Hi
  icases Hi with ⟨%ctr, %k, %sb, Hwgo, Hk, Hrun, Hsli, ⟨%Hctr, %Hkd⟩, Hw⟩
  iunfold slRunning at Hsl
  ihave %Hag := ghostVar_agree γ.sl _ _ _ _ $$ Hsl Hsli
  subst Hag
  icases threadToks_add_one_lt k $$ [Htok Hk] with ⟨%Hlt, Hk⟩
  · iframe
  simp only [↓reduceIte] at Hkd
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have hb : sint.Z ctr + 1 < 2 ^ 31 := by omega
  have hn : sint.nat (ctr + W32 (sint.Z (W64 1))) = sint.nat ctr + 1 := by
    rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; rw [h1]; omega
  iright
  iframe Hw
  iintro Hw Hwgo
  imod Hmask with -
  imod ownTokAuth_S γ.run k $$ Hrun with ⟨Hrun, Hrtok⟩
  imod Hclose $$ [Hsli Hwgo Hk Hrun Hw] with -
  · inext
    iunfold wgInv
    iexists ctr + W32 (sint.Z (W64 1)), k + 1, true
    simp only [↓reduceIte]
    rw [hn]
    iframe
    ipureintro
    have : sint.Z (ctr + W32 (sint.Z (W64 1))) = sint.Z ctr + 1 := by
      rw [show W32 (sint.Z (W64 1)) = W32 1 from rfl]; word
    omega
  imodintro
  iapply HΦ
  iunfold wgRunning
  iunfold slRunning
  iframe

/-- **`b.wg.Done()` by a `serveConn`, with its receipt**: it gets a deposited thread token
back. -/
theorem wp_bridgeWg_Done (b : Loc) (γ : BridgeNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (bF b go!"wg") γ.wg bridgeWGN ∗
        inv bridgeWgInvN (wgInv γ) ∗ wgRunning γ }}
      (App (Val (bF b go!"wg" @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); threadTok }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hrtok⟩ HΦ
  iapply sync.WaitGroup.wp_Done (bF b go!"wg") γ.wg bridgeWGN $$ [] [Hrtok HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro bridgeWG_mask
  iintro Hmask
  inext
  iunfold wgInv at Hi
  icases Hi with ⟨%ctr, %k, %sb, Hwgo, Hk, Hrun, Hsli, ⟨%Hctr, %Hkd⟩, Hw⟩
  iunfold wgRunning at Hrtok
  icombine Hrun Hrtok gives %Hle
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by
    have : 1 ≤ sint.nat ctr := by rw [Hkd]; omega
    omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  icases (threadToks_add k' 1).1 $$ Hk with ⟨Hk, Htok⟩
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ownTokAuth_delete_S γ.run k' $$ Hrun Hrtok with Hrun
  imod Hclose $$ [Hsli Hwgo Hk Hrun Hw] with -
  · inext
    iunfold wgInv
    iexists ctr - W32 1, k', sb
    rw [hn]
    iframe
    ipureintro
    refine ⟨by rw [hz]; omega, by rw [Hkd]; omega⟩
  imodintro
  iapply HΦ
  iexact Htok

/-- **`b.wg.Done()` by `serveListen`, with its half of the flag**: the flag goes back to
`false`. -/
theorem wp_bridgeWg_Done_sl (b : Loc) (γ : BridgeNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup (bF b go!"wg") γ.wg bridgeWGN ∗
        inv bridgeWgInvN (wgInv γ) ∗ slRunning γ }}
      (App (Val (bF b go!"wg" @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hsync, #Hwg, #Hinv, Hsl⟩ HΦ
  iapply sync.WaitGroup.wp_Done (bF b go!"wg") γ.wg bridgeWGN $$ [] [Hsl HΦ]
  · iframe #
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro bridgeWG_mask
  iintro Hmask
  inext
  iunfold wgInv at Hi
  icases Hi with ⟨%ctr, %k, %sb, Hwgo, Hk, Hrun, Hsli, ⟨%Hctr, %Hkd⟩, Hw⟩
  iunfold slRunning at Hsl
  ihave %Hag := ghostVar_agree γ.sl _ _ _ _ $$ Hsl Hsli
  subst Hag
  simp only [↓reduceIte] at Hkd
  have hc : ((sint.nat ctr : Nat) : Int) = sint.Z ctr := Int.toNat_of_nonneg Hctr
  have h1 : 1 ≤ sint.Z ctr := by omega
  have hn : sint.nat (ctr - W32 1) = sint.nat ctr - 1 := by word
  have hz : sint.Z (ctr - W32 1) = sint.Z ctr - 1 := by word
  have hlt : sint.Z ctr < 2 ^ 31 := by word
  iexists ctr
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ghostVar_update_halves false γ.sl true true $$ Hsl Hsli with ⟨-, Hsli⟩
  imod Hclose $$ [Hsli Hwgo Hk Hrun Hw] with -
  · inext
    iunfold wgInv
    iexists ctr - W32 1, k, false
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hn]
    iframe
    ipureintro
    refine ⟨by rw [hz]; omega, by omega⟩
  imodintro
  iapply HΦ
  itrivial

end wg

end lemmas

end bridgeP
end EtcdGrove
end Perennial
