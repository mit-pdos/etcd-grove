/-
`epaxos.New`: the framework's `replica.New`, the protocol's fields (the composite literal), the
rows, the executor's `r.exec`, the nine rpc registrations, the statistics' counters, the frozen
framework (`fwFreeze`), the instance lock with `instLockInv` (the initial state, `ownRep` of
`RState.init i`), `go r.run()` (`wp_run`), the handle `isReplica`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Run
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NewLit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NewLemmas

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

theorem set_pad5 {A : Type} (l : List A) (k : Nat) (hl : l.length = k) (hk : k < 5) (x y : A) :
    (l ++ List.replicate (5 - k) x).set (sint.Z (W64 (k : Int))).toNat y =
      (l ++ [y]) ++ List.replicate (5 - (k + 1)) x := by
  have e : (sint.Z (W64 (k : Int))).toNat = l.length := by rw [hl]; word
  rw [e, show 5 - k = (5 - (k + 1)) + 1 by omega, List.set_append_right _ _ (Nat.le_refl _),
    Nat.sub_self, List.replicate_succ]
  simp

/-- The new row's contents (`make([]*Instance, MAX_INSTANCE)`), stated once: unifying the two
sides inside the big proof made the kernel unfold `List.replicate` (deep recursion). -/
theorem replicate_row_eq :
    List.replicate 10485760 (zero_val Loc) = List.replicate MAX_INSTANCE (null : Loc) := by
  rw [show (10485760 : Nat) = MAX_INSTANCE from rfl]; rfl

set_option maxHeartbeats 4000000 in
theorem wp_New_of (hRN : replica.New.spec (GF := GF)) (hReg : rpc.Table.Register.spec (GF := GF))
    (hCP : replica.Replica.ConnectToPeers.spec (GF := GF))
    (hCCP : replica.Replica.ComputeClosestPeers.spec (GF := GF))
    (hWC : replica.Replica.WaitForClientConnections.spec (GF := GF))
    (hP : dlog.Logger.Printf.spec (GF := GF)) (hS : CmdStringSpec (GF := GF)) (hH : HandlerSpecs (GF := GF))
    (hEx : ExecuteCommandsSpec (GF := GF))
    (γ : EpNames) (k i : Nat) (L : List GoString) (sl : GoSlice) (cfg logger : Loc)
    (c : config.Config) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos ∗
        ⌜k ∈ replicaNodes ∧ L[i]? = some (peerAddrOf k)⌝ ∗ idTok γ i ∗ repFwStart γ i ∗
        epRepStart γ i ∗
        listFinal γ L ∗ sl ↦* L ∗ clientInvs γ ∗
        cfg ↦ c ∗ c.Proxy' ↦ (zeroValDef : config.ProxyInfo) ∗
      ⌜c.Leader' = null ∧ c.Port' = W64 (7500 + k)⌝ ∗
        logger ↦ (zeroValDef : dlog.Logger) }}
      (App (App (App (App (App (App (App (App (App (App (App
        (Val (@! epaxos.New)) (Val #c.Alias')) (Val #(W64 i))) (Val #sl)) (Val #true))
        (Val #false)) (Val #false)) (Val #(W64 0))) (Val #false)) (Val #(W64 2))) (Val #cfg))
        (Val #logger))
    {{ (r : Loc), RET #r; isReplica γ i r ∗ ⌜r ≠ null⌝ }} := by
  wp_start as ⟨%Hk, Hid, Hfws, Heps, #Hlf, Hsl, #HCI, Hcfg, Hproxy, %Hc, Hlog⟩
  ihave #Hpk : pkgInit_epaxos $$ []
  · iPkgInit
  ipersist Hcfg
  ipersist Hlog
  ipersist Hsl
  ihave %Hok := listFinal_ok $$ Hlf
  have hL5 : L.length = 5 := by unfold finalListOk at Hok; rw [Hok.length_eq]; decide
  have hi5 : i < 5 := by
    have := (List.getElem?_eq_some_iff.mp Hk.2).1; omega
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hslen : sl.len = W64 5 := by
    have h1 := Hsll.1; rw [hL5] at h1; have := Hsll.2
    apply BitVec.eq_of_toInt_eq; word
  ipersist Hproxy
  wp_auto
  wp_apply (hRN γ k i L sl c.Alias' cfg logger c.Proxy' c) $$ [$Hlf $Hsl $HCI $Hfws $Hcfg
    $Hproxy $Hlog] as %rr ⟨%p, %Hp, Hfresh⟩
  · ipureintro; exact ⟨Hk, rfl⟩
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch0 %γ0 ⟨#Hch0, -, Ho0⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch1 %γ1 ⟨#Hch1, -, Ho1⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch2 %γ2 ⟨#Hch2, -, Ho2⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch3 %γ3 ⟨#Hch3, -, Ho3⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch4 %γ4 ⟨#Hch4, -, Ho4⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 6000000)) as %ch5 %γ5 ⟨#Hch5, -, Ho5⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 6000000)) as %ch6 %γ6 ⟨#Hch6, -, Ho6⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 4000000)) as %ch7 %γ7 ⟨#Hch7, -, Ho7⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch8 %γ8 ⟨#Hch8, -, Ho8⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 2000000)) as %ch9 %γ9 ⟨#Hch9, -, Ho9⟩
  · ipureintro; decide
  rw [hslen]
  wp_apply (wp_slice_make2 (V := GoSlice) (W64 5)) as %iss ⟨Hiss, -⟩
  · ipureintro; decide
  try rw [hslen]
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %crt ⟨Hcrt, -⟩
  · ipureintro; decide
  try rw [hslen]
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %cut ⟨Hcut, -⟩
  · ipureintro; decide
  try rw [hslen]
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %eut ⟨Heut, -⟩
  · ipureintro; decide
  try rw [hslen]
  wp_apply (wp_slice_make2 (V := GoMap) (W64 5)) as %cfs ⟨Hcfs, -⟩
  · ipureintro; decide
  try rw [hslen]
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %ls ⟨Hls, -⟩
  · ipureintro; decide
  try rw [hslen]
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %lp ⟨Hlp, -⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := w64) (V := w32) _ _) as %msk Hmsk
  wp_apply_core (chan.wp_make2 (V := Loc) (W64 2000000))
  · ipureintro; decide
  iintro %rch %γrc ⟨#Hrch, -, Hrco⟩
  wp_pures
  wp_load
  wp_pures
  wp_load
  wp_pures
  wp_alloc_auto
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_apply wp_Replica_lit
  unfold fwFresh
  icases Hfresh with ⟨#Hro, HBeac, HDur, Htbl, Hstate, Hfst⟩
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hro
  wp_auto
  -- the rows
  ihave HI : (∃ k : Nat, "i" ∷ i_ptr ↦ W64 (k : Int) ∗ "%Hk5" ∷ ⌜k ≤ 5⌝ ∗
      "Hrw" ∷ (∃ rows : List GoSlice, iss ↦* (rows ++ List.replicate (5 - k) (zero_val GoSlice)) ∗
        ⌜rows.length = k⌝ ∗
        [∗list] row ∈ rows, row ↦* List.replicate MAX_INSTANCE (null : Loc)) ∗
      "Hcrt" ∷ crt ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (zero_val w32)) ∗
      "Hcut" ∷ cut ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (zero_val w32)) ∗
      "Heut" ∷ eut ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (zero_val w32)) ∗
      "Hls" ∷ ls ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (zero_val w32)) ∗
      "Hlp" ∷ lp ↦* (List.replicate k (W32 (-1)) ++ List.replicate (5 - k) (zero_val w32)) ∗
      "Hcm" ∷ (∃ cms : List GoMap, cfs ↦* (cms ++ List.replicate (5 - k) (zero_val GoMap)) ∗
        ⌜cms.length = k⌝ ∗ [∗list] m ∈ cms, m ↦$ (∅ : GMap w64 Loc)) : IProp GF)
    $$ [i Hiss Hcrt Hcut Heut Hls Hlp Hcfs]
  · iexists 0
    iframe
    isplitr
    · ipureintro; omega
    isplitl [Hiss]
    · iexists []; iframe; isplitr
      · ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; iempintro
    iexists []; iframe; isplitr
    · ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  wp_if_destruct
  · have hk5 : k < 5 := by rw [hL5] at *; word
    wp_apply (wp_slice_make2 (V := Loc) (W64 10485760)) as %row ⟨Hrow, -⟩
    · ipureintro; decide
    icases Hrw with ⟨%rows, Hiss, %Hrl, Hrows⟩
    icases Hcm with ⟨%cms, Hcfs, %Hcml, Hcms⟩
    ihave %Hl_Hiss := ownSlice_len _ _ _ $$ Hiss
    have hb_Hiss : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z iss.len := by
      have := Hl_Hiss.1; have := Hl_Hiss.2; simp [Hrl] at *; word
    simp only [hb_Hiss, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := GoSlice) iss (sint.Z (W64 (k : Int))) _ row) $$ [$Hiss] as Hiss
    · ipureintro; have := Hl_Hiss.1; have := Hl_Hiss.2; simp [Hrl] at *; word
    ihave %Hl_Hcrt := ownSlice_len _ _ _ $$ Hcrt
    have hb_Hcrt : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z crt.len := by
      have := Hl_Hcrt.1; have := Hl_Hcrt.2; simp [] at *; word
    simp only [hb_Hcrt, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := w32) crt (sint.Z (W64 (k : Int))) _ (W32 (-1))) $$ [$Hcrt] as Hcrt
    · ipureintro; have := Hl_Hcrt.1; have := Hl_Hcrt.2; simp [] at *; word
    ihave %Hl_Heut := ownSlice_len _ _ _ $$ Heut
    have hb_Heut : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z eut.len := by
      have := Hl_Heut.1; have := Hl_Heut.2; simp [] at *; word
    simp only [hb_Heut, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := w32) eut (sint.Z (W64 (k : Int))) _ (W32 (-1))) $$ [$Heut] as Heut
    · ipureintro; have := Hl_Heut.1; have := Hl_Heut.2; simp [] at *; word
    ihave %Hl_Hcut := ownSlice_len _ _ _ $$ Hcut
    have hb_Hcut : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cut.len := by
      have := Hl_Hcut.1; have := Hl_Hcut.2; simp [] at *; word
    simp only [hb_Hcut, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := w32) cut (sint.Z (W64 (k : Int))) _ (W32 (-1))) $$ [$Hcut] as Hcut
    · ipureintro; have := Hl_Hcut.1; have := Hl_Hcut.2; simp [] at *; word
    wp_apply (wp_map_make2 (K := w64) (V := Loc) (W64 200000) _ _) as %cm Hcm
    ihave %Hl_Hcfs := ownSlice_len _ _ _ $$ Hcfs
    have hb_Hcfs : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z cfs.len := by
      have := Hl_Hcfs.1; have := Hl_Hcfs.2; simp [Hcml] at *; word
    simp only [hb_Hcfs, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := GoMap) cfs (sint.Z (W64 (k : Int))) _ cm) $$ [$Hcfs] as Hcfs
    · ipureintro; have := Hl_Hcfs.1; have := Hl_Hcfs.2; simp [Hcml] at *; word
    ihave %Hl_Hls := ownSlice_len _ _ _ $$ Hls
    have hb_Hls : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z ls.len := by
      have := Hl_Hls.1; have := Hl_Hls.2; simp [] at *; word
    simp only [hb_Hls, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := w32) ls (sint.Z (W64 (k : Int))) _ (W32 (-1))) $$ [$Hls] as Hls
    · ipureintro; have := Hl_Hls.1; have := Hl_Hls.2; simp [] at *; word
    ihave %Hl_Hlp := ownSlice_len _ _ _ $$ Hlp
    have hb_Hlp : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z lp.len := by
      have := Hl_Hlp.1; have := Hl_Hlp.2; simp [] at *; word
    simp only [hb_Hlp, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index (V := w32) lp (sint.Z (W64 (k : Int))) _ (W32 (-1))) $$ [$Hlp] as Hlp
    · ipureintro; have := Hl_Hlp.1; have := Hl_Hlp.2; simp [] at *; word
    wp_for_post
    iframe
    iexists k + 1
    have hrep : ∀ a : w32, List.replicate k a ++ [a] = List.replicate (k + 1) a := fun a => by
      rw [List.replicate_succ']
    rw [set_pad5 rows k Hrl hk5, set_pad5 cms k Hcml hk5,
      set_pad5 (List.replicate k (W32 (-1))) k (by simp) hk5, hrep]
    have e1 : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    rw [e1]
    iframe
    isplitr
    · ipureintro; omega
    isplitl [Hiss Hrows Hrow]
    · iexists rows ++ [row]; iframe
      isplitr
      · ipureintro; simp [Hrl]
      iapply BigSepL.bigSepL_cons.2
      rw [replicate_row_eq]
      iframe
      iapply BigSepL.bigSepL_nil.2; iempintro
    iexists cms ++ [cm]; iframe
    isplitr
    · ipureintro; simp [Hcml]
    iapply BigSepL.bigSepL_nil.2; iempintro
  -- after the rows: k = 5
  have hk5 : k = 5 := by rw [hL5] at Hif; have : ¬ ((k : Int) < 5) := by word
                         omega
  subst hk5
  icases Hrw with ⟨%rows, Hiss, %Hrl, Hrows⟩
  icases Hcm with ⟨%cms, Hcfs, %Hcml, Hcms⟩
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  generalize «$r0_ptr» = rp
  ihave ⟨«$r0», %Hrnn⟩ := typedPointsto_not_null_dup $$ «$r0»
  iStructNamedPrefix «$r0» "f_"
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 100) (by decide)) as %stk ⟨Hstk, Hstkc, %Hstkcap⟩
  generalize «$r0_ptr» = ep
  iStructNamedPrefix «$r0» "e_"
  wp_apply (wp_slice_make2 (V := state.Command) (W64 0)) as %cpm ⟨-, -⟩
  · ipureintro; decide
  -- the channels' bags
  iapply fupd_wp
  imod (start_bag (V := GoInterface) (deliverChanP γ i .prepare) (ChanState.Buffered []) ch0 γ0 trivial)
    $$ Hch0 Ho0 with #Hb0
  imod (start_bag (V := GoInterface) (deliverChanP γ i .preAccept) (ChanState.Buffered []) ch1 γ1 trivial)
    $$ Hch1 Ho1 with #Hb1
  imod (start_bag (V := GoInterface) (deliverChanP γ i .accept) (ChanState.Buffered []) ch2 γ2 trivial)
    $$ Hch2 Ho2 with #Hb2
  imod (start_bag (V := GoInterface) (deliverChanP γ i .commit) (ChanState.Buffered []) ch3 γ3 trivial)
    $$ Hch3 Ho3 with #Hb3
  imod (start_bag (V := GoInterface) (deliverChanP γ i .prepareReply) (ChanState.Buffered []) ch4 γ4 trivial)
    $$ Hch4 Ho4 with #Hb4
  imod (start_bag (V := GoInterface) (deliverChanP γ i .preAcceptReply) (ChanState.Buffered []) ch5 γ5 trivial)
    $$ Hch5 Ho5 with #Hb5
  imod (start_bag (V := GoInterface) (deliverChanP γ i .acceptReply) (ChanState.Buffered []) ch7 γ7 trivial)
    $$ Hch7 Ho7 with #Hb7
  imod (start_bag (V := GoInterface) (deliverChanP γ i .tryPreAccept) (ChanState.Buffered []) ch8 γ8 trivial)
    $$ Hch8 Ho8 with #Hb8
  imod (start_bag (V := GoInterface) (deliverChanP γ i .tryPreAcceptReply) (ChanState.Buffered []) ch9 γ9 trivial)
    $$ Hch9 Ho9 with #Hb9
  imod (start_bag (V := Loc) (recoverReq γ i) _ rch γrc (by rw [if_neg (by decide)]; trivial))
    $$ Hrch Hrco with #Hbr
  imodintro
  wp_alloc o0 as Hp0
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o1 as Hp1
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o2 as Hp2
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o3 as Hp3
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o4 as Hp4
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o5 as Hp5
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o6 as Hp6
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o7 as Hp7
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  wp_alloc o8 as Hp8
  wp_auto
  wp_apply (hReg p.tbl) $$ [$Htbl] as Htbl
  have e10 : (W8 9 + 1 : w8) = W8 10 := by decide
  have e11 : (W8 10 + 1 : w8) = W8 11 := by decide
  have e12 : (W8 11 + 1 : w8) = W8 12 := by decide
  have e13 : (W8 12 + 1 : w8) = W8 13 := by decide
  have e14 : (W8 13 + 1 : w8) = W8 14 := by decide
  have e15 : (W8 14 + 1 : w8) = W8 15 := by decide
  have e16 : (W8 15 + 1 : w8) = W8 16 := by decide
  have e17 : (W8 16 + 1 : w8) = W8 17 := by decide
  have e18 : (W8 17 + 1 : w8) = W8 18 := by decide
  simp only [e10, e11, e12, e13, e14, e15, e16, e17, e18]
  -- the statistics' counters
  iStructNamedPrefix HStm "sm_"
  rw [fwStart_unseal]; unfold fwStartDef
  icases Hfst with ⟨Hrfs, HM, Hpeers, Hrd, Hwr, Halv, Hlat, Hewma, Hcw, ⟨%sm, Hsm⟩, HLis, Hpo⟩
  wp_auto
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  wp_apply (wp_mapInsert go.string p.statsMap _ _ _) $$ [$Hsm] as Hsm
  ihave Hfst : fwStart γ rr i L p $$ [Hrfs HM Hpeers Hrd Hwr Halv Hlat Hewma Hcw Hsm HLis Hpo]
  · rw [fwStart_unseal]; unfold fwStartDef
    iframe
  -- the read-only fields
  ipersist f_Replica
  ipersist f_prepareChan
  ipersist f_preAcceptChan
  ipersist f_acceptChan
  ipersist f_commitChan
  ipersist f_prepareReplyChan
  ipersist f_preAcceptReplyChan
  ipersist f_acceptReplyChan
  ipersist f_tryPreAcceptChan
  ipersist f_tryPreAcceptReplyChan
  ipersist f_prepareRPC
  ipersist f_prepareReplyRPC
  ipersist f_preAcceptRPC
  ipersist f_preAcceptReplyRPC
  ipersist f_acceptRPC
  ipersist f_acceptReplyRPC
  ipersist f_commitRPC
  ipersist f_tryPreAcceptRPC
  ipersist f_tryPreAcceptReplyRPC
  ipersist f_InstanceSpace
  ipersist f_crtInstance
  ipersist f_CommittedUpTo
  ipersist f_ExecedUpTo
  ipersist f_conflicts
  ipersist f_lastScan
  ipersist f_lastPut
  ipersist f_maxSeqPerKey
  ipersist f_instancesToRecover
  ipersist f_batchWait
  ipersist f_transconf
  ipersist f_lock
  ipersist f_exec
  ipersist e_r
  ipersist Hiss
  ipersist Hcfs
  -- the frozen framework
  ihave #Hents : tableEntriesOk γ i (newTable (kindSel o0 o1 o2 o3 o4 o5 o6 o7 o8)
      (kindSel ch0 ch4 ch1 ch5 ch2 ch7 ch3 ch8 ch9)) $$ []
  · iapply tableEntries_new γ i _ _ (kindSel γ0 γ4 γ1 γ5 γ2 γ7 γ3 γ8 γ9)
    iapply allKinds_intro
    simp only [kindSel]
    iframe #
  simp only [newTable, MsgKind.all, List.foldl, kindSel, MsgKind.code, MsgKind.ty]
  iapply fupd_wp
  imod (fwFreeze γ rr i p (W8 18) _) $$ Hpkg HBeac HDur Htbl Hents with #Hfz
  -- the instance lock
  unfold epRepStart
  icases Heps with ⟨Hfrag, Hidle, #Hinv⟩
  ihave Hrep := ownRep_init (GF := GF) γ i rp rr p.st iss crt cut eut cfs ls lp msk rows cms Hrl Hcml
    $$ [Hrows Hcrt Hcut Heut Hcms Hmsk Hls Hlp f_maxSeq f_IsLeader f_maxRecvBallot Hstate]
  · iframe #
    iframe
  imod (sync.init_Mutex (instLockInv γ i rp) ⊤ «$v38_ptr») $$ «$v38»
    [Hrep Hfrag Hidle e_stack Hstk Hstkc] with #Hmu
  · inext
    unfold instLockInv execStackOwn
    isplitl [Hrep Hfrag Hidle]
    · iexists _; iframe
    iexists ep, stk, _
    iframe #
    iframe
    ipureintro; rw [Hstkcap]; decide
  imodintro
  ihave #Hisr : isReplica γ i rp $$ []
  · rw [isReplica_unseal]; unfold isReplicaDef epROFields
    iexists rr, L, p
    iframe #
    ipureintro; rw [hL5]; rfl
  wp_apply wp_fork $$ [Hfst f_slowClockChan f_fastClockChan f_cpcounter]
  · wp_apply (wp_run hCP hCCP hWC hP hS hH hEx γ i rp rr L p)
      $$ [Hfst f_slowClockChan f_fastClockChan f_cpcounter] as Hf
    · unfold runPre cpcOwn
      ihave #Hks : ([∗list] k ∈ MsgKind.all, ∃ (ch : GoChan) (γc : ChanNames),
          efld rp k.chanField ↦□ ch ∗ isChanBag γc ch (deliverChanP γ i k)) $$ []
      · iapply allKinds_intro
        simp only [MsgKind.chanField]
        isplitr
        · iexists ch0, γ0; iframe #
        isplitr
        · iexists ch4, γ4; iframe #
        isplitr
        · iexists ch1, γ1; iframe #
        isplitr
        · iexists ch5, γ5; iframe #
        isplitr
        · iexists ch2, γ2; iframe #
        isplitr
        · iexists ch7, γ7; iframe #
        isplitr
        · iexists ch3, γ3; iframe #
        isplitr
        · iexists ch8, γ8; iframe #
        iexists ch9, γ9; iframe #
      iframe #
      iframe
    iexfalso; iexact Hf
  iapply HΦ
  iframe Hisr
  ipureintro; exact Hrnn


end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
