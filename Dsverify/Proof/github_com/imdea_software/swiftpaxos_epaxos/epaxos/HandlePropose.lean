/-
`(*Replica).handlePropose` (the run loop's `ProposeSpec`): the row-full test (fix R-CAP), the
batch drained from `ProposeChan` (`len` + receives), the proposal's ghost step (`ep_propose`, taken
here), `startPhase1`, `r.cpcounter`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlersLink

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

/-- `ep_propose` with the pre-state's invariant (`ep_proposeB`). -/
theorem ep_proposePre (γ : EpNames) (E : CoPset) (i : Nat) (σ : RState) (batch : List Proposal)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hb : batch ≠ [])
    (hfull : rowFull σ = true → batch.length = 1) (hlen : batch.length < 2 ^ 62) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ repIdle γ i -∗
      ([∗list] p ∈ batch, batchElemOk γ i p) -∗ £ 1 ={E}=∗
      ⌜(∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ) ∧
        ∀ p ∈ batch, ∃ inp : KvI, inPre inp ∧ p.cmd = cmdOf inp⌝ ∗
      repFrag γ i (hPropose σ batch).1 ∗ outsOk γ i (hPropose σ batch).2 := by
  rw [epInv_unseal, epInvDef_eq, repIdle_eq, outsOk_eq]
  unfold batchElemOk repFrag inChan
  exact ep_proposeB γ protoN E i σ batch hE hi hb hfull hlen

/-- The replica's state satisfies the protocol invariant (read off `epInv`). -/
theorem repFrag_inv (γ : EpNames) (i : Nat) (σ : RState) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ £ 1 ={⊤}=∗
      repFrag γ i σ ∗ ⌜∃ S : Sys, Inv S ∧ S.rep i = σ⌝ := by
  iintro #Hinv Hf Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  rw [epInv_unseal]; unfold epInvDef
  icases Hi with ⟨%S, Ha, %hS, Hrest⟩
  ihave %hσ := repFrag_agree γ S i σ $$ Ha Hf
  imod Hclose $$ [Ha Hrest] with -
  · inext; iexists S; iframe; ipureintro; exact hS
  imodintro
  iframe Hf
  ipureintro; exact ⟨S, hS, hσ⟩

/-- A received proposal: its model value, held part, and ghost-step part. -/
theorem proposal_split (γ : EpNames) (i : Nat) (g : Loc) :
    proposal (GF := GF) γ i g ⊢ ∃ (p : Proposal) (pp w mu : Loc) (proxy : Bool) (addr : GoString)
      (c : w32) (cv : state.Command),
      g ↦□ replica.defs.GPropose.mk pp w mu proxy addr ∗
      pp ↦□ replica.defs.Propose.mk (W32 0) c cv (W64 0) ∗ cmdOk cv p.cmd ∗
      propHeld γ i false g p ∗ batchElemOk γ i p := by
  unfold proposal
  iintro ⟨%pp, %w, %mu, %proxy, %addr, %cid, %c, %inp, %cv, #Hg, #Hpp, #Hok, #Hcc, #Hcw, Htok,
    Hor⟩
  iexists ⟨cid, cmdOf inp⟩, pp, w, mu, proxy, addr, W32 (uint.Z c), cv
  iframe Hg Hpp Hok
  isplitl [Htok]
  · unfold propHeld
    iexists pp, w, mu, proxy, addr, c, inp, cv
    simp only [Bool.false_eq_true, if_false]
    iframe Hg Hpp Hok Hcc Hcw Htok
  unfold batchElemOk
  icases Hor with (Ho | Ho)
  · ileft; iframe Ho; iexists c, inp; iframe Hcc; ipureintro; rfl
  · iright; iexact Ho

theorem prop_set_pad {α : Type} (xs : List α) (z x : α) (n : Nat) (h : 0 < n) :
    (xs ++ List.replicate n z).set xs.length x = (xs ++ [x]) ++ List.replicate (n - 1) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.set_append_right _ _ (by omega)]
  simp [List.replicate_succ]

/-- The model facts `handlePropose` needs, from the pre-state's invariant. -/
theorem propose_facts {i : Nat} {σ : RState} (h : ∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ) :
    σ.id = i ∧ ConfWf σ ∧ -1 ≤ zz (σ.crtInstance i) ∧ toN (σ.crtInstance i) + 1 < MAX_INSTANCE := by
  obtain ⟨S, hS, hi, rfl⟩ := h
  have hwf := hS.1.1
  refine ⟨hwf.1 i hi, ?_, (hwf.2.2.1 i hi i hi).1, (hwf.2.2.1 i hi i hi).2⟩
  exact ⟨fun q k pr hpr => hwf.2.2.2.1 i hi q k pr hpr, fun q hq => hS.2.classWf i hi q hq⟩

theorem propose_outsWf {σ : RState} (batch : List Proposal)
    (hlen : batch.length < 2 ^ 62)
    (hvals : ∀ p ∈ batch, ∃ inp : KvI, inPre inp ∧ p.cmd = cmdOf inp) :
    OutsWf (hPropose σ batch).2 := by
  intro o ho
  unfold hPropose at ho
  split at ho
  · simp at ho
  dsimp only at ho
  unfold startPhase1 at ho
  dsimp only at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · simp only [bcastPreAcceptOf, preAcceptOf, Option.getD_some, Msg.wf]
    refine ⟨⟨by simpa using hlen, fun c hc => ?_⟩, ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      obtain ⟨inp, hpre, hc⟩ := hvals p hp
      rw [cmdWf, hc]
      cases inp with
      | get k => simp [cmdOf]
      | put k v => simp only [cmdOf]; have := hpre.2.2; omega
      | scan k n => simp only [cmdOf, u64Le_length]; decide
    · unfold depsWf
      rw [(model.ConfProof.ua_spec _ _ _ _).1]; simp [nR]

set_option maxHeartbeats 4000000 in
/-- **`handlePropose(propose)`** in the run loop's form. -/
theorem wp_handlePropose (hS : replica.Replica.SendMsg.spec (GF := GF)) : ProposeSpec (GF := GF) := by
  intro γ i r rr L p Rext ord σ g hpo
  iintro %Φ ⟨#Hctx, Hrep, Hf, Hidle, Hg, Hcpc⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hord := hdCtx_ord $$ Hctx'
  unfold hdCtx
  icases Hctx' with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hfro
  have hi : i < nR := by have := HLn.2; have := HLn.1; unfold nR nRep at *; omega
  icases ownRep_open γ i r σ $$ Hrep with ⟨%Hib, %Hcb, Hinsts, Hrest⟩
  unfold ownRepRest
  icases Hrest with ⟨Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb, Hstore, Hpeer⟩
  unfold repRowArr
  icases Hcrt with ⟨%crt, #Hcrtf, Hcrtsl⟩
  ihave %Hclen := ownSlice_len _ _ _ $$ Hcrtsl
  wp_method_call
  wp_call
  wp_auto_lc 2
  iapply fupd_wp
  imod repFrag_inv γ i σ $$ Hinv Hf Hlc1 with ⟨Hf, %Hpre0⟩
  imodintro
  have Hpre : ∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ := by
    obtain ⟨S, h1, h2⟩ := Hpre0; exact ⟨S, h1, hi, h2⟩
  obtain ⟨hid, hconf, hcrt1, hcrt2⟩ := propose_facts Hpre
  have ei : sint.Z (W64 (sint.Z (W32 (i : Int)))) = i := by have : i < 5 := hi; word
  have ein : (sint.Z (W64 (sint.Z (W32 (i : Int))))).toNat = i := by rw [ei]; simp
  have hb : 0 ≤ sint.Z (W64 (sint.Z (W32 (i : Int)))) ∧ sint.Z (W64 (sint.Z (W32 (i : Int)))) < sint.Z crt.len := by
    rw [ei]; have h1 := Hclen.1; have h2 := Hclen.2
    simp only [List.length_map, List.length_range] at h1
    have : (nR : Int) = sint.Z crt.len := by rw [h1]; exact Int.toNat_of_nonneg h2
    constructor <;> omega
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index crt _ _ _ (σ.crtInstance i) hb.1 $$ [$Hcrtsl] as Hcrtsl
  · ipureintro; rw [ein]; simp [hi]
  ihave %Hgnn := (show proposal γ i g ⊢ ⌜g ≠ null⌝ from by
    unfold proposal; iintro ⟨%pp, %w, %mu, %proxy, %addr, %cid, %c, %inp, %cv, #Hg, -⟩
    iapply typedPointsto_not_null $$ Hg) $$ Hg
  icases proposal_split γ i g $$ Hg with ⟨%p0, %pp, %w, %mu, %proxy, %addr, %c, %cv, #Hgp, #Hpp,
    #Hok, Hheld, Hbe⟩
  have hfullIff : rowFull σ = decide (sint.Z (W32 10485759) ≤ sint.Z (σ.crtInstance i + W32 1)) := by
    unfold rowFull; rw [hid]; simp [BitVec.sle, MAX_INSTANCE]; rfl
  rcases hrf : rowFull σ
  · have hc : ¬ sint.Z (W32 10485759) ≤ sint.Z (σ.crtInstance i + W32 1) := by
      have := hfullIff; rw [hrf] at this; exact of_decide_eq_false this.symm
    rw [show decide (sint.Z (W32 10485759) ≤ sint.Z (σ.crtInstance i + W32 1)) = false from
      decide_eq_false hc]
    ihave ⟨%γc, #Hbag, %Hcap⟩ := fwRO_proposeChanCap _ _ _ _ _ $$ Hfro
    ihave #Hch := is_bag_is_chan _ _ _ $$ Hbag
    wp_auto
    wp_func_call
    wp_call
    wp_apply (Perennial.wp_Len (t := replica.defs.GPropose.ty.PointerType) p.pchan γc) $$ [$Hch]
      as %ln %Hln
    ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
    wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
    unfold fwLockInv
    icases HR with ⟨Hcore, Hext⟩
    icases fwCore_stats _ _ _ _ $$ Hcore with ⟨%sm, Hsm, Hcclose⟩
    ihave #HStm2 := HStm
    iStructNamed HStm2
    wp_auto
    wp_apply (wp_map_lookup1 (V := w64) go.string go.int p.statsMap sm) $$ [$Hsm] as Hsm
    wp_apply wp_mapInsert $$ [$Hsm] as Hsm
    wp_apply (wp_map_lookup1 (V := w64) go.string go.int p.statsMap) $$ [$Hsm] as Hsm
    wp_apply wp_mapInsert $$ [$Hsm] as Hsm
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hsm Hcclose Hext]
    · ihave Hc := Hcclose $$ Hsm
      iframe
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index crt _ _ _ (σ.crtInstance i) hb.1 $$ [$Hcrtsl] as Hcrtsl
    · ipureintro; rw [ein]; simp [hi]
    have hb' : 0 ≤ sint.Z (W64 (sint.Z (W32 (i : Int)))) ∧
        sint.Z (W64 (sint.Z (W32 (i : Int)))) < ((List.range nR).map σ.crtInstance).length := by
      rw [ei]; simp; omega
    wp_apply wp_store_slice_index $$ [$Hcrtsl] as Hcrtsl
    · ipureintro; exact hb'
    rw [ein, ← map_range_upd _ _ _ _ hi]
    -- the batch: `len(ProposeChan) + 1` slots
    have hov : sint.Z ln < 2 ^ 63 - 1 := by have := Hln.2; omega
    have hbs : sint.Z (ln + W64 1) = sint.Z ln + 1 := by have := Hln.1; word
    wp_apply (wp_slice_make2 (V := state.Command) (ln + W64 1)) as %csl ⟨Hcsl, Hccap⟩
    · ipureintro; omega
    wp_apply (wp_slice_make2 (V := Loc) (ln + W64 1)) as %psl ⟨Hpsl, Hpcap⟩
    · ipureintro; omega
    ihave #Hgp2 := Hgp
    iStructNamed Hgp2
    ihave #Hpp2 := Hpp
    iStructNamed Hpp2
    wp_auto
    ihave %Hcl := ownSlice_len _ _ _ $$ Hcsl
    ihave %Hpl := ownSlice_len _ _ _ $$ Hpsl
    obtain ⟨bs, hbsdef⟩ : ∃ bs : Nat, bs = sint.nat ln + 1 := ⟨_, rfl⟩
    have hbsn : sint.nat (ln + W64 1) = bs := by
      rw [hbsdef]; show (sint.Z (ln + W64 1)).toNat = (sint.Z ln).toNat + 1
      rw [hbs]; have := Hln.1; omega
    simp only [hbsn, List.length_replicate] at Hcl Hpl
    have hcz : sint.Z csl.len = bs := by
      have := Hcl.2; rw [show (bs : Int) = ((sint.Z csl.len).toNat : Int) by rw [Hcl.1]]
      omega
    have hpz : sint.Z psl.len = bs := by
      have := Hpl.2; rw [show (bs : Int) = ((sint.Z psl.len).toNat : Int) by rw [Hpl.1]]
      omega
    have h0c : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len := by
      rw [hcz]; exact ⟨by decide, by simp [sint.Z]; omega⟩
    have h0p : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z psl.len := by
      rw [hpz]; exact ⟨by decide, by simp [sint.Z]; omega⟩
    simp only [h0c, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hcsl] as Hcsl
    · ipureintro; simp only [List.length_replicate, hbsn]; exact ⟨by decide, by simp [sint.Z]; omega⟩
    simp only [h0p, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hpsl] as Hpsl
    · ipureintro; simp only [List.length_replicate, hbsn]; exact ⟨by decide, by simp [sint.Z]; omega⟩
    -- receive the rest of the batch
    have hpad1 : ∀ {α : Type} (z x : α), (List.replicate bs z).set 0 x = [x] ++ List.replicate (bs - 1) z := by
      intro α z x
      have := prop_set_pad ([] : List α) z x bs (by omega)
      simpa using this
    rw [hbsn, hpad1, hpad1]
    ihave HI : (∃ (k : Nat) (ps : List Proposal) (gs : List Loc) (cvs : List state.Command),
        "Hi" ∷ i_ptr ↦ W64 (k : Int) ∗
        "Hcsl" ∷ csl ↦* (cvs ++ List.replicate (bs - k) (zero_val state.Command)) ∗
        "Hpsl" ∷ psl ↦* (gs ++ List.replicate (bs - k) (zero_val Loc)) ∗
        "%Hk" ∷ ⌜1 ≤ k ∧ k ≤ bs ∧ ps.length = k ∧ gs.length = k ∧ cvs.length = k⌝ ∗
        "Hoks" ∷ ([∗list] j ↦ c ∈ cvs, ∃ wc, ⌜(ps.map (·.cmd))[j]? = some wc⌝ ∗ cmdOk c wc) ∗
        "Hheld" ∷ ([∗list] j ↦ g ∈ gs, propHeld γ i false g (ps.getD j default)) ∗
        "Hbes" ∷ ([∗list] p ∈ ps, batchElemOk γ i p) : IProp GF)
        $$ [i Hcsl Hpsl Hheld Hbe]
    · iexists 1, [p0], [g], [cv]
      iframe i Hcsl Hpsl
      isplitr
      · ipureintro; exact ⟨Nat.le_refl _, by rw [hbsdef]; omega, rfl, rfl, rfl⟩
      isplitl []
      · iapply (BigSepL.bigSepL_singleton).2; iexists p0.cmd; iframe Hok; ipureintro; rfl
      isplitl [Hheld]
      · iapply (BigSepL.bigSepL_singleton).2; simp only [List.getD_cons_zero]; iexact Hheld
      · iapply (BigSepL.bigSepL_singleton).2; iexact Hbe
    wp_for HI
    have hbsZ : (bs : Int) = sint.Z ln + 1 := by
      rw [hbsdef]; push_cast; rw [show ((sint.nat ln : Nat) : Int) = sint.Z ln from
        Int.toNat_of_nonneg Hln.1]
    have hkz : sint.Z (W64 (k : Int)) = k := by
      have : (k : Int) ≤ sint.Z ln + 1 := by have := Hk.2.1; omega
      have : sint.Z ln < 2 ^ 63 - 1 := hov
      word
    wp_if_destruct
    · -- one more proposal
      have hkb : k < bs := by
        have h' : sint.Z (W64 (k : Int)) < sint.Z (ln + W64 1) := Hif
        rw [hkz, hbs] at h'; omega
      wp_apply (wp_bag_receive (V := Loc) γc p.pchan (proposal γ i)) $$ [$Hbag] as %g' Hg'
      icases proposal_split γ i g' $$ Hg' with ⟨%p', %pp', %w', %mu', %proxy', %addr', %c',
        %cv', #Hgp', #Hpp', #Hok', Hheld', Hbe'⟩
      ihave #Hgp3 := Hgp'
      iStructNamed Hgp3
      ihave #Hpp3 := Hpp'
      iStructNamed Hpp3
      wp_auto
      have hkc : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z csl.len := by
        rw [hkz, hcz]; omega
      have hkp : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z psl.len := by
        rw [hkz, hpz]; omega
      have hkn : (sint.Z (W64 (k : Int))).toNat = k := by rw [hkz]; simp
      simp only [hkc, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index $$ [$Hcsl] as Hcsl
      · ipureintro; simp only [List.length_append, List.length_replicate]; rw [hkz]; omega
      simp only [hkp, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index $$ [$Hpsl] as Hpsl
      · ipureintro; simp only [List.length_append, List.length_replicate]; rw [hkz]; omega
      rw [hkn]
      obtain ⟨Hk1, Hk2, Hk3, Hk4, Hk5⟩ := Hk
      subst Hk5
      rw [prop_set_pad _ _ _ _ (by omega)]
      rw [show (gs ++ List.replicate (bs - cvs.length) (zero_val Loc)).set cvs.length g' =
          (gs ++ [g']) ++ List.replicate (bs - cvs.length - 1) (zero_val Loc) by
        rw [show cvs.length = gs.length by omega]; exact prop_set_pad _ _ _ _ (by omega)]
      wp_for_post
      iframe
      iexists cvs.length + 1, ps ++ [p'], gs ++ [g'], cvs ++ [cv']
      rw [show W64 (cvs.length : Int) + W64 1 = W64 ((cvs.length + 1 : Nat) : Int) by
        have : (cvs.length : Int) < sint.Z ln + 1 := by omega
        have : sint.Z ln < 2 ^ 63 - 1 := hov
        word]
      rw [show bs - (cvs.length + 1) = bs - cvs.length - 1 by omega]
      iframe Hi Hcsl Hpsl
      isplitr
      · ipureintro; simp; omega
      isplitl [Hoks]
      · iapply (BigSepL.bigSepL_append).2
        isplitl [Hoks]
        · iapply BigSepL.bigSepL_mono ?_ $$ Hoks
          intro j c hj
          iintro ⟨%wc, %hwc, Hc⟩
          iexists wc; iframe Hc; ipureintro
          have : j < ps.length := by rw [Hk3]; exact (List.getElem?_eq_some_iff.mp hj).1
          rw [List.map_append, List.getElem?_append_left (by simpa using this)]; exact hwc
        · iapply (BigSepL.bigSepL_singleton).2
          iexists p'.cmd; iframe Hok'; ipureintro; simp [Hk3]
      isplitl [Hheld Hheld']
      · iapply (BigSepL.bigSepL_append).2
        isplitl [Hheld]
        · iapply BigSepL.bigSepL_mono ?_ $$ Hheld
          intro j c hj
          have : j < ps.length := by rw [Hk3, ← Hk4]; exact (List.getElem?_eq_some_iff.mp hj).1
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
        · iapply (BigSepL.bigSepL_singleton).2
          simp [List.getD_eq_getElem?_getD, Hk3, Hk4]; iexact Hheld'
      · iapply (BigSepL.bigSepL_append).2
        iframe Hbes
        iapply (BigSepL.bigSepL_singleton).2; iexact Hbe'
    -- the batch is complete: the proposal step, then `startPhase1`
    obtain ⟨Hk1, Hk2, Hk3, Hk4, Hk5⟩ := Hk
    have hkbs : k = bs := by
      have h' : ¬ sint.Z (W64 (k : Int)) < sint.Z (ln + W64 1) := Hif
      rw [hkz, hbs] at h'; omega
    subst hkbs
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    have hpsne : ps ≠ [] := by intro h; rw [h] at Hk3; simp at Hk3; omega
    iapply fupd_wp
    have hlen : ps.length < 2 ^ 62 := by
      have h1 := Hln.2; have h2 := Hcap; have h3 := Hk3
      simp only [sint.nat] at hbsdef
      omega
    imod ep_proposePre γ ⊤ i σ ps CoPset.subseteq_top hi hpsne (fun h => by rw [hrf] at h; cases h)
      hlen $$ Hinv Hf Hidle Hbes Hlc2 with ⟨%Hpv, Hf, Ho⟩
    imodintro
    -- the model's state after `crtInstance[r.Id]++`, and the step's result
    obtain ⟨σ1, hσ1⟩ : ∃ σ1 : RState, σ1 = { σ with crtInstance := upd σ.crtInstance i (σ.crtInstance i + 1) } := ⟨_, rfl⟩
    have htoN : toN (W32 (i : Int)) = i := by
      unfold toN; have : i < 5 := hi
      rw [show sint.Z (W32 (i : Int)) = (i : Int) by word]; simp
    have hP : hPropose σ ps = ((startPhase1 σ1 (ps.map (·.cmd))
        ⟨toN (W32 (i : Int)), toN (σ.crtInstance i + 1)⟩ (W32 (i : Int)) (σ.crtInstance i + 1)
        (W32 (i : Int)) (some ps)).1,
        Out.ev (.makeBallot ⟨i, toN (σ.crtInstance i + 1)⟩ (W32 (i : Int))) ::
        (startPhase1 σ1 (ps.map (·.cmd)) ⟨toN (W32 (i : Int)), toN (σ.crtInstance i + 1)⟩
          (W32 (i : Int)) (σ.crtInstance i + 1) (W32 (i : Int)) (some ps)).2) := by
      rw [htoN, hσ1]; simp only [hPropose, hrf, hid]; rfl
    rw [hP]
    ihave Ho := outsOk_cons_ev $$ Ho
    -- the arguments
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index crt _ _ _ (σ.crtInstance i + W32 1) hb.1 $$ [$Hcrtsl] as Hcrtsl
    · ipureintro; rw [ein]; simp [hi, upd]
    rw [show σ.crtInstance i + W32 1 = σ.crtInstance i + 1 from rfl]
    -- the state with the bumped row counter
    have hn0 : 0 ≤ zz (σ.crtInstance i + 1) ∧ toN (σ.crtInstance i + 1) + 1 < MAX_INSTANCE := by
      have h1 := hcrt1; have h2 := hcrt2
      have h3 : ¬ sint.Z (W32 10485759) ≤ sint.Z (σ.crtInstance i + W32 1) := hc
      unfold toN zz MAX_INSTANCE at *
      have : sint.Z (W32 10485759) = 10485759 := rfl
      have e : sint.Z (σ.crtInstance i + W32 1) = sint.Z (σ.crtInstance i) + 1 := by
        have : sint.Z (σ.crtInstance i) < 10485760 := by omega
        word
      rw [show σ.crtInstance i + 1 = σ.crtInstance i + W32 1 from rfl, e]; omega
    ihave Hrep1 : ownRep γ i r σ1 $$ [Hinsts Hcrtsl Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore
      Hpeer]
    · iapply ownRep_of
      rw [hσ1]
      unfold ownRepRest repRowArr
      iframe Hinsts Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer
      isplitr
      · ipureintro; exact Hib
      isplitr
      · ipureintro; exact Hcb
      iexists crt; iframe Hcrtf; iexact Hcrtsl
    ihave Hhole := ownRep_hole (GF := GF) γ i r σ1 ⟨toN (W32 (i : Int)), toN (σ.crtInstance i + 1)⟩
      (by rw [htoN]; exact hi) (by have := hn0.2; simp only; omega) $$ Hrep1
    -- the commands and the proposals, read-only from now on
    ipersist Hcsl
    ipersist Hpsl
    ihave #Hcmds : ownCmds csl (ps.map (·.cmd)) DFrac.discard $$ [Hoks]
    · iapply ownCmds_close _ _ _ cvs
      iframe Hcsl Hoks
      ipureintro; simp [Hk3, Hk5]
    have hcsnn : csl ≠ slice.nil := by
      intro h; rw [h] at hcz; simp [slice.nil] at hcz; omega
    have hpsnn : psl ≠ slice.nil := by
      intro h; rw [h] at hpz; simp [slice.nil] at hpz; omega
    ihave Hprops : propsOwn γ i psl (some ps) $$ [Hheld]
    · unfold propsOwn
      iexists gs
      iframe Hpsl Hheld
      ipureintro; exact ⟨hpsnn, by omega⟩
    have hwf1 : RepWf i σ1 ord := ⟨by rw [hσ1]; exact hid, hi, by rw [hσ1]; exact hpo⟩
    have hconf1 : ConfWf σ1 := by rw [hσ1]; exact hconf
    have hout1 := outsWf_tail _ _ (by have := propose_outsWf (σ := σ) ps hlen Hpv.2; rwa [hP] at this)
    have hq1 : 0 ≤ zz (W32 (i : Int)) ∧ zz (W32 (i : Int)) < nR := by
      unfold zz; have : i < 5 := hi
      rw [show sint.Z (W32 (i : Int)) = (i : Int) by word]; unfold nR at *; omega
    wp_apply (wp_startPhase1 hS γ i r rr L p Rext ord σ1 csl (ps.map (·.cmd)) (W32 (i : Int))
      (σ.crtInstance i + 1) (W32 (i : Int)) psl (some ps) hwf1 hq1 hn0 hcsnn hconf1
      Hord hout1)
      $$ [Hhole Hprops Hf Ho] as Hdone
    · unfold hdCtx
      iframe Hhole Hprops Hf Ho
      isplitl []
      · iframe Hpe Hpr Hrr Hfw Hro Hinv Hpo
      iexact Hcmds
    -- `r.cpcounter += len(cmds)`
    unfold cpcOwn
    icases Hcpc with ⟨%v, Hcpc⟩
    wp_auto
    iapply HΦ
    unfold repDone
    iframe Hdone
    iexists _; iexact Hcpc
  -- the row is full: the proposal is dropped (its ghost step taken)
  iapply fupd_wp
  imod ep_proposePre γ ⊤ i σ [p0] CoPset.subseteq_top hi (by simp) (fun _ => rfl) (by simp)
    $$ Hinv Hf Hidle [Hbe] Hlc2 with ⟨-, Hf, Ho⟩
  · iapply (BigSepL.bigSepL_singleton).2; iexact Hbe
  imodintro
  have hP : hPropose σ [p0] = (σ, []) := by simp [hPropose, hrf]
  rw [hP]
  have hc : sint.Z (W32 10485759) ≤ sint.Z (σ.crtInstance i + W32 1) := by
    have := hfullIff; rw [hrf] at this; exact of_decide_eq_true this.symm
  rw [show decide (sint.Z (W32 10485759) ≤ sint.Z (σ.crtInstance i + W32 1)) = true from
    decide_eq_true hc]
  wp_auto
  iapply HΦ
  iframe Hcpc
  iexists σ
  iframe Hf
  isplitr [Ho]
  · iapply ownRep_of
    iframe Hinsts
    unfold ownRepRest repRowArr
    iframe
    isplitr
    · ipureintro; exact Hib
    isplitr
    · ipureintro; exact Hcb
    iexact Hcrtf
  iapply outsOk_idle γ i [] (by intro o ho; simp at ho) $$ Ho

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
