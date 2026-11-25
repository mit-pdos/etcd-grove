/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/DoViewChange.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onDoViewChange` and `finalizeViewChange`: the new primary collects a quorum of valid
DoViewChanges of a view it is the primary of, selects the best log (`IsBest`), takes the
largest commit number (committed in it: `finalize_committed`), starts the view
(`stepFinalize`), executes the committed ops it had not executed (`ghost_lin` at each), seeds the
client table and the pending PrepareOKs of the uncommitted ops, and sends StartViews.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

open Classical

/-- The state at `finalizeViewChange(w)` (from `onDoViewChange`): the replica's state as in
`repInv`, with the pending DoViewChange entry of `w` (live) opened: its responses' map `rsp`,
of at least two responses, each a valid DoViewChange of `w`; the replica is `w`'s primary, in
view change, at a view up to `w`. -/
def replica.finPre (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) (v : replica.Replica) (w : w64) :
    IProp GF :=
  iprop(∃ (lg mine : List Entry) (cw mw : Nat) (me : GoString)
      (C : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) (P : VsrModel.Store → IProp GF)
      (ms : List ipv4port.IPv4Port) (tbl : GMap w64 replica.ClientTableData)
      (pk : GMap w64 replica.PendingPrepareOK) (sv : GMap w64 replica.PendingStartViewChange)
      (dv : GMap w64 replica.PendingDoViewChange) (vst cst : GoInterface)
      (e : replica.PendingDoViewChange) (rsp : GMap w64 events.DoViewChange) (n : Nat),
    -- what never changes
    "%Hid" ∷ ⌜uint.nat v.state'.ID' = r ∧ r < n⌝ ∗
    "#Hms" ∷ v.state'.ClusterMembers' ↦*□ ms ∗
    "%Hmslen" ∷ ⌜ms.length = n⌝ ∗
    "#Hsize" ∷ VsrGhost.fact γ (.size n) ∗
    "#Haddrs" ∷ ([∗list] m ∈ ms, network.addrOk tcp m) ∗
    "%Hnet" ∷ ⌜v.network' = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗
    "#HisTCP" ∷ network.isTCP tcp γ me ∗
    "Hsender" ∷ network.tcpSender tcp ∗
    "#Hprotos" ∷ network.netProtos γ ∗
    "%Htime" ∷ ⌜time.isTime v.time'⌝ ∗
    "#Hlogger" ∷ log.slog.isLogger v.logger' ∗
    "#Hsrv" ∷ examples.vsrkv.srvOk v.srvhandler' P ∗
    "#Hcodec" ∷ encoding.json.codecSet (GF := GF) ∗
    "#Hkit" ∷ encoding.json.kitCodecOk (jc := C) F ∗
    "#Hsys" ∷ VsrGhost.sysInv γ ∗
    "#HregI" ∷ VsrGhost.regInv γ ∗
    "#Hsq" ∷ queue.isQueue events.NetworkEvent.ty v.internal'.sq' (replica.sqElem γ tcp) ∗
    -- the model state
    "Hrep" ∷ VsrGhost.repOwn γ r (replica.repOf v lg) ∗
    "%Hstatus" ∷ ⌜replica.StatusOk v.state'.Status'⌝ ∗
    "%Hst" ∷ ⌜replica.statusOf v.state'.Status' = .stateTransfer →
      primary n (uint.nat v.state'.ViewNumber') ≠ r⌝ ∗
    -- the log
    "#Hlog" ∷ log.ownLogs v.state'.Logs' DFrac.discard lg ∗
    "Hcap" ∷ ownSliceCap log.Log v.state'.Logs' (DFrac.own 1) ∗
    "%Hopnum" ∷ ⌜uint.nat v.state'.OpNum' = lg.length⌝ ∗
    -- the commit number
    "%Hcommit" ∷ ⌜uint.nat v.state'.CommitNumber' ≤ lg.length ∧
      cw ≤ uint.nat v.state'.ViewNumber'⌝ ∗
    "#Hcfact" ∷ VsrGhost.fact γ (.committedBy cw (lg.take (uint.nat v.state'.CommitNumber'))) ∗
    -- the executed prefix and the store
    "%Hmine" ∷ ⌜mine.length = uint.nat v.internal'.lastExecutedOpNum' ∧ mine <+: lg ∧
      mw ≤ replica.mineView v⌝ ∗
    "#Hmlin" ∷ VsrGhost.fact γ (.linPrefix mine) ∗
    "#Hmcom" ∷ VsrGhost.fact γ (.committedBy mw mine) ∗
    "Hstore" ∷ P (storeOf mine) ∗
    -- the client table
    "Htbl" ∷ v.state'.ClientTable' ↦$ tbl ∗
    "%Htmine" ∷ ⌜replica.Covers tbl mine⌝ ∗
    "%Htlog" ∷ ⌜replica.IsNormalPrimary n v r → replica.Covers tbl lg⌝ ∗
    "#Htres" ∷ ([∗map] c ↦ d ∈ tbl, replica.tblOk γ c d) ∗
    -- the pending maps
    "Hpk" ∷ v.internal'.pendingPOKs' ↦$ pk ∗
    "Hpks" ∷ ([∗map] k ↦ e ∈ pk, replica.pokOk γ n tcp v r k e) ∗
    "Hsv" ∷ v.internal'.pendingStartViewChange' ↦$ sv ∗
    "Hsvs" ∷ ([∗map] _w ↦ e ∈ sv, replica.svOk e) ∗
    "Hdv" ∷ v.internal'.pendingDoViewChange' ↦$ dv ∗
    "Hdvs" ∷ ([∗map] w ↦ e ∈ Std.delete dv w, replica.dvOk γ v w e) ∗
    "%Hde" ∷ ⌜dv !! w = some e⌝ ∗
    "Hrsp" ∷ e.Responses' ↦$ rsp ∗
    "Hrsps" ∷ ([∗map] rid ↦ x ∈ rsp, replica.dvcOk γ w rid x) ∗
    "%Hfin" ∷ ⌜w % W64 n = v.state'.ID' ∧ v.state'.Status' = W64 1 ∧
      uint.Z v.state'.ViewNumber' ≤ uint.Z w ∧ n < 2 * GMap.size rsp⌝ ∗
    -- the timers
    "Hvct" ∷ time.isTimer v.internal'.viewChangeTimer' vst ∗
    "Hct" ∷ time.isTimer v.internal'.commitTimer' cst ∗
    "Hgst" ∷ replica.gstOk n v r)

/-- The persistent part of a collected DoViewChange (`dvcOk` without the capacity). -/
def replica.dvcP (γ : VsrGhost.Names) (w rid : w64) (x : events.DoViewChange) :
    IProp GF :=
  iprop(∃ d : Dvc, ⌜d.view = uint.nat w ∧ d.rid = uint.nat rid ∧
      uint.nat x.ViewNum' = d.view ∧ uint.nat x.LastStableViewNum' = d.lnv ∧
      uint.nat x.OpNum' = d.log.length ∧ uint.nat x.CommitNum' = d.commit ∧
      uint.nat x.ReplicaID' = d.rid⌝ ∗
    log.ownLogs x.Logs' DFrac.discard d.log ∗ VsrGhost.fact γ (.msg (.doViewChange d)))

instance replica.dvcP_persistent (γ : VsrGhost.Names) (w rid : w64) (x : events.DoViewChange) :
    Persistent (replica.dvcP (GF := GF) γ w rid x) := by
  unfold replica.dvcP; infer_instance

theorem replica.dvcOk_split (γ : VsrGhost.Names) (w rid : w64) (x : events.DoViewChange) :
    replica.dvcOk (GF := GF) γ w rid x ⊢ replica.dvcP γ w rid x ∗ ownSliceCap log.Log x.Logs' (DFrac.own 1) := by
  unfold replica.dvcOk replica.dvcP
  iintro ⟨%d, %Hd, #Hl, #Hf, Hc⟩
  iframe Hc
  iexists d
  iframe Hl Hf
  ipureintro; exact Hd

/-- A pending DoViewChange entry stays valid when fewer entries are live. -/
theorem replica.dvOk_mono (γ : VsrGhost.Names) (v v' : replica.Replica) (k : w64)
    (e : replica.PendingDoViewChange) (h : replica.Live v' k → replica.Live v k) :
    replica.dvOk (GF := GF) γ v k e ⊢ replica.dvOk γ v' k e := by
  unfold replica.dvOk
  by_cases h' : replica.Live v' k
  · simp only [h', h h', _root_.decide_true, ↓reduceIte]; exact .rfl
  · simp only [h', _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    iintro -; itrivial

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- `finalizeViewChange(w)`: the replica starts view `w` as its primary, normal, with the best
log of the collected DoViewChanges; it holds the StartView of `w` its fields make. -/
theorem replica.wp_finalizeViewChange (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (v : replica.Replica) (w : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.finPre γ r tcp v w }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"finalizeViewChange"))
        (Val #w))
    {{ RET #(); ∃ (v' : replica.Replica) (lg' : List Entry), rp ↦ v' ∗ replica.repInv γ r tcp v' ∗
        ⌜v'.state'.ID' = v.state'.ID' ∧ v'.state'.ClusterMembers' = v.state'.ClusterMembers' ∧
          v'.logger' = v.logger'⌝ ∗
        log.ownLogs v'.state'.Logs' DFrac.discard lg' ∗
        VsrGhost.fact γ (.msg (.startView (uint.nat v'.state'.ViewNumber') (uint.nat v'.state'.OpNum')
          (uint.nat v'.state'.CommitNumber') lg' (uint.nat v'.state'.ID'))) }} := by
  wp_start as ⟨Hr, Hpre⟩
  unfold replica.finPre
  iNamed Hpre
  wp_auto
  wp_apply (wp_slice_literal_nonnull (V := log.Log) [])
  isplitr
  · ipureintro; rfl
  iintro %bl0 %Hbl0 ⟨Hbl0s, -⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hdv as Hdv
  simp only [Hde, Option.getD_some]
  ihave Hsplit : iprop([∗map] k ↦ x ∈ rsp, replica.dvcP γ w k x ∗
      ownSliceCap log.Log x.Logs' (DFrac.own 1)) $$ [Hrsps]
  · iapply (BI.BigSepM.bigSepM_mono (fun _ => replica.dvcOk_split γ w _ _)) $$ Hrsps
  rw [BI.BigSepM.bigSepM_sep_eq]
  icases Hsplit with ⟨HrspP, Hcaps⟩
  have : Persistent ([∗map] k ↦ x ∈ rsp, replica.dvcP γ w k x : IProp GF) :=
    BI.BigSepM.bigSepM_persistent (fun _ => inferInstance)
  icases HrspP with #HrspP
  ipersist Hbl0s
  ihave #Hbl0 : log.ownLogs (slice.mk bl0 (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])))
      DFrac.discard [] $$ [Hbl0s]
  · unfold log.ownLogs
    iexists []
    iframe Hbl0s
    ipureintro
    exact ⟨rfl, fun h => Hbl0 (by cases h; rfl)⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (fun keys (i : Int) => iprop(∃ (found : Bool) (bl bo bc : w64)
      (bls : GoSlice) (blog : List Entry) (seen : List Dvc) (xv : events.DoViewChange),
      found_ptr ↦ found ∗ bestLastStableView_ptr ↦ bl ∗ bestOpNum_ptr ↦ bo ∗
      bestCommit_ptr ↦ bc ∗ bestLogs_ptr ↦ bls ∗ v_ptr ↦ xv ∗
      ⌜0 ≤ i ∧ VsrReplica.SelInv found (uint.nat bl) (uint.nat bo) (uint.nat bc) blog seen ∧
        seen.map (·.rid) = (keys.take i.toNat).map uint.nat ∧
        (∀ d ∈ seen, d.view = uint.nat w) ∧
        (found = true → ∃ kb xb, rsp !! kb = some xb ∧ xb.Logs' = bls)⌝ ∗
      log.ownLogs bls DFrac.discard blog ∗
      [∗list] d ∈ seen, VsrGhost.fact γ (.msg (.doViewChange d)))) _ _ _ _ rsp _ _) $$ Hrsp
  iintro %keys %Hkeys
  obtain ⟨Hkmem, Hksize, Hknd⟩ := Hkeys
  isplitl [found bestLastStableView bestOpNum bestCommit bestLogs v]
  · iexists false, W64 0, W64 0, W64 0, _, [], [], _
    iframe found bestLastStableView bestOpNum bestCommit bestLogs v Hbl0
    isplitr
    · ipureintro
      refine ⟨Int.le_refl _, by simpa using VsrReplica.selInv_nil, by simp, by simp, by simp⟩
    · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
  isplitr
  · imodintro
    iintro %i %key %x %Hkx HP
    obtain ⟨Hki, Hkx⟩ := Hkx
    icases HP with ⟨%found, %bl, %bo, %bc, %bls, %blog, %seen, %xv, Hfound, Hbl, Hbo, Hbc,
      Hbls, Hxv, %Hsel, #Hblog, #Hseen⟩
    ihave #Hdx := BI.BigSepM.bigSepM_lookup Hkx $$ HrspP
    unfold replica.dvcP
    icases Hdx with ⟨%d, %Hd, #Hld, #Hfd⟩
    obtain ⟨Hdv, Hdr, Hxv, Hxl, Hxo, Hxc, Hxr⟩ := Hd
    wp_auto
    wp_join iprop(∃ (found' : Bool) (bl' bo' : w64) (bls' : GoSlice),
        found_ptr ↦ found' ∗ bestLastStableView_ptr ↦ bl' ∗ bestOpNum_ptr ↦ bo' ∗
        bestLogs_ptr ↦ bls' ∗ v_ptr ↦ x ∗
        ⌜found' = true ∧
          uint.nat bl' = (if VsrReplica.SelNew found (uint.nat bl) (uint.nat bo) d then d.lnv
            else uint.nat bl) ∧
          uint.nat bo' = (if VsrReplica.SelNew found (uint.nat bl) (uint.nat bo) d
            then d.log.length else uint.nat bo) ∧
          bls' = (if VsrReplica.SelNew found (uint.nat bl) (uint.nat bo) d then x.Logs'
            else bls)⌝)
      at next with [Hfound Hbl Hbo Hbls Hxv] as ⟨%found', %bl', %bo', %bls', Hfound, Hbl, Hbo, Hbls, Hxv,
        %Hupd⟩
    · cases found
      · wp_auto
        isplitr
        · ipureintro; first | rfl | trivial
        iexists _, _, _, _
        iframe
        ipureintro
        simp [VsrReplica.SelNew, Hxl, Hxo]
      · wp_auto
        wp_if_destruct
        · isplitr
          · ipureintro; first | rfl | trivial
          iexists _, _, _, _
          iframe
          ipureintro
          have : VsrReplica.SelNew true (uint.nat bl) (uint.nat bo) d := by
            right; left; rw [← Hxl]; word
          simp [this, Hxl, Hxo]
        wp_if_destruct
        · wp_if_destruct
          · isplitr
            · ipureintro; first | rfl | trivial
            iexists _, _, _, _
            iframe
            ipureintro
            rw [Hxl]
            have : VsrReplica.SelNew true d.lnv (uint.nat bo) d := by
              right; right; refine ⟨rfl, ?_⟩; rw [← Hxo]; word
            simp [this, Hxo]
          · isplitr
            · ipureintro; first | rfl | trivial
            iexists _, _, _, _
            iframe
            ipureintro
            rw [Hxl]
            have : ¬ VsrReplica.SelNew true d.lnv (uint.nat bo) d := by
              simp only [VsrReplica.SelNew, Bool.true_eq_false, _root_.false_or, not_or, not_and,
                Nat.not_lt]
              exact ⟨Nat.le_refl _, fun _ => by rw [← Hxo]; word⟩
            simp [this]
        · isplitr
          · ipureintro; first | rfl | trivial
          iexists _, _, _, _
          iframe
          ipureintro
          have : ¬ VsrReplica.SelNew true (uint.nat bl) (uint.nat bo) d := by
            simp only [VsrReplica.SelNew, Bool.true_eq_false, _root_.false_or, not_or, not_and,
              Nat.not_lt]
            rename_i h1 h2
            refine ⟨by rw [← Hxl]; word, fun h => absurd ?_ h2⟩
            rw [← Hxl] at h; word
          simp [this]
    wp_join iprop(∃ bc' : w64, bestCommit_ptr ↦ bc' ∗ v_ptr ↦ x ∗
        ⌜uint.nat bc' = if uint.nat bc < d.commit then d.commit else uint.nat bc⌝)
      with [Hbc Hxv] as ⟨%bc', Hbc, Hxv, %Hbc'⟩
    · iexists _
      iframe
      ipureintro
      rw [if_pos (by rw [← Hxc]; word)]; exact Hxc
    · iexists _
      iframe
      ipureintro
      rw [if_neg (by rw [← Hxc]; word)]
    obtain ⟨Hi0, Hsel, Hrids, Hviews, Hfnd⟩ := Hsel
    obtain ⟨Hf', Hbl', Hbo', Hbls'⟩ := Hupd
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists found', bl', bo', bc', bls',
      (if VsrReplica.SelNew found (uint.nat bl) (uint.nat bo) d then d.log else blog),
      seen ++ [d], x
    iframe Hfound Hbl Hbo Hbc Hbls Hxv
    isplitr
    · ipureintro
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · rw [Hf', Hbl', Hbo', Hbc']
        exact VsrReplica.selInv_step Hsel d
      · rw [List.map_append, Hrids, show (i + 1).toNat = i.toNat + 1 by omega,
          List.take_add_one, Hki]
        simp [Hdr]
      · intro d' hd'
        rcases List.mem_append.mp hd' with hd' | hd'
        · exact Hviews d' hd'
        · simp at hd'; subst hd'; exact Hdv
      · intro _
        by_cases hs : VsrReplica.SelNew found (uint.nat bl) (uint.nat bo) d
        · exact ⟨key, x, Hkx, by rw [Hbls', if_pos hs]⟩
        · have hft : found = true := by
            cases found
            · exact absurd (Or.inl rfl) hs
            · rfl
          rw [Hbls', if_neg hs]
          exact Hfnd hft
    isplitl []
    · by_cases hs : VsrReplica.SelNew found (uint.nat bl) (uint.nat bo) d
      · rw [Hbls', if_pos hs, if_pos hs]; iexact Hld
      · rw [Hbls', if_neg hs, if_neg hs]; iexact Hblog
    iapply (BI.BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    iframe Hseen Hfd
  iintro HP Hrsp
  icases HP with ⟨%found, %bl, %bo, %bc, %bls, %blog, %seen, %xv, Hfound, Hbl, Hbo, Hbc,
      Hbls, Hxv, %Hsel, #Hblog, #Hseen⟩
  obtain ⟨-, Hsel, Hrids, Hviews, Hfnd⟩ := Hsel
  -- the DoViewChanges seen: all the responses, from distinct replicas, at least two
  obtain ⟨Hw3, Hst1, Hvw, Hsz⟩ := Hfin
  ihave %Hmlen0 := ownSlice_len $$ Hms
  have hn63 := (replica.len_of_slice _ n (by rw [← Hmslen]; exact Hmlen0)).2
  have hkeys : (keys.take ((GMap.size rsp : Int).toNat)) = keys := by
    rw [Int.toNat_natCast, ← Hksize, List.take_length]
  rw [hkeys] at Hrids
  have hnd : (keys.map uint.nat).Nodup :=
    List.Pairwise.map uint.nat (fun a b hab h => hab (by word)) Hknd
  have h2 : n < 2 * (keys.map uint.nat).length := by rw [List.length_map, Hksize]; exact Hsz
  have hfound : found = true := by
    cases found
    · have := Hsel.1.mp rfl
      subst this
      have := congrArg List.length Hrids
      simp at this
      omega
    · rfl
  subst hfound
  have hr3 : r < n := Hid.2
  have hprim : primary n (uint.nat w) = r := by
    rw [← Hid.1, ← Hw3, replica.primary_word _ _ hn63]
  have hvc : (replica.repOf v lg).status = .viewChange := by
    simp [replica.repOf, replica.statusOf, Hst1]
  have hvle : (replica.repOf v lg).view ≤ uint.nat w := by
    simp only [replica.repOf]; word
  have hmw : mw ≤ (replica.repOf v lg).lnv := by
    have := Hmine.2.2
    simpa [replica.mineView, replica.repOf, replica.statusOf, Hst1] using this
  ihave #Hfs : ([∗list] f ∈ (seen.map (fun d => Fact.msg (.doViewChange d)) ++
      [Fact.committedBy mw mine]), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    rw [BI.BigSepL.bigSepL_map]
    iframe Hseen Hmcom
  have Hall : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = replica.repOf v lg →
      (∀ f ∈ (seen.map (fun d => Fact.msg (.doViewChange d)) ++ [Fact.committedBy mw mine]),
        Holds s f) → _ := fun s hs hsn hrp hf =>
    VsrReplica.finalize_all s hs r (uint.nat w) (replica.repOf v lg) hrp (hsn ▸ hr3)
      (hsn ▸ hprim) hvc hvle seen
      (fun d hd => ⟨Hviews d hd, by
        have := hf (.msg (.doViewChange d))
          (List.mem_append_left _ (List.mem_map_of_mem hd)); exact this⟩)
      (keys.map uint.nat) Hrids hnd (hsn ▸ h2)
      (uint.nat bl) (uint.nat bo) (uint.nat bc) blog Hsel mine mw hmw
      (by have := hf (.committedBy mw mine) (by simp); exact this)
  imod VsrReplica.ghost_pure_rep' γ n r (replica.repOf v lg) _
    (mine <+: blog ∧ uint.nat bc ≤ blog.length ∧ uint.nat bo = blog.length ∧
      (replica.repOf v lg).lnv < (replica.repOf v lg).view)
    (fun s hs hsn hrp hf => let H := Hall s hs hsn hrp hf; ⟨H.1, H.2.1, H.2.2.1, by
      have := VsrReplica.lnv_lt_view s hs r (hsn ▸ hr3) (by rw [hrp]; exact hvc)
      rwa [hrp] at this⟩)
    $$ Hsize Hsys Hrep Hfs with ⟨Hrep, %Hpure⟩
  obtain ⟨Hmb, Hbcl, Hbol, Hlnv⟩ := Hpure
  imod VsrReplica.ghost_step' γ n r (replica.repOf v lg)
    { replica.repOf v lg with view := uint.nat w, status := .normal, log := blog } _
    [Fact.msg (.startView (uint.nat w) blog.length (uint.nat bc) blog r),
     Fact.committedBy (uint.nat w) (blog.take (uint.nat bc))]
    (fun s => stepFinalize s r (uint.nat w) blog)
    (fun s hs hsn hrp hf => by
      obtain ⟨-, -, -, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Hall s hs hsn hrp hf
      refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
      intro f hfm
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hfm
      rcases hfm with rfl | rfl
      · exact h7
      · exact h8)
    $$ Hsize Hsys Hrep Hfs with ⟨Hrep, Hfs'⟩
  wp_auto
  unfold replica.ReplicaStatusNormal
  wp_auto
  obtain ⟨vf, hvf⟩ : ∃ vf : replica.Replica, vf = { v with state' := { v.state' with
      ViewNumber' := w, OpNum' := bo, Logs' := bls, CommitNumber' := bc,
      Status' := W64 0 } } := ⟨_, rfl⟩
  ihave Hr : rp ↦ vf $$ [Hr]
  · iExactEq Hr
    rw [hvf]
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r _ [] (blog.length ≤ 6 * 2 ^ 28)
    (fun s hs hsn hrp _ => by
      have := VsrModel.repLog_length_le s hs r (hsn ▸ hr3); rw [hrp] at this; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, %Hblen⟩
  have hmine_take : mine = blog.take (uint.nat v.internal'.lastExecutedOpNum') := by
    rw [← Hmine.1]; exact VsrReplica.prefix_eq_take Hmb
  subst hmine_take
  icases Hfs' with ⟨#HsvF, #HcF, -⟩
  ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hblog
  ihave HI : (∃ (i le : w64) (tbl' : GMap w64 replica.ClientTableData),
      "i" ∷ i_ptr ↦ i ∗
      "Hr" ∷ rp ↦ ({ vf with internal' := { vf.internal' with lastExecutedOpNum' := le } } :
        replica.Replica) ∗
      "Htbl" ∷ vf.state'.ClientTable' ↦$ tbl' ∗
      "Hstore" ∷ P (storeOf (blog.take (uint.nat le))) ∗
      "#Hlin" ∷ VsrGhost.fact γ (.linPrefix (blog.take (uint.nat le))) ∗
      "#Htres" ∷ ([∗map] c ↦ d ∈ tbl', replica.tblOk γ c d) ∗
      "%Hle" ∷ ⌜uint.nat i = uint.nat le + 1 ∧ uint.nat le ≤ blog.length ∧
        replica.Covers tbl' (blog.take (uint.nat le)) ∧
        (le = v.internal'.lastExecutedOpNum' ∨ uint.nat le ≤ uint.nat bc)⌝ : IProp GF)
      $$ [i Hr Htbl Hstore]
  · iexists _, v.internal'.lastExecutedOpNum', tbl
    iframe i Hstore Hmlin Htres
    isplitl [Hr]
    · iExactEq Hr; rw [hvf]
    isplitl [Htbl]
    · iExactEq Htbl; rw [hvf]
    ipureintro
    have := Hmb.length_le
    refine ⟨?_, ?_, Htmine, Or.inl rfl⟩
    · have h1 := Hmine.1; rw [List.length_take] at h1
      have : uint.nat v.internal'.lastExecutedOpNum' < 2 ^ 64 - 1 := by
        have : uint.nat v.internal'.lastExecutedOpNum' ≤ blog.length := by
          rw [List.length_take] at this; omega
        omega
      word
    · have h1 := Hmine.1; rw [List.length_take] at h1 this; omega
  have hvfC : vf.state'.CommitNumber' = bc := by rw [hvf]
  have hvfL : vf.state'.Logs' = bls := by rw [hvf]
  have hvfH : vf.srvhandler' = v.srvhandler' := by rw [hvf]
  wp_for HI
  wp_if_destruct
  · -- execute op i
    have hi1 : 1 ≤ uint.nat i := by omega
    have hile : uint.nat i ≤ uint.nat bc := by rw [hvfC] at Hif; word
    list_elem blog (uint.nat le) as ex
    wp_method_call
    wp_auto
    rw [hvfL]
    have hi63 : uint.nat i < 2 ^ 63 := by omega
    wp_apply (H.wp_OpAt bls DFrac.discard blog i ex (by word)
      (by rw [show sint.nat i - 1 = uint.nat le by word]; exact Hex_lookup)) $$ [Hblog]
    · iexact Hblog
    iintro -
    wp_auto
    rw [hvfH]
    wp_bind (App (Val #v.srvhandler') (Val #ex.op))
    unfold examples.vsrkv.srvOk
    iapply Hsrv $$ Hstore
    inext
    iintro Hstore
    wp_auto
    have hlk : blog[sint.nat i - 1]? = some ex := by
      rw [show sint.nat i - 1 = uint.nat le by word]; exact Hex_lookup
    wp_method_call
    wp_auto
    rw [hvfL]
    wp_apply (H.wp_ClientIDAt bls DFrac.discard blog i ex (by word) hlk) $$ [Hblog]
    · iexact Hblog
    iintro -
    wp_auto
    wp_method_call
    wp_auto
    rw [hvfL]
    wp_apply (H.wp_RequestIDAt bls DFrac.discard blog i ex (by word) hlk) $$ [Hblog]
    · iexact Hblog
    iintro -
    wp_auto_lc 1
    have hle_bc : uint.nat le < uint.nat bc := by omega
    have hml : blog.take (uint.nat le) <+: blog.take (uint.nat bc) :=
      VsrReplica.take_prefix_of_le blog (by omega)
    have hlen_m : (blog.take (uint.nat le)).length = uint.nat le := by
      rw [List.length_take]; omega
    have hex' : (blog.take (uint.nat bc))[(blog.take (uint.nat le)).length]? = some ex := by
      rw [hlen_m, List.getElem?_take, if_pos hle_bc]; exact Hex_lookup
    obtain ⟨hout, htk⟩ := VsrReplica.outOf_lin hml ex hex'
    rw [hlen_m] at hout htk
    imod VsrReplica.ghost_lin' γ (blog.take (uint.nat bc)) (blog.take (uint.nat le))
      (uint.nat le + 1) ex (by rw [hlen_m]) hml (by simpa [hlen_m] using hex') 0 (uint.nat w)
      $$ Hlc1 Hsys HregI HcF Hlin with ⟨#Hlin', #Hrep'⟩
    rw [hout, htk]
    wp_apply (replica.wp_recordResult rp _ tbl' (W64 ex.cid) (W64 ex.req)
      (handle (storeOf (blog.take (uint.nat le))) ex.op).2) $$ [Hr Htbl] as ⟨Hr, Htbl⟩
    · iframe Hr; iExactEq Htbl; rfl
    have hexb : ex ∈ blog := List.mem_of_getElem? Hex_lookup
    obtain ⟨hcb, hqb⟩ := Hlb ex hexb
    ihave #Htres' := replica.tblOk_recRes γ tbl' (W64 ex.cid) (W64 ex.req)
      (handle (storeOf (blog.take (uint.nat le))) ex.op).2 0 $$ [Htres Hrep']
    · iframe Htres
      rw [show uint.nat (W64 ex.req) = ex.req by word, show uint.nat (W64 ex.cid) = ex.cid by word]
      iexact Hrep'
    wp_for_post
    iframe
    iexists (i + W64 1), i, _
    have htki : blog.take (uint.nat i) = blog.take (uint.nat le) ++ [ex] := by
      rw [show uint.nat i = uint.nat le + 1 by omega]
      exact VsrReplica.take_succ_eq blog _ ex Hex_lookup
    rw [htki, VsrReplica.storeOf_append_one]
    iframe Hr Htbl Hstore Hlin' Htres' i
    ipureintro
    refine ⟨by word, ?_, ?_, ?_⟩
    · omega
    · exact replica.covers_recRes tbl' _ ex _ hcb hqb Hle.2.2.1
    · right; omega
  -- after the execution loop: the executed prefix reaches the commit number
  have hlebc : uint.nat bc ≤ uint.nat le := by rw [hvfC] at Hif; word
  wp_apply (wp_map_make1 (K := w64) (V := replica.PendingPrepareOK)) as %pkm Hpkm
  obtain ⟨vF, hvF⟩ : ∃ vF : replica.Replica, vF = { vf with internal' := { vf.internal' with
      lastExecutedOpNum' := le, pendingPOKs' := pkm } } := ⟨_, rfl⟩
  ihave Hr : rp ↦ vF $$ [Hr]
  · iExactEq Hr; rw [hvF]
  have hvFC : vF.state'.CommitNumber' = bc := by rw [hvF, hvf]
  have hvFL : vF.state'.Logs' = bls := by rw [hvF, hvf]
  have hvFO : vF.state'.OpNum' = bo := by rw [hvF, hvf]
  have hvFT : vF.state'.ClientTable' = v.state'.ClientTable' := by rw [hvF, hvf]
  have hvFI : vF.state'.ID' = v.state'.ID' := by rw [hvF, hvf]
  have hvFV : vF.state'.ViewNumber' = w := by rw [hvF, hvf]
  have hvFS : vF.state'.Status' = W64 0 := by rw [hvF, hvf]
  have hvFP : vF.internal'.pendingPOKs' = pkm := by rw [hvF]
  have hnp : replica.IsNormalPrimary n vF r := by
    refine ⟨by simp [replica.statusOf, hvFS], ?_⟩
    rw [hvFV]; exact hprim
  ihave #Hemp : ([∗map] k ↦ e ∈ (∅ : GMap w64 replica.PendingPrepareOK),
      replica.pokOk γ n tcp vF r k e) $$ []
  · iapply (BI.BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
  ihave HI : (∃ (j : w64) (tbl2 : GMap w64 replica.ClientTableData)
      (pk2 : GMap w64 replica.PendingPrepareOK),
      "i" ∷ i_ptr ↦ j ∗ "Hr" ∷ rp ↦ vF ∗
      "Htbl" ∷ vF.state'.ClientTable' ↦$ tbl2 ∗
      "#Htres" ∷ ([∗map] c ↦ d ∈ tbl2, replica.tblOk γ c d) ∗
      "Hpk" ∷ pkm ↦$ pk2 ∗ "Hpks" ∷ ([∗map] k ↦ e ∈ pk2, replica.pokOk γ n tcp vF r k e) ∗
      "%Hj" ∷ ⌜uint.nat bc + 1 ≤ uint.nat j ∧ uint.nat j ≤ blog.length + 1 ∧
        replica.Covers tbl2 (blog.take (uint.nat le)) ∧
        replica.Covers tbl2 (blog.take (uint.nat j - 1))⌝ : IProp GF)
      $$ [i Hr Htbl Hpkm]
  · iexists _, tbl', ∅
    iframe i Hr Htres Hpkm Hemp
    isplitl [Htbl]
    · iExactEq Htbl; rw [hvF]
    ipureintro
    refine ⟨by word, by word, Hle.2.2.1, ?_⟩
    rw [show uint.nat (vf.state'.CommitNumber' + W64 1) - 1 = uint.nat bc by rw [hvfC]; word]
    exact replica.covers_prefix tbl' (VsrReplica.take_prefix_of_le blog hlebc) Hle.2.2.1
  wp_for HI
  rw [hvFO]
  wp_if_destruct
  · -- seed op j
    have hj1 : 1 ≤ uint.nat j := by omega
    have hjl : uint.nat j ≤ blog.length := by rw [← Hbol]; word
    list_elem blog (uint.nat j - 1) as ej
    have hlk : blog[sint.nat j - 1]? = some ej := by
      rw [show sint.nat j - 1 = uint.nat j - 1 by word]; exact Hej_lookup
    wp_method_call
    wp_auto
    rw [hvFL]
    wp_apply (H.wp_ClientIDAt bls DFrac.discard blog j ej (by word) hlk) $$ [Hblog]
    · iexact Hblog
    iintro -
    wp_auto
    wp_method_call
    wp_auto
    rw [hvFL]
    wp_apply (H.wp_RequestIDAt bls DFrac.discard blog j ej (by word) hlk) $$ [Hblog]
    · iexact Hblog
    iintro -
    wp_auto
    wp_apply (replica.wp_recordRequest rp vF tbl2 (W64 ej.cid) (W64 ej.req)) $$ [Hr Htbl]
      as ⟨Hr, Htbl⟩
    · iframe
    imod VsrReplica.ghost_fact' γ n r _ [] (.msg (.prepareOK (uint.nat w) (uint.nat j) r))
      (fun s hs hsn hrp _ => by
        have := VsrModel.prepareOK_own s hs r (uint.nat j) (hsn ▸ hr3) (by rw [hrp]; left; rfl)
          (by rw [hrp]; exact hjl)
        rw [hrp] at this; exact this)
      $$ Hsize Hsys Hrep Hnil with ⟨Hrep, #Hpok⟩
    wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %rm Hrm
    wp_apply wp_mapInsert $$ Hrm as Hrm
    rw [hvFP]
    wp_apply wp_mapInsert $$ Hpk as Hpk
    have hejb : ej ∈ blog := List.mem_of_getElem? Hej_lookup
    obtain ⟨hcb, hqb⟩ := Hlb ej hejb
    ihave #Htres2 := replica.tblOk_recReq γ tbl2 (W64 ej.cid) (W64 ej.req) $$ Htres
    ihave Hpe : replica.pokOk γ n tcp vF r j
        ⟨zero_val ipv4port.IPv4Port, zero_val events.Request, rm⟩ $$ [Hrm]
    · unfold replica.pokOk
      simp only [hnp, _root_.decide_true, ↓reduceIte]
      iexists _
      iframe Hrm
      isplitl []
      · iright; ipureintro; rfl
      iapply (BI.BigSepM.bigSepM_insert (M := GMap w64) (h := rfl)).2
      isplitl []
      · rw [hvFV, hvFI, Hid.1]; iexact Hpok
      iapply (BI.BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
    ihave Hpks := BI.BigSepM.bigSepM_insert_elim $$ Hpe Hpks
    wp_for_post
    iframe
    iexists (j + W64 1), _, _
    iframe Hr Htbl Htres2 Hpk Hpks i
    ipureintro
    have htkj : blog.take (uint.nat j) = blog.take (uint.nat j - 1) ++ [ej] := by
      rw [show uint.nat j = uint.nat j - 1 + 1 by omega]
      rw [VsrReplica.take_succ_eq blog _ ej Hej_lookup]; simp
    refine ⟨by word, by word, ?_, ?_⟩
    · exact replica.covers_prefix _ (List.prefix_append _ _)
        (replica.covers_recReq tbl2 _ ej hcb hqb Hj.2.2.1)
    · rw [show uint.nat (j + W64 1) - 1 = uint.nat j by word, htkj]
      exact replica.covers_recReq tbl2 _ ej hcb hqb Hj.2.2.2
  -- the end: the replica is the normal primary of `w`
  have hjend : uint.nat j - 1 = blog.length := by
    have : ¬ uint.Z j ≤ uint.Z bo := by simpa using Hif
    have : uint.nat j = uint.nat bo + 1 := by have := Hj.2.1; rw [← Hbol] at this; word
    omega
  have hcov : replica.Covers tbl2 blog := by
    have := Hj.2.2.2; rwa [hjend, List.take_length] at this
  have hlelen : uint.nat le ≤ blog.length := Hle.2.1
  -- the executed prefix's commitment
  ihave #Hmc : (∃ mw' : Nat, ⌜mw' ≤ uint.nat w⌝ ∗
      VsrGhost.fact γ (.committedBy mw' (blog.take (uint.nat le)))) $$ []
  · rcases Hle.2.2.2 with hle0 | hle1
    · iexists mw
      rw [hle0]
      iframe Hmcom
      ipureintro
      have hl := hmw
      simp only [replica.repOf] at hl Hlnv hvle
      omega
    · have : uint.nat le = uint.nat bc := by omega
      iexists (uint.nat w)
      rw [this]
      iframe HcF
      ipureintro; omega
  icases Hmc with ⟨%mw', %Hmw', #Hmc⟩
  -- the selected log's capacity
  obtain ⟨kb, xb, hkb, hxb⟩ := Hfnd rfl
  ihave Hcapb := (BI.BigSepM.bigSepM_lookup (M := GMap w64)
    (Φ := fun _ x => ownSliceCap log.Log x.Logs' (DFrac.own 1)) hkb) $$ Hcaps
  rw [hxb]
  -- the pending DoViewChanges: fewer are live
  ihave Hdvs := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.dvOk_mono γ v vF k e' (by
      unfold replica.Live; intro hl
      rcases hl with hl | ⟨hl, hs⟩
      · left; rw [hvFV] at hl; word
      · simp [replica.statusOf, hvFS] at hs)) $$ Hdvs
  ihave Hdvs := (BI.BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun k e' => replica.dvOk γ vF k e') Hde).2 $$ [Hdvs]
  · iframe Hdvs
    unfold replica.dvOk
    simp only [show ¬ replica.Live vF w by
      unfold replica.Live; rw [hvFV]; simp [replica.statusOf, hvFS], _root_.decide_false,
      Bool.false_eq_true, ↓reduceIte]
    itrivial
  -- the get-state timer is unset (the replica was changing views)
  ihave Hgst : replica.gstOk n vF r $$ [Hgst]
  · unfold replica.gstOk
    icases Hgst with (%Hn | ⟨-, %Hn⟩)
    · ileft; ipureintro; rw [hvF, hvf]; exact Hn
    · exfalso; simp [replica.statusOf, Hst1] at Hn
  iapply HΦ
  iexists vF, blog
  iframe Hr
  isplitl [Hsender Hrep Hcapb Hstore Htbl Hpk Hpks Hsv Hsvs Hdv Hdvs Hvct Hct Hgst]
  · unfold replica.repInv
    iexists blog, blog.take (uint.nat le), uint.nat w, mw', me, C, F, P, ms, tbl2, pk2, sv, dv,
      vst, cst, n
    have hrepF : replica.repOf vF blog =
        { replica.repOf v lg with view := uint.nat w, status := .normal, log := blog } := by
      simp [replica.repOf, hvFV, hvFS, replica.statusOf]; rw [hvF, hvf]
    have e1 : vF.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hvF, hvf]
    have e2 : vF.network' = v.network' := by rw [hvF, hvf]
    have e3 : vF.time' = v.time' := by rw [hvF, hvf]
    have e4 : vF.logger' = v.logger' := by rw [hvF, hvf]
    have e5 : vF.srvhandler' = v.srvhandler' := by rw [hvF, hvf]
    have e6 : vF.internal'.sq' = v.internal'.sq' := by rw [hvF, hvf]
    have e8 : vF.internal'.pendingStartViewChange' = v.internal'.pendingStartViewChange' := by
      rw [hvF, hvf]
    have e9 : vF.internal'.pendingDoViewChange' = v.internal'.pendingDoViewChange' := by
      rw [hvF, hvf]
    have e10 : vF.internal'.viewChangeTimer' = v.internal'.viewChangeTimer' := by rw [hvF, hvf]
    have e11 : vF.internal'.commitTimer' = v.internal'.commitTimer' := by rw [hvF, hvf]
    have e12 : vF.internal'.lastExecutedOpNum' = le := by rw [hvF]
    rw [hrepF, e1, e2, e3, e4, e5, e6, e8, e9, e10, e11, e12, hvFL, hvFO, hvFC, hvFP, hvFT,
      hvFI]
    rw [hvFT] at *
    iFrameNamed
    iframe Hblog Hcapb HcF Hlin Hmc
    ipureintro
    have hnorm : replica.statusOf vF.state'.Status' = .normal := by
      simp [replica.statusOf, hvFS]
    refine ⟨Hid, Hmslen, Hnet, Htime, ?_⟩
    refine ⟨by simp [replica.StatusOk, hvFS], fun h => ?_, Hbol, ⟨Hbcl, by rw [hvFV]; exact Nat.le_refl _⟩,
      ⟨by rw [List.length_take]; omega, List.take_prefix _ _, ?_⟩, Hj.2.2.1, fun _ => hcov⟩
    · rw [hnorm] at h; cases h
    · simp only [replica.mineView, hnorm, hvFV]; simp; exact Hmw'
  isplitr
  · ipureintro; exact ⟨by rw [hvF, hvf], by rw [hvF, hvf], by rw [hvF, hvf]⟩
  rw [hvFL, hvFV, hvFO, hvFC, hvFI, Hbol, Hid.1]
  iframe Hblog HsvF

theorem replica.wp_onDoViewChange (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (x : events.DoViewChange) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ replica.dvcOk γ x.ViewNum' x.ReplicaID' x }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onDoViewChange"))
        (Val #src)) (Val #x))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, Hx⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (H.wp_String_ptr src_ptr (DFrac.own 1) src) $$ [src] as src
  · iexact src
  wp_log
  wp_apply H.wp_Reset $$ [Hvct] as Hvct
  · iexact Hvct
  wp_apply (replica.wp_primaryForView rp v ms n (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms; ipureintro; exact Hmslen
  try wp_auto
  wp_if_destruct
  rotate_left
  · -- not the primary of the view
    wp_log
    close_own
  wp_if_destruct
  rotate_left
  · -- not in view change
    wp_log
    close_own
  wp_if_destruct
  · -- an old view
    wp_log
    close_own
  have hlive : replica.Live v x.ViewNum' := by
    unfold replica.Live replica.statusOf
    rename_i Hlt _ _
    by_cases heq : v.state'.ViewNumber' = x.ViewNum'
    · right; simp_all
    · left; have : v.state'.ViewNumber' ≠ x.ViewNum' := heq
      have : uint.Z v.state'.ViewNumber' ≠ uint.Z x.ViewNum' := fun h => this (by word)
      word
  wp_apply wp_map_lookup2 $$ Hdv as Hdv
  wp_join iprop(∃ (dv' : GMap w64 replica.PendingDoViewChange) (e : replica.PendingDoViewChange),
      v.internal'.pendingDoViewChange' ↦$ dv' ∗ ⌜dv' !! x.ViewNum' = some e⌝ ∗
      ([∗map] w ↦ e ∈ dv', replica.dvOk γ v w e) ∗ rp ↦ v ∗ r_ptr ↦ rp ∗ ev_ptr ↦ x)
    with [Hdv Hdvs Hr r ev] as ⟨%dv', %e, Hdv, %Hde, Hdvs, Hr, r, ev⟩
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp Hif
    iexists dv, e
    iframe Hdv Hdvs Hr r ev
    ipureintro; exact he
  · have hnone : dv !! x.ViewNum' = none := by simpa using Hif
    wp_apply (wp_map_make1 (K := w64) (V := events.DoViewChange)) as %m Hm
    wp_apply wp_mapInsert $$ Hdv as Hdv
    wp_join_done
    iexists _, _
    iframe Hdv Hr r ev
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    iapply (BigSepM.bigSepM_insert hnone).2
    iframe Hdvs
    unfold replica.dvOk
    simp only [hlive, _root_.decide_true, ↓reduceIte]
    iexists ∅
    iframe Hm
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    iempintro
  ihave ⟨He, Hdvs⟩ := (BigSepM.bigSepM_delete Hde).1 $$ Hdvs
  ihave He : iprop(∃ rsp : GMap w64 events.DoViewChange, e.Responses' ↦$ rsp ∗
      [∗map] rid ↦ y ∈ rsp, replica.dvcOk γ x.ViewNum' rid y) $$ [He]
  · unfold replica.dvOk
    simp only [hlive, _root_.decide_true, ↓reduceIte]
    iexact He
  icases He with ⟨%rsp, Hrsp, Hrsps⟩
  wp_apply wp_map_lookup1 $$ Hdv as Hdv
  simp only [Hde, Option.getD_some]
  wp_apply wp_mapInsert $$ Hrsp as Hrsp
  ihave Hrsps := BigSepM.bigSepM_insert_elim $$ Hx Hrsps
  ihave %Hmlen := ownSlice_len $$ Hms
  wp_apply wp_map_lookup1 $$ Hdv as Hdv
  simp only [Hde, Option.getD_some]
  wp_apply wp_map_len_lt $$ Hrsp as ⟨Hrsp, %Hsz⟩
  obtain ⟨h3, hn63⟩ := replica.len_of_slice _ n (by rw [← Hmslen]; exact Hmlen)
  rw [h3]
  wp_if_destruct
  rotate_left
  · -- no majority yet
    ihave He : replica.dvOk γ v x.ViewNum' e $$ [Hrsp Hrsps]
    · unfold replica.dvOk
      simp only [hlive, _root_.decide_true, ↓reduceIte]
      iexists (<[x.ReplicaID' := x]> rsp)
      iframe Hrsp
      iexact Hrsps
    ihave Hdvs := (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun w e => replica.dvOk γ v w e) Hde).2 $$ [He Hdvs]
    · iframe
    iapply HΦ
    iexists v
    iframe Hr
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv', vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  have hsz2 : n < 2 * GMap.size (<[x.ReplicaID' := x]> rsp) :=
    replica.maj_of_sdiv n _ hn63 (by word) Hif
  wp_log
  wp_apply (replica.wp_finalizeViewChange H rp γ r tcp v x.ViewNum') $$
      [-HΦ r ev] as ⟨%v', %lg', Hr, Hinv, %Hsame, #Hlog', #HsvF⟩
  · iframe Hr
    unfold replica.finPre
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv', vst, cst, e,
      (<[x.ReplicaID' := x]> rsp), n
    iFrameNamed
    ipureintro
    rename_i Hif1 Hif2 Hif3
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog,
      Hde, ⟨Hif1, Hif2, by word, hsz2⟩⟩
  iclear Hms Haddrs HisTCP Hprotos Hlogger Hsrv Hcodec Hkit Hsys HregI Hsq Hlog Hcfact Hmlin
    Hmcom Htres
  iNamed Hinv
  ihave %Hmlen2 := ownSlice_len $$ Hms
  ihave HI : (∃ (i : w64) (mem : ipv4port.IPv4Port) (mi : w64),
      "i" ∷ i_ptr ↦ i ∗ "member" ∷ member_ptr ↦ mem ∗ "mi" ∷ mi_ptr ↦ mi ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i member mi]
  · iexists _, _, _; iframe; ipureintro; word
  have h3' : v'.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen2).1
  wp_for HI
  rw [h3']
  wp_if_destruct
  · have hi3 : sint.nat i < ms.length := by
      have := (replica.len_of_slice _ _ Hmlen2).2; rw [Hmslen] at this ⊢; word
    list_elem ms (sint.nat i) as m
    rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v'.state'.ClusterMembers'.len by
      rw [h3']; word)]
    wp_apply (wp_load_slice_index _ (sint.Z i) ms _ m (by word)) $$ [Hms]
    · iframe Hms; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hm_lookup
    iintro -
    wp_auto
    wp_if_destruct
    · -- itself: continue
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
    wp_apply (H.wp_String_ptr member_ptr (DFrac.own 1) m) $$ [member] as member
    · iexact member
    wp_log
    ihave #Ham := BI.BigSepL.bigSepL_lookup Hm_lookup $$ Haddrs
    wp_apply (replica.wp_sendStartViewToBackup H rp v' γ tcp C F m lg') $$ [Hr Hsender]
      as %err ⟨Hr, Hsender, #Herr⟩
    · iframe Hr Hsender Ham Hlog' HsvF
      unfold replica.sendCtx
      iexists me
      iframe HisTCP Hprotos Hcodec Hkit Hsys
      ipureintro; exact Hnet
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
    | ok ii =>
      wp_auto
      wp_apply (H.wp_String_ptr member_ptr (DFrac.own 1) m) $$ [member] as member
      · iexact member
      wp_log
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
  wp_log
  iapply HΦ
  iexists v'
  iframe Hr
  iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
  iFrameNamed
  ipureintro
  exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
