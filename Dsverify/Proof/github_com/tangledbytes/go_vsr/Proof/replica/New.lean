/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/New.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`replica.New(cfg)`: parse the configured members (`FromHostPort`), sort them (`sort.Sort` through
`ipv4port.ByLess`'s sorter: a permutation), build the replica (the maps, `NewLogs`, the queue at
`replica.sqElem γ tcp`, the timers) and establish `replica.own` at the initial model state.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Pure
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Ghost
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Perennial.Proof.sort.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

omit [C : models_lab.jsoncodec.JsonCodec GF] in
/-- The parsed configured members are `addrOk`. -/
theorem replica.addrs_of_cfg (tcp : Loc) (γ : VsrGhost.Names) (me : GoString)
    (l : List ipv4port.IPv4Port) :
    network.isTCP (GF := GF) tcp γ me ∗ ([∗list] p ∈ l, ∃ a : GoString, ipv4port.ipCfg p a) ⊢
      [∗list] m ∈ l, network.addrOk tcp m := by
  induction l with
  | nil =>
    iintro -
    iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | cons x xs ih =>
    iintro ⟨#Ht, Hl⟩
    ihave ⟨⟨%a, #Ha⟩, Hl⟩ := (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl
    ihave %h := ipv4port.ipCfg_str x a $$ Ha
    iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl []
    · iapply network.addrOk_cfg tcp γ me x a h.1 h.2 $$ Ht
    iapply ih
    iframe Ht Hl

set_option maxHeartbeats 1000000 in
theorem replica.New.wp_proof
    (wp_FromHostPort : ipv4port.IPv4Port.FromHostPort.spec (GF := GF) (hG := hG))
    (wp_sorter : ipv4port.ByLess.sorter.spec (GF := GF) (hG := hG))
    (wp_NewLogs : log.NewLogs.spec (GF := GF) (hG := hG))
    (wp_QNew : queue.New.spec (GF := GF) (hG := hG))
    (wp_NewTimer : time.NewTimer.spec (GF := GF) (hG := hG)) :
    replica.New.spec (GF := GF) (hG := hG) := by
  intro F cfg γ N r tcp me dq ms P hid hr hms hN62 haddrs hnet htime
  wp_start as ⟨Hmem, #Hsrv, Hstore, #HisTCP, Hsender, #Hprotos, #Hlogger, Hrep, #Hsize, #Hsys,
    #HregI, #Hcodec, #Hkit⟩
  ihave %Hmlen := ownSlice_len $$ Hmem
  wp_auto
  wp_apply (wp_slice_make2 (V := ipv4port.IPv4Port) cfg.Members'.len) as %sl ⟨Hsl, Hslcap⟩
  · ipureintro; exact Hmlen.2
  obtain ⟨hlen3, hN63⟩ := replica.len_of_slice _ N (by rw [← hms]; exact Hmlen)
  rw [hlen3]
  rename_i ii_ptr
  ihave %Hsllen := ownSlice_len $$ Hsl
  have hsl3 : sl.len = W64 N := by
    have := Hsllen.1; simp at this; word
  ihave HI : (∃ (n : w64) (ps : List ipv4port.IPv4Port) (k : w64) (s : GoString),
      "i" ∷ i_ptr ↦ n ∗ "Hi0" ∷ ii_ptr ↦ k ∗ "v" ∷ v_ptr ↦ s ∗
      "Hsl" ∷ sl ↦* (ps ++ List.replicate (N - ps.length) (zero_val ipv4port.IPv4Port)) ∗
      "Hps" ∷ ([∗list] p ∈ ps, ∃ a : GoString, ipv4port.ipCfg p a) ∗
      "%Hn" ∷ ⌜sint.nat n = ps.length ∧ ps.length ≤ N ∧ 0 ≤ sint.Z n⌝ : IProp GF)
      $$ [-HΦ Hmem Hstore Hsender Hrep «$res0» «$res1» cfg Hslcap clustermembers]
  · iexists (W64 0), [], _, _
    iframe
    simp only [List.length_nil, Nat.sub_zero, List.nil_append]
    rw [show sint.nat (W64 (N : Int)) = N by word]
    iframe
    isplitl []
    · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    ipureintro; exact ⟨by decide, Nat.zero_le _, by decide⟩
  wp_for HI
  rw [hlen3]
  by_cases Hif : sint.Z n < sint.Z (W64 N)
  · simp only [decide_eq_true Hif, decide_true, ↓reduceIte, ite_true, decide_eq_true_eq]
    try wp_auto
    have hn3 : sint.nat n < ms.length := by rw [hms]; word
    list_elem ms (sint.nat n) as a
    rw [if_pos (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cfg.Members'.len by rw [hlen3]; word)]
    wp_apply (wp_load_slice_index _ (sint.Z n) ms _ a (by word)) $$ [Hmem]
    · iframe Hmem; ipureintro; rw [show (sint.Z n).toNat = sint.nat n by word]; exact Ha_lookup
    iintro Hmem
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len by rw [hsl3]; word)]
    have hlk : (ps ++ List.replicate (N - ps.length) (zero_val ipv4port.IPv4Port))[(sint.Z n).toNat]?
        = some (zero_val ipv4port.IPv4Port) := by
      have h3 : sint.nat n < N := by word
      rw [show (sint.Z n).toNat = ps.length by rw [← Hn.1]]
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_replicate]
      simp; omega
    ihave ⟨Hel, Hsl⟩ := ownSlice_elem_acc (sint.Z n) _ sl _ _ Hn.2.2 hlk $$ Hsl
    wp_apply (wp_FromHostPort _ _ a (haddrs a (List.mem_of_getElem? Ha_lookup)))
      $$ [Hel] as ⟨%p, Hel, #Hp⟩
    · iexact Hel
    ihave Hsl := Hsl $$ Hel
    wp_for_post
    iframe
    iexists _, ps ++ [p], _, _
    iframe
    have h3 : sint.nat n < N := by word
    have hset : (ps ++ List.replicate (N - ps.length) (zero_val ipv4port.IPv4Port)).set
        (sint.Z n).toNat p =
        ps ++ [p] ++ List.replicate (N - (ps ++ [p]).length) (zero_val ipv4port.IPv4Port) := by
      rw [show (sint.Z n).toNat = ps.length by rw [← Hn.1]]
      rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
      obtain ⟨kk, hk⟩ : ∃ kk, N - ps.length = kk + 1 := ⟨N - ps.length - 1, by omega⟩
      rw [hk, List.replicate_succ, List.set_cons_zero]
      simp only [List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.cons_append, List.nil_append]
      have hk' : N - (ps.length + (0 + 1)) = kk := by omega
      rw [hk']
    rw [hset]
    iframe
    isplitl []
    · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2
      iexists a; iexact Hp
    ipureintro
    simp only [List.length_append, List.length_cons, List.length_nil]
    refine ⟨by word, by omega, by word⟩
  simp only [decide_eq_false Hif, false_neq_true, decide_false, decide_true, ↓reduceIte,
    ite_true, ite_false, decide_eq_true_eq, Bool.false_eq_true]
  try wp_auto
  have hps3 : ps.length = N := by
    have : sint.nat n ≥ N := by word
    omega
  rw [hps3]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  try wp_auto
  ihave #Hsorter := wp_sorter sl $$ []
  · iPkgInit
  wp_apply (sort.wp_Sort (GF := GF) ⟨ipv4port.ByLess.ty, #sl⟩ (ipv4port.cfgList sl)
      ipv4port.portLt ipv4port.ByLess.swo ps) $$ [Hsl Hps] as %ps' Hpost
  · iframe Hsorter
    unfold ipv4port.cfgList
    isplitl [Hsl Hps]
    · isplitl [Hsl]
      · iExactEq Hsl; simp [hps3]
      iexact Hps
    ipureintro
    -- `sort.Sort` needs `ps.length ≤ 2 ^ 62` (replica-1: `New.spec` takes `n < 2 ^ 62`)
    omega
  iNamed Hpost
  unfold ipv4port.cfgList
  icases Hxs with ⟨Hsl, #Hps⟩
  have hps'3 : ps'.length = N := by rw [← Hperm.length_eq]; exact hps3
  ipersist Hsl
  ihave #Haddrs := replica.addrs_of_cfg tcp γ me ps' $$ [HisTCP Hps]
  · iframe HisTCP Hps
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_fact' γ N r _ _ (.committedBy 0 [])
    (fun s hs _ _ _ => VsrReplica.committedBy_nil s (VsrReplica.n_pos s hs) 0)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, #Hc0⟩
  imod VsrReplica.ghost_fact' γ N r _ _ (.linPrefix [])
    (fun s _ _ _ _ => List.nil_prefix) $$ Hsize Hsys Hrep Hnil with ⟨Hrep, #Hl0⟩
  wp_apply (wp_map_make1 (K := w64) (V := replica.ClientTableData)) as %tblm Htbl
  wp_apply wp_NewLogs as %lsl ⟨Hlogs, Hlcap⟩
  ihave Hlogs := log.ownLogs_persist _ _ _ $$ Hlogs
  imod Hlogs with #Hlogs
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := replica.PendingPrepareOK)) as %pkm Hpk
  wp_apply (wp_map_make1 (K := w64) (V := replica.PendingStartViewChange)) as %svm Hsv
  wp_apply (wp_map_make1 (K := w64) (V := replica.PendingDoViewChange)) as %dvm Hdv
  wp_apply (wp_QNew events.NetworkEvent.ty (replica.sqElem γ tcp)) as %q #Hq
  wp_apply (wp_NewTimer cfg.Time' cfg.HeartbeatTimeout' htime) as %ct Hct
  wp_apply (wp_NewTimer cfg.Time' (cfg.HeartbeatTimeout' * W64 2) htime) as %vct Hvct
  try wp_auto
  iapply HΦ
  iframe Hmem
  unfold replica.isReplica replica.own
  iexists _
  iframe «$r0»
  isplitr
  · ipureintro; rfl
  unfold replica.repInv
  iexists [], [], 0, 0, me, C, F, P, ps', ∅, ∅, ∅, ∅, interface.nil, interface.nil, N
  dsimp only
  ihave #Hms : sl ↦*□ ps' $$ [Hsl]
  · iexact Hsl
  ihave #Hsq := Hq
  ihave #Hlog := Hlogs
  ihave #Hcfact : VsrGhost.fact γ (Fact.committedBy 0 (List.take (uint.nat (W64 0)) [])) $$ []
  · simp only [List.take_nil]; iexact Hc0
  ihave #Hmlin := Hl0
  ihave #Hmcom := Hc0
  iFrameNamed
  isplitl []
  · ipureintro; exact ⟨hid, hr⟩
  isplitl []
  · ipureintro; exact hps'3
  isplitl []
  · ipureintro; exact hnet
  isplitl []
  · ipureintro; exact htime
  isplitl [Hrep]
  · iExactEq Hrep
    simp [replica.repOf, replica.statusOf, initRep]
  isplitl []
  · ipureintro; left; rfl
  isplitl []
  · ipureintro; intro h; simp [replica.statusOf] at h
  isplitl [Hlcap]
  · iexact Hlcap
  isplitl []
  · ipureintro; rfl
  isplitl []
  · ipureintro; simp
  isplitl []
  · ipureintro; simp
  isplitl [Hstore]
  · iExactEq Hstore; rfl
  isplitl []
  · ipureintro; intro e he; cases he
  isplitl []
  · ipureintro; intro _ e he; cases he
  isplitl []
  · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
  isplitl []
  · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
  isplitl []
  · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
  isplitl []
  · iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
  unfold replica.gstOk
  ileft; ipureintro; rfl

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
