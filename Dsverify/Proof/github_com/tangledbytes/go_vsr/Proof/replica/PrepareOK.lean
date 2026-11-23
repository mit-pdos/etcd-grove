/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/PrepareOK.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onPrepareOK`: the primary counts a valid PrepareOK of its view for an op it has; with a quorum
(two distinct replicas) the view's log up to the op is committed (`committed_of_prepareOKs`), and
it executes the ops up to it (`ghost_lin` at each), sends Commits, records the results and replies
to the clients.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Exec

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs

variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

set_option maxHeartbeats 1000000 in
theorem replica.wp_onPrepareOK (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (x : events.PrepareOK) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗
        VsrGhost.fact γ (.msg (.prepareOK (uint.nat x.ViewNum') (uint.nat x.OpNum')
          (uint.nat x.ReplicaID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onPrepareOK"))
        (Val #src)) (Val #x))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Hpf⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  ihave %Hmlen0 := ownSlice_len $$ Hms
  have hn63 : n < 2 ^ 63 := by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen0).2
  wp_auto
  wp_apply (H.wp_String_ptr from_ptr (DFrac.own 1) src) $$ [«from»] as «from»
  · iexact «from»
  wp_log
  wp_if_destruct
  rotate_left
  · wp_log
    close_own
  wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms; ipureintro; exact Hmslen
  wp_if_destruct
  rotate_left
  · wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
    · iframe Hr Hms; ipureintro; exact Hmslen
    wp_log
    close_own
  wp_if_destruct
  · wp_log
    close_own
  wp_if_destruct
  rotate_left
  · wp_log
    close_own
  wp_if_destruct
  · wp_log
    close_own
  rename_i Hst0 Hprim Hgt Hveq
  have Hle := Hif
  have hnp : replica.IsNormalPrimary n v r := by
    refine ⟨by simp [replica.statusOf, Hst0], ?_⟩
    rw [replica.primary_word _ _ hn63, ← Hprim]; exact Hid.1
  wp_apply wp_map_lookup2 $$ Hpk as Hpk
  wp_join iprop(∃ (pk' : GMap w64 replica.PendingPrepareOK) (e : replica.PendingPrepareOK),
      v.internal'.pendingPOKs' ↦$ pk' ∗ ⌜pk' !! x.OpNum' = some e⌝ ∗
      ([∗map] k ↦ e ∈ pk', replica.pokOk γ n tcp v r k e) ∗ rp ↦ v ∗ r_ptr ↦ rp ∗ pok_ptr ↦ x)
    with [Hpk Hpks Hr r pok] as ⟨%pk', %e, Hpk, %Hpe, Hpks, Hr, r, pok⟩
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp Hif
    iexists pk, e
    iframe Hpk Hpks Hr r pok
    ipureintro; exact he
  · have hnone : pk !! x.OpNum' = none := by simpa using Hif
    wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %m Hm
    wp_apply wp_mapInsert $$ Hpk as Hpk
    wp_join_done
    iexists _, _
    iframe Hpk Hr r pok
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    iapply (BI.BigSepM.bigSepM_insert hnone).2
    iframe Hpks
    unfold replica.pokOk
    simp only [hnp, _root_.decide_true, ↓reduceIte]
    iexists ∅
    iframe Hm
    isplitl []
    · iright; ipureintro; rfl
    iapply (BI.BigSepM.bigSepM_empty (PROP := IProp GF)).2; iempintro
  ihave ⟨He, Hpks⟩ := (BigSepM.bigSepM_delete Hpe).1 $$ Hpks
  ihave He : iprop(∃ rs : GMap w64 Unit, e.Responses' ↦$ rs ∗
      (network.addrOk tcp e.ClientAddr' ∨ ⌜e.ClientAddr'.str' = []⌝) ∗
      [∗map] j ↦ _u ∈ rs, VsrGhost.fact γ (.msg (.prepareOK (uint.nat v.state'.ViewNumber')
        (uint.nat x.OpNum') (uint.nat j)))) $$ [He]
  · unfold replica.pokOk
    simp only [hnp, _root_.decide_true, ↓reduceIte]
    iexact He
  icases He with ⟨%rs, Hrs, #Hca, Hrsf⟩
  wp_apply wp_map_lookup1 $$ Hpk as Hpk
  simp only [Hpe, Option.getD_some]
  wp_apply wp_mapInsert $$ Hrs as Hrs
  ihave Hrsf := BI.BigSepM.bigSepM_insert_elim (M := GMap w64)
    (Φ := fun j (_u : Unit) => VsrGhost.fact γ (.msg (.prepareOK (uint.nat v.state'.ViewNumber')
      (uint.nat x.OpNum') (uint.nat j)))) $$ [] Hrsf
  · rw [← Hveq]; iexact Hpf
  ihave %Hmlen := ownSlice_len $$ Hms
  wp_apply wp_map_lookup1 $$ Hpk as Hpk
  simp only [Hpe, Option.getD_some]
  wp_apply wp_map_len_lt $$ Hrs as ⟨Hrs, %Hsz⟩
  have h3 : v.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
  rw [h3]
  wp_if_destruct
  rotate_left
  · -- no quorum yet
    ihave He : replica.pokOk γ n tcp v r x.OpNum' e $$ [Hrs Hrsf]
    · unfold replica.pokOk
      simp only [hnp, _root_.decide_true, ↓reduceIte]
      iexists _
      iframe Hrs Hca Hrsf
    ihave Hpks := (BI.BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun k e' => replica.pokOk γ n tcp v r k e') Hpe).2 $$ [He Hpks]
    · iframe
    iapply HΦ
    iexists v
    iframe Hr
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk', sv, dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  -- a quorum: the responses' keys, more than half of the replicas, each a valid PrepareOK of
  -- this view for the op
  have hmaj : n < 2 * GMap.size (<[x.ReplicaID' := ()]> rs) :=
    replica.maj_of_sdiv n _ hn63 Hsz Hif
  have hop : uint.nat x.OpNum' ≤ lg.length := by rw [← Hopnum]; word
  ihave #Hfab := replica.keyIds_facts (<[x.ReplicaID' := ()]> rs)
    (fun j => Fact.msg (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat x.OpNum') j)) γ
    $$ Hrsf
  -- the view's log (the primary's) up to the op is committed
  imod VsrReplica.ghost_fact' γ n r _ _
    (.committedBy (uint.nat v.state'.ViewNumber') (lg.take (uint.nat x.OpNum')))
    (fun s hs hsn hrp hf => by
      have hQ : ∀ a ∈ replica.keyIds (<[x.ReplicaID' := ()]> rs),
          MsgValid s (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat x.OpNum') a) :=
        fun a ha => hf _ (List.mem_map_of_mem ha)
      have hq : Quorum s.n (replica.keyIds (<[x.ReplicaID' := ()]> rs)) :=
        ⟨replica.keyIds_nodup _, fun a ha => (hQ a ha).1,
          by rw [replica.keyIds_length, hsn]; exact hmaj⟩
      have hn : (s.reps r).status = .normal := by rw [hrp]; exact hnp.1
      have hp : primary s.n (s.reps r).view = r := by rw [hrp, hsn]; exact hnp.2
      have hL := VsrReplica.primary_vlog s hs r (hsn ▸ Hid.2) hn hp
      rw [hrp] at hL
      exact VsrModel.committedBy_of_in s _ _ _ (Nat.le_refl _)
        (VsrModel.committed_of_prepareOKs s hs _ _ _ lg hL hop hq hQ))
    $$ Hsize Hsys Hrep Hfab with ⟨Hrep, #Hcom⟩
  wp_log
  -- the pending PrepareOKs, whole again
  ihave He : replica.pokOk γ n tcp v r x.OpNum' e $$ [Hrs Hrsf]
  · unfold replica.pokOk
    simp only [hnp, _root_.decide_true, ↓reduceIte]
    iexists _
    iframe Hrs Hca Hrsf
  ihave Hpks := (BI.BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun k e' => replica.pokOk γ n tcp v r k e') Hpe).2 $$ [He Hpks]
  · iframe
  have hr3 : r < n := Hid.2
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r _ [] (lg.length ≤ 6 * 2 ^ 28)
    (fun s hs hsn hrp _ => by
      have := VsrModel.repLog_length_le s hs r (hsn ▸ hr3); rw [hrp] at this; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, %Hblen⟩
  ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hlog
  have hmw : mw ≤ uint.nat v.state'.ViewNumber' := by
    have := Hmine.2.2; simpa [replica.mineView, replica.statusOf, Hst0] using this
  have hmine_take : mine = lg.take (uint.nat v.internal'.lastExecutedOpNum') := by
    rw [← Hmine.1]; exact VsrReplica.prefix_eq_take Hmine.2.1
  subst hmine_take
  ihave HI : (∃ (i cn le : w64) (tbl' : GMap w64 replica.ClientTableData)
      (pk2 : GMap w64 replica.PendingPrepareOK) (cwI mwI : Nat),
      "i" ∷ i_ptr ↦ i ∗
      "Hr" ∷ rp ↦ replica.withExec v cn le ∗
      "Htbl" ∷ v.state'.ClientTable' ↦$ tbl' ∗
      "Hpk" ∷ v.internal'.pendingPOKs' ↦$ pk2 ∗
      "Hpks" ∷ ([∗map] k ↦ e ∈ pk2, replica.pokOk γ n tcp v r k e) ∗
      "Hstore" ∷ P (storeOf (lg.take (uint.nat le))) ∗
      "#Hlin" ∷ VsrGhost.fact γ (.linPrefix (lg.take (uint.nat le))) ∗
      "#Htres" ∷ ([∗map] c ↦ d ∈ tbl', replica.tblOk γ c d) ∗
      "#Hcf" ∷ VsrGhost.fact γ (.committedBy cwI (lg.take (uint.nat cn))) ∗
      "#Hmc" ∷ VsrGhost.fact γ (.committedBy mwI (lg.take (uint.nat le))) ∗
      "%Hle" ∷ ⌜uint.nat i = uint.nat le + 1 ∧ uint.nat le ≤ lg.length ∧
        uint.nat cn ≤ lg.length ∧ cwI ≤ uint.nat v.state'.ViewNumber' ∧
        mwI ≤ uint.nat v.state'.ViewNumber' ∧
        replica.Covers tbl' (lg.take (uint.nat le)) ∧ replica.Covers tbl' lg⌝ : IProp GF)
      $$ [i Hr Htbl Hpk Hpks Hstore]
  · iexists _, v.state'.CommitNumber', v.internal'.lastExecutedOpNum', tbl, pk', cw, mw
    iframe i Htbl Hpk Hpks Hstore Hmlin Htres Hcfact Hmcom
    isplitl [Hr]
    · iExactEq Hr; rfl
    ipureintro
    have : uint.nat v.internal'.lastExecutedOpNum' ≤ lg.length := by
      have h1 := Hmine.1; rw [List.length_take] at h1; omega
    refine ⟨?_, this, Hcommit.1, Hcommit.2, hmw, Htmine, Htlog hnp⟩
    word
  wp_for HI
  wp_if_destruct
  · -- execute op i
    obtain ⟨Hi, Hlel, Hcnl, Hcw, Hmw, Hcov1, Hcov2⟩ := Hle
    have hile : uint.nat i ≤ uint.nat x.OpNum' := by word
    have hi1 : 1 ≤ uint.nat i := by omega
    have hlt : uint.nat le < lg.length := by omega
    list_elem lg (uint.nat le) as ex
    have hlk : lg[sint.nat i - 1]? = some ex := by
      rw [show sint.nat i - 1 = uint.nat le by word]; exact Hex_lookup
    wp_method_call
    wp_auto
    wp_apply (H.wp_OpAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_log
    wp_method_call
    wp_auto
    wp_apply (H.wp_OpAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_auto
    irename i => Hio
    wp_bind (App (Val #v.srvhandler') (Val #ex.op))
    unfold examples.vsrkv.srvOk
    iapply Hsrv $$ Hstore
    inext
    iintro Hstore
    wp_auto
    ihave Hr : rp ↦ replica.withExec v i i $$ [Hr]
    · iExactEq Hr; rfl
    -- the facts of op i: committed by the view, its Commit
    have hil : uint.nat i ≤ lg.length := by omega
    ihave #Hcom1 : ([∗list] f ∈ [Fact.committedBy (uint.nat v.state'.ViewNumber')
        (lg.take (uint.nat x.OpNum'))], VsrGhost.fact γ f) $$ []
    · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hcom
    imod VsrReplica.ghost_fact' γ n r _ _
      (.committedBy (uint.nat v.state'.ViewNumber') (lg.take (uint.nat i)))
      (fun s hs hsn hrp hf => by
        have h := hf _ (List.mem_singleton_self _)
        exact VsrModel.committedBy_prefix s _ _ _ (VsrReplica.take_prefix_of_le lg hile) h)
      $$ Hsize Hsys Hrep Hcom1 with ⟨Hrep, #Hci⟩
    ihave #Hci1 : ([∗list] f ∈ [Fact.committedBy (uint.nat v.state'.ViewNumber')
        (lg.take (uint.nat i))], VsrGhost.fact γ f) $$ []
    · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hci
    imod VsrReplica.ghost_fact' γ n r _ _
      (.msg (.commit (uint.nat v.state'.ViewNumber') (uint.nat i) (uint.nat v.state'.ID')))
      (fun s hs hsn hrp hf => by
        have hc := hf _ (List.mem_singleton_self _)
        have h := VsrModel.commit_own s hs r (uint.nat i) (hsn ▸ hr3)
          (by rw [hrp]; left; simp [replica.repOf, replica.statusOf, Hst0])
          (by rw [hrp]; exact hil) (by rw [hrp]; exact hc)
        rw [hrp, ← Hid.1] at h; exact h)
      $$ Hsize Hsys Hrep Hci1 with ⟨Hrep, #Hcmt⟩
    -- the Commits
    ihave %Hmlen2 := ownSlice_len $$ Hms
    ihave HJ : (∃ (j : w64) (mem : ipv4port.IPv4Port) (mi : w64),
        "i" ∷ i_ptr ↦ j ∗ "member" ∷ member_ptr ↦ mem ∗ "mi" ∷ mi_ptr ↦ mi ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF) $$ [i member mi]
    · iexists _, _, _; iframe; ipureintro; word
    wp_for HJ
    rw [h3]
    wp_if_destruct
    · have hj3 : sint.nat j < ms.length := by
        have := (replica.len_of_slice _ _ Hmlen).2; rw [Hmslen] at this ⊢; word
      list_elem ms (sint.nat j) as m
      rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.state'.ClusterMembers'.len by
        rw [h3]; word)]
      wp_apply (wp_load_slice_index _ (sint.Z j) ms _ m (by word)) $$ [Hms]
      · iframe Hms; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hm_lookup
      iintro -
      wp_auto
      wp_if_destruct
      · wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro; word
      ihave #Ham := BI.BigSepL.bigSepL_lookup Hm_lookup $$ Haddrs
      wp_apply (replica.wp_sendCommitToBackup H rp (replica.withExec v i i) γ tcp C F m i)
        $$ [Hr Hsender] as %err ⟨Hr, Hsender, #Herr⟩
      · iframe Hr Hsender Ham Hcmt
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
    wp_method_call
    wp_auto
    wp_apply (H.wp_ClientIDAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_auto
    wp_method_call
    wp_auto
    wp_apply (H.wp_RequestIDAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_auto_lc 1
    -- op i is linearized; its reply
    have hle_op : uint.nat le < uint.nat x.OpNum' := by omega
    have hml : lg.take (uint.nat le) <+: lg.take (uint.nat x.OpNum') :=
      VsrReplica.take_prefix_of_le lg (by omega)
    have hlen_m : (lg.take (uint.nat le)).length = uint.nat le := by
      rw [List.length_take]; omega
    have hex' : (lg.take (uint.nat x.OpNum'))[(lg.take (uint.nat le)).length]? = some ex := by
      rw [hlen_m, List.getElem?_take, if_pos hle_op]; exact Hex_lookup
    obtain ⟨hout, htk⟩ := VsrReplica.outOf_lin hml ex hex'
    rw [hlen_m] at hout htk
    imod VsrReplica.ghost_lin' γ (lg.take (uint.nat x.OpNum')) (lg.take (uint.nat le))
      (uint.nat le + 1) ex (by rw [hlen_m]) hml (by simpa [hlen_m] using hex')
      (uint.nat v.state'.ViewNumber') (uint.nat v.state'.ViewNumber')
      $$ Hlc1 Hsys HregI Hcom Hlin with ⟨#Hlin', #Hrep'⟩
    rw [hout, htk]
    wp_apply (replica.wp_recordResult rp _ tbl' (W64 ex.cid) (W64 ex.req)
      (handle (storeOf (lg.take (uint.nat le))) ex.op).2) $$ [Hr Htbl] as ⟨Hr, Htbl⟩
    · iframe Hr; iExactEq Htbl; rfl
    have hexb : ex ∈ lg := List.mem_of_getElem? Hex_lookup
    obtain ⟨hcb, hqb⟩ := Hlb ex hexb
    ihave #Htres' := replica.tblOk_recRes γ tbl' (W64 ex.cid) (W64 ex.req)
      (handle (storeOf (lg.take (uint.nat le))) ex.op).2 (uint.nat v.state'.ViewNumber')
      $$ [Htres Hrep']
    · iframe Htres
      rw [show uint.nat (W64 ex.req) = ex.req by word, show uint.nat (W64 ex.cid) = ex.cid by word]
      iexact Hrep'
    -- the pending entry of op i: its client's address
    ihave ⟨#Haddr, Hpks⟩ : ((network.addrOk tcp ((pk2 !! i).getD (zero_val _)).ClientAddr' ∨
        ⌜((pk2 !! i).getD (zero_val replica.PendingPrepareOK)).ClientAddr'.str' = []⌝) ∗
        [∗map] k ↦ e ∈ Std.delete pk2 i, replica.pokOk γ n tcp v r k e) $$ [Hpks]
    · cases hpi : pk2 !! i with
      | none =>
        rw [show Std.delete pk2 i = pk2 from GMap.delete_notin _ _ hpi]
        iframe Hpks
        iright; ipureintro; rfl
      | some e' =>
        ihave ⟨He', Hpks⟩ := (BigSepM.bigSepM_delete hpi).1 $$ Hpks
        iframe Hpks
        unfold replica.pokOk
        icases He' with ⟨%rs', -, #Hc', -⟩
        simp only [Option.getD_some]
        iexact Hc'
    wp_auto
    wp_apply wp_map_lookup1 $$ Hpk as Hpk
    wp_apply H.wp_String
    wp_log
    wp_apply wp_map_lookup1 $$ Hpk as Hpk
    wp_apply H.wp_String
    wp_join with [r Hr Hsender Hpk Hio res clientID reqID]
    · -- the reply to the client
      icases Haddr with (#Hca2 | %Hn)
      rotate_left
      · exfalso; simp [Hn] at Hif
      wp_apply wp_map_lookup1 $$ Hpk as Hpk
      ihave #Hrep2 : VsrGhost.fact γ (.msg (.reply (uint.nat (W64 ex.req)) (uint.nat (W64 ex.cid))
          (uint.nat (replica.withExec v i i).state'.ViewNumber')
          (handle (storeOf (lg.take (uint.nat le))) ex.op).2)) $$ []
      · rw [show uint.nat (W64 ex.req) = ex.req by word, show uint.nat (W64 ex.cid) = ex.cid by word]
        iexact Hrep'
      wp_apply (replica.wp_sendReplyToClient H rp (replica.withExec v i i) γ tcp C F _
          (W64 ex.cid) (W64 ex.req) _) $$ [Hr Hsender]
        as %err ⟨Hr, Hsender, #Herr⟩
      · iframe Hr Hsender Hca2 Hrep2
        unfold replica.sendCtx
        iexists me
        iframe HisTCP Hprotos Hcodec Hkit Hsys
        ipureintro; exact Hnet
      cases err with
      | nil =>
        wp_auto
        wp_join_done
      | ok ii =>
        wp_auto
        wp_apply wp_map_lookup1 $$ Hpk as Hpk
        wp_apply H.wp_String
        wp_apply wp_map_lookup1 $$ Hpk as Hpk
        wp_log
        wp_join_done
    wp_apply wp_mapDelete $$ Hpk as Hpk
    have htki : lg.take (uint.nat i) = lg.take (uint.nat le) ++ [ex] := by
      rw [Hi]; exact VsrReplica.take_succ_eq lg _ ex Hex_lookup
    wp_for_post
    iframe
    iexists (i + W64 1), i, i, _, _, uint.nat v.state'.ViewNumber', uint.nat v.state'.ViewNumber'
    rw [htki, VsrReplica.storeOf_append_one]
    iframe Hr Htbl Hstore Hlin' Htres' Hpk Hpks Hio Hci
    ipureintro
    refine ⟨by word, by omega, by omega, Nat.le_refl _, Nat.le_refl _,
      replica.covers_recRes tbl' _ ex _ hcb hqb Hcov1, replica.covers_recRes_mono _ _ _ _ _ Hcov2⟩
  · -- the end of the loop
    obtain ⟨Hi, Hlel, Hcnl, Hcw, Hmw, Hcov1, Hcov2⟩ := Hle
    ihave Hrep : VsrGhost.repOwn γ r (replica.repOf (replica.withExec v cn le) lg) $$ [Hrep]
    · iExactEq Hrep; rfl
    ihave Hgst : replica.gstOk n (replica.withExec v cn le) r $$ [Hgst]
    · iExactEq Hgst; rfl
    ihave Hpks : ([∗map] k ↦ e ∈ pk2, replica.pokOk γ n tcp (replica.withExec v cn le) r k e)
      $$ [Hpks]
    · iExactEq Hpks; rfl
    ihave Hdvs : ([∗map] w ↦ e ∈ dv, replica.dvOk γ (replica.withExec v cn le) w e) $$ [Hdvs]
    · iExactEq Hdvs; rfl
    iapply HΦ
    iexists replica.withExec v cn le
    iframe Hr
    iexists lg, lg.take (uint.nat le), cwI, mwI, me, C, F, P, ms, tbl', pk2, sv, dv, vst, cst, n
    iFrameNamed
    simp only [replica.withExec]
    iframe Hcf Hlin Hmc
    ipureintro
    refine ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, ⟨Hcnl, Hcw⟩,
      ⟨by rw [List.length_take]; omega, List.take_prefix _ _, ?_⟩, Hcov1, fun _ => Hcov2⟩
    simpa [replica.mineView, replica.statusOf, Hst0] using Hmw



end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
