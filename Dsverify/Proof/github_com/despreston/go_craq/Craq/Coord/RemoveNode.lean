/-
`cdr.RemoveNode(address)`: the tail is fenced (its token and cover come back) before it is
removed, and the new last replica is activated from it; another replica is removed and its
neighbors updated.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Reps
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Find
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Log

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogSpecs GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem wp_RemoveNode (cfg : Cfg GF) (c : Loc) (a : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
        isCoord cfg c }}
      (App (Val (c @!! go.GoType.PointerType coordinator.Coordinator.ty @!! go!"RemoveNode"))
        (Val #a))
    {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∨ models_lab.errAny err }} := by
  wp_start as #Hc
  unfold isCoord coordDef
  icases Hc with ⟨#Hctx, -, %Hbound, %f, #Htport, #Hfac, #Hmu⟩
  wp_alloc_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hlk⟩
  iNamed Hlk
  wp_auto
  wp_apply wp_findReplicaIndex cfg a sl rs (DFrac.own 1) $$ [Hsl] as %idx %found ⟨Hsl, %Hfound⟩
  · iframe Hsl; iexact Hnfs
  cases found
  · -- not found
    wp_auto
    wp_apply errors.wp_New_errorString as %e ⟨-, #He⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
      Hreps Hjoin Htok]
    · inext; iapply coordLock_pack cfg c sl rs ver hd tl Hwf; iframe; iexact Hnfs
    iapply HΦ; iright; iapply errMsg_errAny (msg := go!"unknown node")
    unfold net.rpc.errMsg
    iexists ⟨go.GoType.PointerType errors.errorString.ty, #e⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact errorString_isError
    iexact He
  obtain ⟨hidx0, rI, hrI, hrIa⟩ := Hfound rfl
  ihave %Hlen := ownSlice_len $$ Hsl
  simp only [List.length_map] at Hlen
  have hidxl : sint.nat idx < rs.length := (List.getElem?_eq_some_iff.mp hrI).1
  ihave ⟨#HerrE, #HerrL, #HerrD, #HerrV⟩ := coord_pkg_errs $$ Hpkg
  wp_auto
  wp_if_destruct
  · -- the last replica is never removed
    ihave ⟨%errL, #HerrLa, #HerrLm⟩ := newVar_errMsg _ _ $$ HerrL
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
      Hreps Hjoin Htok]
    · inext; iapply coordLock_pack cfg c sl rs ver hd tl Hwf; iframe; iexact Hnfs
    iapply HΦ; iright; iapply errMsg_errAny $$ HerrLm
  have hm2 : 2 ≤ rs.length := by
    have : rs.length ≠ 1 := by intro h; apply Hif; word
    omega
  wp_if_destruct
  · -- the tail: fenced, removed, the new last activated from it
    have hidx : sint.nat (sl.len - W64 1) = rs.length - 1 := by word
    rw [hidx] at hrI
    list_elem rs (rs.length - 2) as rP
    ihave ⟨Hpre, HT, -⟩ := (bigSepL_split_at _ rs (rs.length - 1) rI hrI).1 $$ Hreps
    ihave ⟨HTc, HTr⟩ := (connRole_last cfg rs _ rI (by omega)).1 $$ HT
    ihave #HnfT := nodeFacts_at cfg rs _ rI hrI $$ Hnfs
    have hb : 0 ≤ sint.Z (sl.len - W64 1) ∧ sint.Z (sl.len - W64 1) < sint.Z sl.len := ⟨hidx0, by word⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) (rs.map Rep.loc) (DFrac.own 1) rI.loc
      hidx0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro
      rw [show (sint.Z (sl.len - W64 1)).toNat = rs.length - 1 by word]
      exact locs_at rs _ rI hrI
    ihave Hm : metaPtr «$a1_ptr» (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩ $$ [«$a1»]
    · unfold metaPtr; iexact «$a1»
    wp_apply wp_sendMeta cfg c rI.loc «$a1_ptr» rI.addr rI.conn (DFrac.own 1)
      ⟨false, false, go!"", go!"", go!""⟩ ((true, go!"") : Role) $$ [HnfT HTc Hm HTr]
      as %err ⟨%bT, HTc, HTpost⟩
    · iframe HnfT HTc Hm
      isplitr
      · ipureintro; simp [metaAddrsOk]
      unfold sendPre
      cases rI.conn
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte]; iframe HTr; unfold updDep; simp only [Bool.false_eq_true, false_and, ↓reduceIte]; itrivial
    unfold sendPost
    icases HTpost with (⟨%Hok, HTpost⟩ | ⟨%HbT, #Herr⟩)
    · -- fenced: the token and the tail's cover
      obtain ⟨rfl, hTc, rfl⟩ := Hok
      unfold updPost
      simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte, _root_.and_self]
      icases HTpost with ⟨-, %L, Htok, #Hcov⟩
      wp_auto
      ihave %Hslwf := ownSlice_wf $$ Hsl
      have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (sl.len - W64 1) ∧
          sint.Z (sl.len - W64 1) ≤ sint.Z sl.cap := ⟨by word, by word, by word⟩
      simp only [hb2, ↓reduceIte]
      wp_auto
      have hb3 : 0 ≤ sint.Z (sl.len - W64 1 + W64 1) ∧ sint.Z (sl.len - W64 1 + W64 1) ≤ sint.Z sl.len ∧
          sint.Z sl.len ≤ sint.Z sl.cap := ⟨by word, by word, Hslwf.2⟩
      simp only [hb3, ↓reduceIte]
      wp_apply wp_slice_delete sl (rs.map Rep.loc) (sl.len - W64 1) ⟨hidx0, by word⟩ $$ [Hsl Hcap]
        as %sl' ⟨Hsl, Hcap⟩
      · iframe
      have hrs' : (rs.map Rep.loc).eraseIdx (sint.nat (sl.len - W64 1)) =
          (rs.take (rs.length - 1)).map Rep.loc := by
        rw [hidx, List.eraseIdx_eq_take_drop_succ, List.drop_of_length_le (by simp; omega),
          List.append_nil, List.map_take]
      rw [hrs']
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [interface.mkOk go.string #a]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %args_sl ⟨Hargs, -⟩
      wp_apply log.Printf.wp_proof _ _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hargs]
      · iframe
      iintro -
      wp_auto
      -- the new last replica `rP`
      unfold craqCtx
      icases Hctx with ⟨-, %Hctxp, -⟩
      have hm := hm2
      ihave %Hlen' := ownSlice_len $$ Hsl
      simp only [List.length_map, List.length_take] at Hlen'
      have hP' : (rs.take (rs.length - 1))[rs.length - 2]? = some rP := by
        rw [List.getElem?_take_of_lt (by omega)]; exact HrP_lookup
      have hpidx : sint.nat (sl.len - W64 1 - W64 1) = rs.length - 2 := by word
      have hb4 : 0 ≤ sint.Z (sl.len - W64 1 - W64 1) ∧ sint.Z (sl.len - W64 1 - W64 1) < sint.Z sl'.len :=
        ⟨by word, by word⟩
      simp only [hb4, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl' (sint.Z (sl.len - W64 1 - W64 1)) _ (DFrac.own 1) rP.loc hb4.1
        $$ [Hsl] as Hsl
      · iframe Hsl; ipureintro
        rw [show (sint.Z (sl.len - W64 1 - W64 1)).toNat = rs.length - 2 by word]
        exact locs_at _ _ rP hP'
      ihave ⟨Hpre2, HP, -⟩ := (bigSepL_split_at _ _ (rs.length - 2) rP hP').1 $$ Hpre
      ihave ⟨HPc, HPr⟩ := connRole_mid cfg rs (rs.length - 2) rP (by omega) $$ HP
      have hTin : rI.addr ≠ go!"" := by
        intro h
        apply Hctxp.2.2.2.1
        rw [← h]; exact Hwf.2 rI (List.mem_of_getElem? hrI)
      have hch' : ∀ r ∈ rs.take (rs.length - 1), r.addr ∈ cfg.chain :=
        fun r hr => Hwf.2 r (List.mem_of_mem_take hr)
      ihave #Hnfs' := nodeFacts_take cfg rs (rs.length - 1) $$ Hnfs
      wp_apply wp_updateNode cfg c sl' (rs.take (rs.length - 1)) (DFrac.own 1) (sl.len - W64 1 - W64 1) rP
        rP.conn ((false, rI.addr) : Role) (by word) (by rw [hpidx]; exact hP') hch'
        $$ [Hreplicas Hsl HPc HPr Htok] as %errP ⟨Hreplicas, Hsl, %bP, HPc, HPpost⟩
      · iframe Hreplicas Hsl HPc
        isplitr
        · iexact Hnfs'
        unfold sendPre
        cases hPc : rP.conn
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · simp only [↓reduceIte]
          icases HPr with ⟨%x, HPr, %Hx⟩
          have hx : x = rI.addr := Hx.2 rI (by rw [show rs.length - 2 + 1 = rs.length - 1 by omega]; exact hrI) hTc
          subst hx
          iframe HPr
          unfold updDep
          have hmt : (metaOf (rs.take (rs.length - 1)) (sint.nat (sl.len - W64 1 - W64 1))).isTail = true := by
            simp only [metaOf, hpidx, List.length_take, decide_eq_true_eq]; omega
          rw [hmt]
          simp only [_root_.and_self, ↓reduceIte, if_neg hTin]
          iexists L
          iframe Htok
          unfold srcOk
          rw [if_neg hTin]
          iexact Hcov
      have hmt : (metaOf (rs.take (rs.length - 1)) (sint.nat (sl.len - W64 1 - W64 1))).isTail = true := by
        simp only [metaOf, hpidx, List.length_take, decide_eq_true_eq]; omega
      have hmn : (metaOf (rs.take (rs.length - 1)) (sint.nat (sl.len - W64 1 - W64 1))).next = go!"" := by
        simp only [metaOf, hpidx, List.length_take]
        rw [if_neg (by omega)]
      ihave ⟨HPr, HPerr⟩ : (if bP then roleHalf cfg.γ rP.addr ((true, go!"") : Role) else iprop(True)) ∗
          (⌜errP = interface.nil⌝ ∨ models_lab.errAny errP) $$ [HPpost]
      · unfold sendPost
        icases HPpost with (⟨%Hok, HPpost⟩ | ⟨%Hb, #He⟩)
        · obtain ⟨rfl, -, rfl⟩ := Hok
          unfold updPost
          icases HPpost with ⟨HPr, -⟩
          rw [hmt, hmn]
          simp only [↓reduceIte]
          iframe HPr
          ileft; ipureintro; trivial
        · subst Hb
          simp only [Bool.false_eq_true, ↓reduceIte]
          isplitr
          · itrivial
          iright; iexact He
      icases HPerr with #HPerr
      wp_join at next with [err]
      · icases HPerr with (%Herr | #Herr)
        · subst Herr
          wp_auto
          wp_join_done
        · ihave %Hne := models_lab.errAny_ne_nil $$ Herr
          obtain ⟨i, rfl⟩ : ∃ i, errP = GoInterface.ok i := by
            cases errP with
            | nil => exact absurd rfl Hne
            | ok i => exact ⟨i, rfl⟩
          wp_auto
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [GoInterface.ok i]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %args_sl ⟨Hargs, -⟩
          wp_apply wp_Printf_args _ _ [GoInterface.ok i] _ $$ [Hargs]
          · iframe Hargs
            iapply BigSepL.bigSepL_cons.2
            isplitr
            · iapply logArg_err $$ Herr
            iapply BigSepL.bigSepL_nil.2; iempintro
          iintro -
          wp_auto
          wp_join_done
      -- the others learn the new tail
      have htake : rs.take (rs.length - 1) = rs.take (rs.length - 2) ++ [rP] := by
        rw [show rs.length - 1 = rs.length - 2 + 1 by omega]
        exact take_succ_of_getElem? rs _ rP HrP_lookup
      have htt : (rs.take (rs.length - 1)).take (rs.length - 2) = rs.take (rs.length - 2) := by
        rw [List.take_take]; congr 1; omega
      rw [htt] at *
      have hmap : (rs.take (rs.length - 2) ++ [{ rP with conn := bP }]).map Rep.loc =
          (rs.take (rs.length - 1)).map Rep.loc := by rw [htake]; simp
      have hmapa : (rs.take (rs.length - 2) ++ [{ rP with conn := bP }]).map Rep.addr =
          (rs.take (rs.length - 1)).map Rep.addr := by rw [htake]; simp
      ihave #Hnfs'' := nodeFacts_of_map cfg _ (rs.take (rs.length - 2) ++ [{ rP with conn := bP }])
        hmap hmapa $$ Hnfs'
      ihave Hin := reps_inF cfg (rs.take (rs.length - 2)) { rP with conn := bP } $$ [Hpre2]
      · iapply BigSepL.bigSepL_mono _ $$ Hpre2
        intro j r hj
        have hl : j < (rs.take (rs.length - 2)).length := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_take] at hl
        exact connRole_updIn cfg rs j r (by omega)
      have hlenle := reps_length_le cfg rs Hwf
      wp_apply wp_updateAll cfg c sl' (rs.take (rs.length - 2) ++ [{ rP with conn := bP }])
        (sl.len - W64 1 - W64 1) ⟨by word, by rw [hpidx]; simp⟩ (by simp; omega)
        (fun r hr => by
          have : r.addr ∈ (rs.take (rs.length - 1)).map Rep.addr := by
            rw [← hmapa]; exact List.mem_map_of_mem hr
          obtain ⟨r0, hr0, he⟩ := List.mem_map.mp this
          rw [← he]; exact hch' r0 hr0)
        $$ [Hreplicas Hsl Hin] as ⟨Hreplicas, Hsl, Hout⟩
      · iframe Hreplicas Hin
        isplitl [Hsl]
        · rw [hmap]; iexact Hsl
        iexact Hnfs''
      ihave ⟨%pre', %Hm, Hreps⟩ := reps_final cfg (rs.take (rs.length - 2)) { rP with conn := bP }
        $$ [Hout HPc HPr]
      · iframe Hout; iframe
      have hmapF : (pre' ++ [{ rP with conn := bP }]).map Rep.loc = (rs.take (rs.length - 1)).map Rep.loc := by
        rw [← hmap]; simp [Hm.1]
      have hmapFa : (pre' ++ [{ rP with conn := bP }]).map Rep.addr =
          (rs.take (rs.length - 1)).map Rep.addr := by
        rw [← hmapa]; simp [Hm.2]
      have hwfF : repsWf cfg (pre' ++ [{ rP with conn := bP }]) := by
        apply repsWf_sub cfg rs _ Hwf
        rw [hmapFa, List.map_take]; exact List.take_sublist _ _
      ihave #HnfsF := nodeFacts_of_map cfg _ (pre' ++ [{ rP with conn := bP }]) hmapF hmapFa $$ Hnfs'
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
        Hreps Hjoin]
      · inext
        iapply coordLock_pack cfg c sl' (pre' ++ [{ rP with conn := bP }]) ver hd rP.loc hwfF
        iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps
        isplitl [Hsl]
        · rw [hmapF, ← hmap]; iexact Hsl
        isplitr
        · iexact HnfsF
        isplitl [Hjoin]
        · iapply joins_sub cfg rs _ _ $$ Hjoin
          intro b hb
          rw [hmapFa, List.map_take] at hb
          exact List.mem_of_mem_take hb
        rw [if_neg (by simp)]
        itrivial
      iapply HΦ; ileft; ipureintro; rfl
    · -- the fence failed: the tail is disconnected, nothing removed
      subst HbT
      ihave %Hne := models_lab.errAny_ne_nil $$ Herr
      obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok i => exact ⟨i, rfl⟩
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
        [interface.mkOk go.string #a, GoInterface.ok i]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %args_sl ⟨Hargs, -⟩
      wp_apply wp_Printf_args _ _ [interface.mkOk go.string #a, GoInterface.ok i] _ $$ [Hargs]
      · iframe Hargs
        iapply BigSepL.bigSepL_cons.2
        isplitr
        · iapply logArg_str
        iapply BigSepL.bigSepL_cons.2
        isplitr
        · iapply logArg_err $$ Herr
        iapply BigSepL.bigSepL_nil.2; iempintro
      iintro -
      wp_auto
      have hT' : rI.addr = rI.addr ∧ (false = true → rI.conn = true) := ⟨rfl, by simp⟩
      ihave Hreps := reps_put cfg rs (rs.length - 1) rI hrI { rI with conn := false } hT' $$ [Hpre HTc]
      · iframe Hpre
        isplitr
        · rw [List.drop_of_length_le (by omega)]; iapply BigSepL.bigSepL_nil.2; iempintro
        iapply connRole_disc cfg _ _ { rI with conn := false } rfl $$ HTc
      have hml := map_set_eq Rep.loc (r' := { rI with conn := false }) hrI rfl
      have hma := map_set_eq Rep.addr (r' := { rI with conn := false }) hrI rfl
      ihave #Hnfs1 := nodeFacts_of_map cfg rs _ hml hma $$ Hnfs
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
        Hreps Hjoin Htok]
      · inext
        iapply coordLock_pack cfg c sl (rs.set (rs.length - 1) { rI with conn := false }) ver hd tl
          ⟨by rw [hma]; exact Hwf.1, fun r hr => by
            have : r.addr ∈ (rs.set (rs.length - 1) { rI with conn := false }).map Rep.addr :=
              List.mem_map_of_mem hr
            rw [hma] at this
            obtain ⟨r0, hr0, he⟩ := List.mem_map.mp this
            rw [← he]; exact Hwf.2 r0 hr0⟩
        iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps
        isplitl [Hsl]
        · rw [hml]; iexact Hsl
        isplitr
        · iexact Hnfs1
        isplitl [Hjoin]
        · iapply joins_sub cfg rs _ _ $$ Hjoin
          intro b hb; rw [hma] at hb; exact hb
        rw [if_neg (show ¬ (rs.set (rs.length - 1) { rI with conn := false } = []) by
          intro h; rw [List.set_eq_nil_iff] at h; simp [h] at hm2)]
        itrivial
      iapply HΦ; iright; iexact Herr
  · -- another replica: removed, its successor and predecessor updated
    have hi1 : sint.nat idx + 1 < rs.length := by
      have : sint.nat idx ≠ rs.length - 1 := by intro h; apply Hif; word
      omega
    list_elem rs (sint.nat idx + 1) as rS
    ihave ⟨HA, HX, HB⟩ := (bigSepL_split_at _ rs (sint.nat idx) rI hrI).1 $$ Hreps
    ihave ⟨HS, HB⟩ := (bigSepL_drop_split (fun j x => connRole cfg rs j x) rs (sint.nat idx + 1) rS
      HrS_lookup).1 $$ HB
    ihave %Hslwf := ownSlice_wf $$ Hsl
    have hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z idx ∧ sint.Z idx ≤ sint.Z sl.cap :=
      ⟨by word, by word, by word⟩
    simp only [hb2, ↓reduceIte]
    wp_auto
    have hb3 : 0 ≤ sint.Z (idx + W64 1) ∧ sint.Z (idx + W64 1) ≤ sint.Z sl.len ∧
        sint.Z sl.len ≤ sint.Z sl.cap := ⟨by word, by word, Hslwf.2⟩
    simp only [hb3, ↓reduceIte]
    wp_apply wp_slice_delete sl (rs.map Rep.loc) idx ⟨hidx0, by word⟩ $$ [Hsl Hcap]
      as %sl' ⟨Hsl, Hcap⟩
    · iframe
    rw [map_eraseIdx']
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [interface.mkOk go.string #a]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %args_sl ⟨Hargs, -⟩
    wp_apply log.Printf.wp_proof _ _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hargs]
    · iframe
    iintro -
    wp_auto
    -- the successor `rS`, now at `idx`
    ihave %Hlen' := ownSlice_len $$ Hsl
    simp only [List.length_map, List.length_eraseIdx_of_lt (show sint.nat idx < rs.length by omega)]
      at Hlen'
    have hlt : sint.Z idx < sint.Z sl'.len := by word
    rw [decide_eq_true hlt]
    wp_auto
    have hS' : (rs.eraseIdx (sint.nat idx))[sint.nat idx]? = some rS := by
      rw [List.getElem?_eraseIdx_of_ge (Nat.le_refl _)]; exact HrS_lookup
    have hlen' : (rs.eraseIdx (sint.nat idx)).length = rs.length - 1 :=
      List.length_eraseIdx_of_lt (by omega)
    have hch' : ∀ r ∈ rs.eraseIdx (sint.nat idx), r.addr ∈ cfg.chain :=
      fun r hr => Hwf.2 r (List.mem_of_mem_eraseIdx hr)
    ihave #Hnfs' : [∗list] r ∈ rs.eraseIdx (sint.nat idx), nodeFacts cfg r.loc r.addr $$ []
    · rw [List.eraseIdx_eq_take_drop_succ]
      iapply BigSepL.bigSepL_append.2
      ihave H := (BigSepL.bigSepL_take_drop (Φ := fun _ (r : Rep) => nodeFacts (hG := hG) cfg r.loc r.addr)
        (l := rs) (n := sint.nat idx)).1 $$ Hnfs
      icases H with ⟨H1, H2⟩
      iframe H1
      ihave H3 := (BigSepL.bigSepL_take_drop (Φ := fun _ (r : Rep) => nodeFacts (hG := hG) cfg r.loc r.addr)
        (l := rs.drop (sint.nat idx)) (n := 1)).1 $$ H2
      icases H3 with ⟨-, H4⟩
      rw [List.drop_drop]
      iexact H4
    ihave ⟨HSc, HSr⟩ := connRole_split cfg rs _ rS $$ HS
    ihave ⟨%xS, HSr⟩ := roleRes_sendPre cfg rs (sint.nat idx + 1) rS (metaOf (rs.eraseIdx (sint.nat idx)) (sint.nat idx))
      (by simp only [metaOf, hlen']; exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩) $$ HSr
    wp_apply wp_updateNode cfg c sl' (rs.eraseIdx (sint.nat idx)) (DFrac.own 1) idx rS rS.conn _ hidx0 hS' hch'
      $$ [Hreplicas Hsl HSc HSr] as %errS ⟨Hreplicas, Hsl, %bS, HSc, HSpost⟩
    · iframe
      iexact Hnfs'
    have hsplit : rs.eraseIdx (sint.nat idx) = rs.take (sint.nat idx) ++ [rS] ++ rs.drop (sint.nat idx + 2) := by
      rw [List.eraseIdx_eq_take_drop_succ, List.drop_eq_getElem_cons (by omega)]
      have : rs[sint.nat idx + 1] = rS := by
        have := HrS_lookup; rw [List.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
      rw [this]; simp
    have htl : (rs.take (sint.nat idx)).length = sint.nat idx := by simp; omega
    unfold sendPost
    icases HSpost with (⟨%Hok, HSpost⟩ | ⟨%HbS, #HerrS⟩)
    · -- the successor knows its new neighbors
      obtain ⟨rfl, hSc, rfl⟩ := Hok
      unfold updPost
      icases HSpost with ⟨HSr, -⟩
      wp_auto
      have hidx1 : 0 < sint.Z idx ∨ sint.Z idx = 0 := by omega
      wp_if_destruct
      · -- the predecessor `rPr`
        have hi0 : 0 < sint.nat idx := by word
        list_elem rs (sint.nat idx - 1) as rPr
        ihave ⟨HA, HPr⟩ := (bigSepL_take_snoc (connRole cfg rs) rs (sint.nat idx - 1) rPr HrPr_lookup).1
          $$ [HA]
        · rw [show sint.nat idx - 1 + 1 = sint.nat idx by omega]; iexact HA
        have hPr' : (rs.eraseIdx (sint.nat idx))[sint.nat idx - 1]? = some rPr := by
          rw [List.getElem?_eraseIdx_of_lt (by omega)]; exact HrPr_lookup
        ihave ⟨HPc, HPr⟩ := connRole_split cfg rs _ rPr $$ HPr
        ihave ⟨%xP, HPr⟩ := roleRes_sendPre cfg rs (sint.nat idx - 1) rPr
          (metaOf (rs.eraseIdx (sint.nat idx)) (sint.nat (idx - W64 1)))
          (by simp only [metaOf, hlen']; rw [show sint.nat (idx - W64 1) = sint.nat idx - 1 by word]
              exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩) $$ HPr
        wp_apply wp_updateNode cfg c sl' (rs.eraseIdx (sint.nat idx)) (DFrac.own 1) (idx - W64 1) rPr rPr.conn _
          (by word) (by rw [show sint.nat (idx - W64 1) = sint.nat idx - 1 by word]; exact hPr') hch'
          $$ [Hreplicas Hsl HPc HPr] as %errP ⟨Hreplicas, Hsl, %bP, HPc, HPpost⟩
        · iframe
          iexact Hnfs'
        have hPidx : sint.nat (idx - W64 1) = sint.nat idx - 1 := by word
        rw [hPidx]
        have hsplit2 : rs.eraseIdx (sint.nat idx) =
            rs.take (sint.nat idx - 1) ++ [rPr, rS] ++ rs.drop (sint.nat idx + 2) := by
          rw [hsplit, show sint.nat idx = sint.nat idx - 1 + 1 by omega,
            take_succ_of_getElem? rs _ rPr HrPr_lookup]
          simp
        have hF : (rs.take (sint.nat idx - 1) ++ [{ rPr with conn := bP }, rS] ++ rs.drop (sint.nat idx + 2)).map
            Rep.loc = (rs.eraseIdx (sint.nat idx)).map Rep.loc := by rw [hsplit2]; simp
        have hFa : (rs.take (sint.nat idx - 1) ++ [{ rPr with conn := bP }, rS] ++ rs.drop (sint.nat idx + 2)).map
            Rep.addr = (rs.eraseIdx (sint.nat idx)).map Rep.addr := by rw [hsplit2]; simp
        have hFl : (rs.take (sint.nat idx - 1) ++ [{ rPr with conn := bP }, rS] ++
            rs.drop (sint.nat idx + 2)).length = (rs.eraseIdx (sint.nat idx)).length := by
          simpa using congrArg List.length hF
        ihave ⟨HPrF, #HPerr, %HbP⟩ : connRole cfg (rs.take (sint.nat idx - 1) ++ [{ rPr with conn := bP }, rS] ++
            rs.drop (sint.nat idx + 2)) (sint.nat idx - 1) { rPr with conn := bP } ∗
            (⌜errP = interface.nil⌝ ∨ models_lab.errAny errP) ∗ ⌜bP = true → rPr.conn = true⌝ $$ [HPc HPpost]
        · unfold sendPost
          icases HPpost with (⟨%Hok, HPpost⟩ | ⟨%Hb, #He⟩)
          · obtain ⟨rfl, hPc, rfl⟩ := Hok
            unfold updPost
            icases HPpost with ⟨HPr, -⟩
            isplitl [HPc HPr]
            · iapply connRole_of_meta cfg _ _ _ { rPr with conn := true } hFl hFa rfl
              iframe
            isplitr
            · ileft; ipureintro; trivial
            ipureintro; exact fun _ => hPc
          · subst Hb
            isplitl [HPc]
            · iapply connRole_disc cfg _ _ { rPr with conn := false } rfl $$ HPc
            isplitr
            · iright; iexact He
            ipureintro; intro h; cases h
        ihave HSF := connRole_of_meta cfg (rs.eraseIdx (sint.nat idx))
          (rs.take (sint.nat idx - 1) ++ [{ rPr with conn := bP }, rS] ++ rs.drop (sint.nat idx + 2))
          (sint.nat idx) rS hFl hFa hSc $$ [HSc HSr]
        · rw [hSc]; iframe
        have htl1 : (rs.take (sint.nat idx - 1)).length = sint.nat idx - 1 := by simp; omega
        ihave Hreps := reps_assemble cfg rs (rs.take (sint.nat idx - 1)) [{ rPr with conn := bP }, rS]
          (rs.drop (sint.nat idx + 2)) (by rw [htl1]) (by rw [htl1]; simp; congr 1; omega) (by simp)
          (by simp; omega)
          (fun _ r' hr' hc => by
            simp at hr'; subst hr'
            exact ⟨rPr, by rw [htl1]; exact HrPr_lookup, HbP hc, rfl⟩) $$ [HA HPrF HSF HB]
        · iframe HA
          isplitl [HPrF HSF]
          · iapply BigSepL.bigSepL_cons.2
            rw [htl1, Nat.add_zero]
            iframe HPrF
            iapply BigSepL.bigSepL_singleton.2
            rw [show sint.nat idx - 1 + (0 + 1) = sint.nat idx by omega]
            iexact HSF
          iapply BigSepL.bigSepL_mono _ $$ HB
          intro k x _
          rw [htl1]; simp only [List.length_cons, List.length_nil]
          rw [show sint.nat idx - 1 + (0 + 1 + 1) + 1 + k = sint.nat idx + 1 + 1 + k by omega]
        ihave #HnfsF := nodeFacts_of_map cfg _ _ hF hFa $$ Hnfs'
        have hsub : ((rs.take (sint.nat idx - 1) ++ [{ rPr with conn := bP }, rS] ++
            rs.drop (sint.nat idx + 2)).map Rep.addr).Sublist (rs.map Rep.addr) := by
          rw [hFa, ← map_eraseIdx']; exact List.eraseIdx_sublist _ _
        icases HPerr with (%Herr | #Herr)
        · subst Herr
          wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
            Hreps Hjoin]
          · inext
            iapply coordLock_new cfg c sl' rs _ ver hd tl Hwf hsub (by simp)
            iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
            isplitl [Hsl]
            · rw [hF]; iexact Hsl
            iexact HnfsF
          iapply HΦ; ileft; ipureintro; rfl
        · ihave %Hne := models_lab.errAny_ne_nil $$ Herr
          obtain ⟨ie, rfl⟩ : ∃ ie, errP = GoInterface.ok ie := by
            cases errP with
            | nil => exact absurd rfl Hne
            | ok i => exact ⟨i, rfl⟩
          wp_auto
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [GoInterface.ok ie]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %args_sl ⟨Hargs, -⟩
          wp_apply wp_Printf_args _ _ [GoInterface.ok ie] _ $$ [Hargs]
          · iframe Hargs
            iapply BigSepL.bigSepL_cons.2
            isplitr
            · iapply logArg_err $$ Herr
            iapply BigSepL.bigSepL_nil.2; iempintro
          iintro -
          wp_auto
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
            Hreps Hjoin]
          · inext
            iapply coordLock_new cfg c sl' rs _ ver hd tl Hwf hsub (by simp)
            iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
            isplitl [Hsl]
            · rw [hF]; iexact Hsl
            iexact HnfsF
          iapply HΦ; iright; iexact Herr
      · -- the head was removed: no predecessor
        have hi0 : sint.nat idx = 0 := by word
        have hF : (rs.take (sint.nat idx) ++ [rS] ++ rs.drop (sint.nat idx + 2)).map Rep.loc =
            (rs.eraseIdx (sint.nat idx)).map Rep.loc := by rw [hsplit]
        have hFa : (rs.take (sint.nat idx) ++ [rS] ++ rs.drop (sint.nat idx + 2)).map Rep.addr =
            (rs.eraseIdx (sint.nat idx)).map Rep.addr := by rw [hsplit]
        have hFl : (rs.take (sint.nat idx) ++ [rS] ++ rs.drop (sint.nat idx + 2)).length =
            (rs.eraseIdx (sint.nat idx)).length := by rw [hsplit]
        ihave HSF := connRole_of_meta cfg (rs.eraseIdx (sint.nat idx))
          (rs.take (sint.nat idx) ++ [rS] ++ rs.drop (sint.nat idx + 2))
          (sint.nat idx) rS hFl hFa hSc $$ [HSc HSr]
        · rw [hSc]; iframe
        ihave Hreps := reps_assemble cfg rs (rs.take (sint.nat idx)) [rS]
          (rs.drop (sint.nat idx + 2)) (by rw [htl]) (by rw [htl]; rfl) (by simp)
          (by simp; omega) (fun h => by simp [hi0] at h) $$ [HA HSF HB]
        · iframe HA
          isplitl [HSF]
          · iapply BigSepL.bigSepL_singleton.2
            rw [htl, Nat.add_zero]
            iexact HSF
          iapply BigSepL.bigSepL_mono _ $$ HB
          intro k x _
          rw [htl, List.length_singleton]
        ihave #HnfsF := nodeFacts_of_map cfg _ _ hF hFa $$ Hnfs'
        have hsub : ((rs.take (sint.nat idx) ++ [rS] ++ rs.drop (sint.nat idx + 2)).map Rep.addr).Sublist
            (rs.map Rep.addr) := by
          rw [hFa, ← map_eraseIdx']; exact List.eraseIdx_sublist _ _
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
          Hreps Hjoin]
        · inext
          iapply coordLock_new cfg c sl' rs _ ver hd tl Hwf hsub (by simp)
          iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
          isplitl [Hsl]
          · rw [hF]; iexact Hsl
          iexact HnfsF
        iapply HΦ; ileft; ipureintro; rfl
    · -- the successor's update failed: it is disconnected
      subst HbS
      ihave %Hne := models_lab.errAny_ne_nil $$ HerrS
      obtain ⟨ie, rfl⟩ : ∃ ie, errS = GoInterface.ok ie := by
        cases errS with
        | nil => exact absurd rfl Hne
        | ok i => exact ⟨i, rfl⟩
      wp_auto
      ihave #HerrS' := HerrS
      unfold models_lab.errAny
      icases HerrS' with ⟨%e, %He, -, #HE⟩
      cases He
      wp_apply HE
      iintro %msg
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType []) [interface.mkOk go.string #msg]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %args_sl ⟨Hargs, -⟩
      wp_apply log.Printf.wp_proof _ _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hargs]
      · iframe
      iintro -
      wp_auto
      have hF : (rs.take (sint.nat idx) ++ [{ rS with conn := false }] ++ rs.drop (sint.nat idx + 2)).map Rep.loc =
          (rs.eraseIdx (sint.nat idx)).map Rep.loc := by rw [hsplit]; simp
      have hFa : (rs.take (sint.nat idx) ++ [{ rS with conn := false }] ++ rs.drop (sint.nat idx + 2)).map Rep.addr =
          (rs.eraseIdx (sint.nat idx)).map Rep.addr := by rw [hsplit]; simp
      ihave Hreps := reps_assemble cfg rs (rs.take (sint.nat idx)) [{ rS with conn := false }]
        (rs.drop (sint.nat idx + 2)) (by rw [htl]) (by rw [htl]; rfl) (by simp)
        (by simp; omega) (fun _ r' hr' hc => by simp at hr'; subst hr'; simp at hc) $$ [HA HSc HB]
      · iframe HA
        isplitl [HSc]
        · iapply BigSepL.bigSepL_singleton.2
          iapply connRole_disc cfg _ _ { rS with conn := false } rfl $$ HSc
        iapply BigSepL.bigSepL_mono _ $$ HB
        intro k x _
        rw [htl, List.length_singleton]
      ihave #HnfsF := nodeFacts_of_map cfg _ _ hF hFa $$ Hnfs'
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreplicas Hsl Hcap Hversion Hnext Hhead Htail
        Hreps Hjoin]
      · inext
        iapply coordLock_new cfg c sl' rs _ ver hd tl Hwf
          (by rw [hFa, ← map_eraseIdx']; exact List.eraseIdx_sublist _ _) (by simp)
        iframe Hreplicas Hcap Hversion Hnext Hhead Htail Hreps Hjoin
        isplitl [Hsl]
        · rw [hF]; iexact Hsl
        iexact HnfsF
      iapply HΦ; iright; iexact HerrS

end proof

end github_com.despreston.go_craq

end Perennial
