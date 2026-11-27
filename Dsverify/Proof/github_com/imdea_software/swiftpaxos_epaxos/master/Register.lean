/-
`m.Register(args, reply)` (`masterRegister.spec`, `NetRpc/Specs.lean`): replica node `k`
registers its configured address; the reply is `Ready` with the final list (`listFinal`) once five
are registered, else not ready.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs
public import Proof.fmt.SprintfPure
public import Perennial.Proof.fmt.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions] [epaxos.Assumptions]

open replica.defs in
theorem regReply_combine (pr : Loc) (h : pr ≠ null) (a : w64) (b : GoSlice) (c d : Bool) :
    pr.[RegisterReply, go!"ReplicaId"] ↦ a ∗ pr.[RegisterReply, go!"NodeList"] ↦ b ∗
      pr.[RegisterReply, go!"Ready"] ↦ c ∗ pr.[RegisterReply, go!"IsLeader"] ↦ d ⊢
      (pr ↦ RegisterReply.mk a b c d : IProp GF) := by
  iintro ⟨H1, H2, H3, H4⟩
  iapply typedPointsto_combine (V := RegisterReply) pr _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe

set_option goose.wp.extras true in
set_option maxHeartbeats 1600000 in
open replica.defs in
theorem masterRegister.wp_proof (γ : EpNames) : masterRegister.spec (GF := GF) γ (isMaster γ) := by
  intro m k pa pr hk
  wp_start as ⟨#Hm, Hpa, Hpr⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %hprnn⟩
  iStructNamedPrefix Hpr "r"
  unfold isMaster
  icases Hm with ⟨#Hpkg, %mu, %cfg, %logger, %ic, %c, #Hlock, #Hmu, #Hic, #Hcond, #HN, #Hcfgf, #Hcfg, %Hld, #Hlogf, #Hlog⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  unfold masterLockInv masterLists
  icases Hinv with ⟨%ks, %nl, %al, %pl, %ldsl, %alsl, %latsl, %ld, %alv, %lat, %fi, %Hks, Hlists, #Hldf, Hld, #Half, Halv, #Hlatf, Hlat, Hfi⟩
  obtain ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩ := Hks
  by_cases h5 : ks.length < 5
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h5)]
    icases Hlists with ⟨Hnlf, Hnl, Hnlc, Hadf, Hal, Halc, Hplf, Hpl, Hplc, Hunset⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
      [interface.mkOk go.string #(replicaIp k), interface.mkOk go.int #(portOf k)]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, -⟩
    wp_auto
    wp_apply _root_.Perennial.EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s:%d"
        [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d]
        _ _ _ _ (by fmt_encode) (by fmt_fits) (.str _ _ _ (.int _ _ _ _
        (.int _) .nil)) $$ [$Hfmt $Hsl] as %ap ⟨-, %Hap⟩
    have hap := sprintf_str_colon_int _ _ _ Hap
    have hk6 : k ≤ 6 := by
      simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
    have hsz : sint.Z (portOf k) = 7500 + k := by unfold portOf; word
    rw [hsz, ← peerAddrOf_fmt k hk] at hap
    subst hap
    rename_i key_ptr
    irename : (key_ptr ↦ (zero_val w64) : IProp GF) => Hkey
    ihave %Hnll := ownSlice_len _ _ _ $$ Hnl
    ihave HI : (∃ (iw kv : w64) (apv : GoString), "i" ∷ i_ptr ↦ iw ∗ "Hkey" ∷ key_ptr ↦ kv ∗
        "ap" ∷ ap_ptr ↦ apv ∗ "Hnl" ∷ nl ↦* List.map peerAddrOf ks ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z iw ∧ sint.Z iw ≤ sint.Z nl.len ∧
          ∀ t, t < sint.nat iw → ks[t]? ≠ some k⌝ : IProp GF)
        $$ [i Hkey ap Hnl]
    · iexists _, _, _; iframe; ipureintro; refine ⟨by word, by word, ?_⟩; intro t ht; word
    wp_for HI
    wp_if_destruct
    · list_elem (List.map peerAddrOf ks) (sint.nat iw) as x
      rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z nl.len by word)]
      wp_apply wp_load_slice_index nl (sint.Z iw) _ _ x (by word) $$ [$Hnl] as Hnl
      · ipureintro; simpa [sint.nat] using Hx_lookup
      rw [List.getElem?_map] at Hx_lookup
      obtain ⟨kx, hkx, rfl⟩ := Option.map_eq_some_iff.mp Hx_lookup
      have hkxs : kx ∈ ks := List.mem_of_getElem? hkx
      wp_if_destruct
      · -- found: not ready
        have hkeq : k = kx := peerAddrOf_inj _ _ hk (hsub kx hkxs) Hif
        subst hkeq
        wp_for_post
        have hiwlt : sint.nat iw < ks.length := (List.getElem?_eq_some_iff.mp hkx).1
        wp_if_destruct
        · exfalso; simp at Hnll; word
        wp_if_destruct
        · exfalso; simp at Hnll; word
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hld Halv Hlat Hfi Hnlf Hnl Hnlc Hadf Hal Halc
          Hplf Hpl Hplc Hunset]
        · iexists ks, nl, al, pl, ldsl, alsl, latsl, ld, alv, lat, fi
          rw [ite_eq_left_of_eq_true _ _ (eq_true h5)]
          inext
          iframe
          iframe Hldf Half Hlatf
          ipureintro; exact ⟨hnd, hsub, hnlc, halc, hplc, hldl, halvl, hlatl⟩
        iapply HΦ
        iexists (W64 0), slice.nil, (DFrac.own 1), [], false, false
        isplitl [rReady rReplicaId rNodeList rIsLeader]
        · iapply regReply_combine pr hprnn
          iframe
        unfold regReplyOk
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitl
        · iapply ownSlice_nil
        itrivial
      · wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro t ht
        by_cases htt : t < sint.nat iw
        · exact Hi.2.2 t htt
        · have : t = sint.nat iw := by word
          subst this; rw [hkx]; intro h; exact Hif (by rw [Option.some.inj h])
    · -- not found
      have hiw : iw = nl.len := by word
      subst hiw
      have hkn : k ∉ ks := by
        intro hm
        obtain ⟨t, ht, hkt⟩ := List.getElem_of_mem hm
        apply Hi.2.2 t (by simp at Hnll; omega)
        rw [List.getElem?_eq_getElem ht, hkt]
      have hL : sint.nat nl.len = ks.length := by simp at Hnll; omega
      ihave %Hall := ownSlice_len _ _ _ $$ Hal
      ihave %Hpll := ownSlice_len _ _ _ $$ Hpl
      have hal : al.len = nl.len := by simp at Hall; word
      have hpl : pl.len = nl.len := by simp at Hpll; word
      have hcap : ∀ s : GoSlice, sint.Z s.cap = 5 → s.len = nl.len →
          0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (nl.len + W64 1) ∧
          sint.Z s.len ≤ sint.Z (nl.len + W64 1) ∧ sint.Z (nl.len + W64 1) ≤ sint.Z s.cap := by
        intro s hs hsl; rw [hsl]; constructor <;> word
      icases ownSlice_slice_into_capacity (W64 0) (nl.len + W64 1) nl _ $$ [Hnl Hnlc]
        with ⟨%vn, -, Hnl, Hnlc⟩
      · iframe; ipureintro; exact hcap nl hnlc rfl
      icases ownSlice_slice_into_capacity (W64 0) (nl.len + W64 1) al _ $$ [Hal Halc]
        with ⟨%va, -, Hal, Halc⟩
      · iframe; ipureintro; exact hcap al halc hal
      icases ownSlice_slice_into_capacity (W64 0) (nl.len + W64 1) pl _ $$ [Hpl Hplc]
        with ⟨%vp, -, Hpl, Hplc⟩
      · iframe; ipureintro; exact hcap pl hplc hpl
      have hb3 : ∀ s : GoSlice, sint.Z s.cap = 5 →
          (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (nl.len + W64 1) ∧
            sint.Z (nl.len + W64 1) ≤ sint.Z s.cap) := by
        intro s hs; refine ⟨by decide, by word, by word⟩
      have hlt5 : sint.Z nl.len < 5 := by word
      have hib : 0 ≤ sint.Z nl.len ∧ sint.Z nl.len < sint.Z (nl.len + W64 1 - W64 0) := by
        constructor <;> word
      ihave %Hnvl := ownSlice_len _ _ _ $$ Hnl
      ihave %Hval := ownSlice_len _ _ _ $$ Hal
      ihave %Hvpl := ownSlice_len _ _ _ $$ Hpl
      rw [ite_eq_left (hb3 nl hnlc)]
      wp_auto
      rw [ite_eq_left hib]
      wp_apply wp_store_slice_index $$ [$Hnl] as Hnl
      · ipureintro; simp only [slice.slice] at Hnvl; constructor <;> word
      rw [ite_eq_left (hb3 al halc)]
      wp_auto
      rw [ite_eq_left hib]
      wp_apply wp_store_slice_index $$ [$Hal] as Hal
      · ipureintro; simp only [slice.slice] at Hval; constructor <;> word
      rw [ite_eq_left (hb3 pl hplc)]
      wp_auto
      rw [ite_eq_left hib]
      wp_apply wp_store_slice_index $$ [$Hpl] as Hpl
      · ipureintro; simp only [slice.slice] at Hvpl; constructor <;> word
      ihave %Hldl := ownSlice_len _ _ _ $$ Hld
      rw [ite_eq_left (show 0 ≤ sint.Z nl.len ∧ sint.Z nl.len < sint.Z ldsl.len by
        constructor <;> simp [hldl] at Hldl <;> word)]
      wp_apply wp_store_slice_index $$ [$Hld] as Hld
      · ipureintro; simp [hldl] at Hldl ⊢; constructor <;> word
      have hn1 : sint.nat (W64 0) = 0 := rfl
      have hlen1 : sint.nat (nl.len + W64 1 - W64 0) = ks.length + 1 := by word
      simp only [slice.slice, hn1, hlen1] at Hnvl Hval Hvpl
      have hlm : ∀ {β : Type} (f : Nat → β), (ks.map f).length = sint.nat nl.len := by
        intro β f; rw [List.length_map, hL]
      rw [set_app_end _ _ _ _ (hlm _) (by have := Hnvl.1; simp at this; rw [List.length_append, hlm]; omega),
        set_app_end _ _ _ _ (hlm _) (by have := Hval.1; simp at this; rw [List.length_append, hlm]; omega),
        set_app_end _ _ _ _ (hlm _) (by have := Hvpl.1; simp at this; rw [List.length_append, hlm]; omega)]
      have hks' : (ks ++ [k]).Nodup :=
        (List.perm_append_singleton k ks).nodup_iff.mpr (List.nodup_cons.mpr ⟨hkn, hnd⟩)
      have hsub' : ∀ x ∈ ks ++ [k], x ∈ replicaNodes := by
        intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact hsub x hx
        · simp at hx; subst hx; exact hk
      have hcap' : ∀ s : GoSlice, sint.Z s.cap = 5 →
          sint.Z (slice.slice s GoString (W64 0) (nl.len + W64 1)).cap = 5 := by
        intro s hs; simp only [slice.slice]; word
      wp_if_destruct
      · have hk4 : ks.length = 4 := by word
        ipersist Hnlf
        ipersist Hadf
        ipersist Hplf
        ipersist Hnl
        ipersist Hal
        ipersist Hpl
        imod listFix γ ((ks ++ [k]).map peerAddrOf) (ks_perm _ hks' hsub' (by simp; omega)) $$ Hunset
          with #HLf
        ihave Hc2 := Hcfg
        iStructNamed Hc2
        wp_apply (IntoValTyped.wp_load (V := Loc) (t := go.GoType.PointerType go.string) _ _ c.Leader')
          $$ [$Leader] as -
        rw [Hld]
        wp_auto
        ihave HI2 : (∃ (iw2 ml ldr : w64), "i" ∷ i_ptr ↦ iw2 ∗ "minLatency" ∷ minLatency_ptr ↦ ml ∗
            "leader" ∷ leader_ptr ↦ ldr ∗ "%Hi2" ∷ ⌜0 ≤ sint.Z iw2 ∧ sint.Z iw2 ≤ 5⌝ : IProp GF)
            $$ [i minLatency leader]
        · iexists _, _, _; iframe; ipureintro; constructor <;> word
        ihave %Hldl := ownSlice_len _ _ _ $$ Hld
        ihave %Hlatl := ownSlice_len _ _ _ $$ Hlat
        wp_for HI2
        wp_if_destruct
        · list_elem lat (sint.nat iw2) as x
          rw [ite_eq_left (show 0 ≤ sint.Z iw2 ∧ sint.Z iw2 < sint.Z latsl.len by word)]
          wp_apply wp_load_slice_index latsl (sint.Z iw2) _ _ x (by word) $$ [$Hlat] as Hlat
          · ipureintro; simpa [sint.nat] using Hx_lookup
          generalize (float64Leb x ml && !float64Eq x ml) = b
          wp_if_destruct
          · wp_for_post
            iframe
            iexists _, _, _
            iframe
            ipureintro; constructor <;> word
          · rw [ite_eq_left (show 0 ≤ sint.Z iw2 ∧ sint.Z iw2 < sint.Z latsl.len by word)]
            wp_apply wp_load_slice_index latsl (sint.Z iw2) _ _ x (by word) $$ [$Hlat] as Hlat
            · ipureintro; simpa [sint.nat] using Hx_lookup
            wp_for_post
            iframe
            iexists _, _, _
            iframe
            ipureintro; constructor <;> word
        wp_join iprop(∃ (b : Bool) (ld' : List Bool),
            pr.[RegisterReply, go!"IsLeader"] ↦ b ∗ ldsl ↦* ld' ∗ ⌜ld'.length = 5⌝ ∗
            master_ptr ↦ m ∗ index_ptr ↦ nl.len ∗ reply_ptr ↦ pr)
          with [rIsLeader Hld master index reply]
          as ⟨%b, %ld', rIsLeader, Hld, %Hld', master, index, reply⟩
        · rw [ite_eq_left (show 0 ≤ sint.Z nl.len ∧ sint.Z nl.len < sint.Z ldsl.len by
            simp at Hldl; word)]
          wp_apply wp_store_slice_index $$ [$Hld] as Hld
          · ipureintro; simp at Hldl ⊢; word
          wp_join_done
          iexists _, _; iframe; ipureintro; simp [hldl]
        · iexists _, _; iframe; ipureintro; simp [hldl]
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hld Halv Hlat Hfi]
        · iexists ks ++ [k], _, _, _, ldsl, alsl, latsl, ld', alv, lat, fi
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp; omega))]
          inext
          simp only [List.map_append, List.map_cons, List.map_nil]
          iframe
          iframe Hnlf Hnl Hadf Hal Hplf Hpl HLf Hldf Half Hlatf
          ipureintro
          refine ⟨hks', hsub', ?_, ?_, ?_, Hld', halvl, hlatl⟩ <;> simp only [slice.slice] <;> word
        iapply HΦ
        iexists nl.len, _, DFrac.discard, (ks ++ [k]).map peerAddrOf, true, b
        isplitl [rReady rReplicaId rNodeList rIsLeader]
        · iapply regReply_combine pr hprnn
          iframe
        unfold regReplyOk
        simp only [↓reduceIte]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe Hnl HLf
        ipureintro
        have : uint.nat nl.len = ks.length := by word
        rw [this]; simp
      · -- not ready yet
        have h5' : (ks ++ [k]).length < 5 := by simp; word
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hld Halv Hlat Hfi Hnlf Hnl Hnlc Hadf Hal Halc
          Hplf Hpl Hplc Hunset]
        · iexists ks ++ [k], _, _, _, ldsl, alsl, latsl, _, alv, lat, fi
          rw [ite_eq_left_of_eq_true _ _ (eq_true h5')]
          inext
          simp only [List.map_append, List.map_cons, List.map_nil]
          iframe
          iframe Hldf Half Hlatf
          ipureintro
          refine ⟨hks', hsub', ?_, ?_, ?_, by simp [hldl], halvl, hlatl⟩ <;>
            simp only [slice.slice] <;> word
        iapply HΦ
        iexists (W64 0), slice.nil, (DFrac.own 1), [], false, false
        isplitl [rReady rReplicaId rNodeList rIsLeader]
        · iapply regReply_combine pr hprnn
          iframe
        unfold regReplyOk
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitl
        · iapply ownSlice_nil
        itrivial
  rw [ite_eq_right_of_eq_false _ _ (eq_false h5)]
  icases Hlists with ⟨#Hnlf, #Hnl, #Hadf, #Hal, #Hplf, #Hpl, #HLf⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.string #(replicaIp k), interface.mkOk go.int #(portOf k)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Hsl, -⟩
  wp_auto
  wp_apply _root_.Perennial.EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%s:%d"
      [.dir none _root_.Perennial.fmt.verb_s, .lit go!":", .dir none _root_.Perennial.fmt.verb_d]
      _ _ _ _ (by fmt_encode) (by fmt_fits) (.str _ _ _ (.int _ _ _ _
      (.int _) .nil)) $$ [$Hfmt $Hsl] as %ap ⟨-, %Hap⟩
  have hap := sprintf_str_colon_int _ _ _ Hap
  have hk6 : k ≤ 6 := by
    simp only [replicaNodes, List.mem_cons, List.mem_nil_iff, or_false] at hk; omega
  have hsz : sint.Z (portOf k) = 7500 + k := by unfold portOf; word
  rw [hsz, ← peerAddrOf_fmt k hk] at hap
  subst hap
  rename_i key_ptr
  irename : (key_ptr ↦ (zero_val w64) : IProp GF) => Hkey
  ihave %Hnll := ownSlice_len _ _ _ $$ Hnl
  have hkin : k ∈ ks := ks_full ks hnd hsub h5 k hk
  obtain ⟨j, hj, hkj⟩ := List.getElem_of_mem hkin
  ihave HI : (∃ (iw kv : w64) (apv : GoString), "i" ∷ i_ptr ↦ iw ∗ "Hkey" ∷ key_ptr ↦ kv ∗
      "ap" ∷ ap_ptr ↦ apv ∗ "%Hi" ∷ ⌜0 ≤ sint.Z iw ∧ sint.Z iw ≤ j⌝ : IProp GF)
      $$ [i Hkey ap]
  · iexists _, _, _; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · list_elem (List.map peerAddrOf ks) (sint.nat iw) as x
    rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z nl.len by word)]
    wp_apply wp_load_slice_index nl (sint.Z iw) _ _ x (by word) $$ [$Hnl] as -
    · ipureintro; simpa [sint.nat] using Hx_lookup
    rw [List.getElem?_map] at Hx_lookup
    obtain ⟨kx, hkx, rfl⟩ := Option.map_eq_some_iff.mp Hx_lookup
    have hkxs : kx ∈ ks := List.mem_of_getElem? hkx
    wp_if_destruct
    · -- found
      have hkeq : k = kx := peerAddrOf_inj _ _ hk (hsub kx hkxs) Hif
      subst hkeq
      wp_for_post
      have hkslen : ks.length = 5 := by have := ks_le ks hnd hsub; omega
      have hnlen : nl.len = W64 5 := by simp at Hnll; word
      have hiwlt : sint.nat iw < 5 := hkslen ▸ (List.getElem?_eq_some_iff.mp hkx).1
      wp_if_destruct
      · exfalso; word
      rw [hnlen]
      wp_auto
      ihave Hc2 := Hcfg
      iStructNamed Hc2
      wp_apply (IntoValTyped.wp_load (V := Loc) (t := go.GoType.PointerType go.string) _ _ c.Leader')
        $$ [$Leader] as -
      rw [Hld]
      wp_auto
      ihave HI2 : (∃ (iw2 ml ldr : w64), "i" ∷ i_ptr ↦ iw2 ∗ "minLatency" ∷ minLatency_ptr ↦ ml ∗
          "leader" ∷ leader_ptr ↦ ldr ∗ "%Hi2" ∷ ⌜0 ≤ sint.Z iw2 ∧ sint.Z iw2 ≤ 5⌝ : IProp GF)
          $$ [i minLatency leader]
      · iexists _, _, _; iframe; ipureintro; constructor <;> word
      ihave %Hldl := ownSlice_len _ _ _ $$ Hld
      ihave %Hlatl := ownSlice_len _ _ _ $$ Hlat
      wp_for HI2
      wp_if_destruct
      · list_elem lat (sint.nat iw2) as x
        rw [ite_eq_left (show 0 ≤ sint.Z iw2 ∧ sint.Z iw2 < sint.Z latsl.len by word)]
        wp_apply wp_load_slice_index latsl (sint.Z iw2) _ _ x (by word) $$ [$Hlat] as Hlat
        · ipureintro; simpa [sint.nat] using Hx_lookup
        generalize (float64Leb x ml && !float64Eq x ml) = b
        wp_if_destruct
        · wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro; constructor <;> word
        · rw [ite_eq_left (show 0 ≤ sint.Z iw2 ∧ sint.Z iw2 < sint.Z latsl.len by word)]
          wp_apply wp_load_slice_index latsl (sint.Z iw2) _ _ x (by word) $$ [$Hlat] as Hlat
          · ipureintro; simpa [sint.nat] using Hx_lookup
          wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro; constructor <;> word
      wp_join iprop(∃ (b : Bool) (ld' : List Bool),
          pr.[RegisterReply, go!"IsLeader"] ↦ b ∗ ldsl ↦* ld' ∗ ⌜ld'.length = 5⌝ ∗
          master_ptr ↦ m ∗ index_ptr ↦ iw ∗ reply_ptr ↦ pr)
        with [rIsLeader Hld master index reply]
        as ⟨%b, %ld', rIsLeader, Hld, %Hld', master, index, reply⟩
      · rw [ite_eq_left (show 0 ≤ sint.Z iw ∧ sint.Z iw < sint.Z ldsl.len by
          simp [hldl] at Hldl; word)]
        wp_apply wp_store_slice_index $$ [$Hld] as Hld
        · ipureintro; simp [hldl] at Hldl ⊢; word
        wp_join_done
        iexists _, _; iframe; ipureintro; simp [hldl]
      · iexists _, _; iframe; ipureintro; exact hldl
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hld Halv Hlat Hfi]
      · iexists ks, nl, al, pl, ldsl, alsl, latsl, ld', alv, lat, fi
        rw [ite_eq_right_of_eq_false _ _ (eq_false h5)]
        inext
        iframe
        iframe Hnlf Hnl Hadf Hal Hplf Hpl HLf Hldf Half Hlatf
        ipureintro; exact ⟨hnd, hsub, hnlc, halc, hplc, Hld', halvl, hlatl⟩
      iapply HΦ
      iexists iw, nl, DFrac.discard, ks.map peerAddrOf, true, b
      isplitl [rReady rReplicaId rNodeList rIsLeader]
      · iapply regReply_combine pr hprnn
        iframe
      unfold regReplyOk
      simp only [↓reduceIte]
      iframe Hnl HLf
      ipureintro
      have : uint.nat iw = sint.nat iw := by word
      rw [this, List.getElem?_map, hkx]; rfl
    · wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      have hne : sint.nat iw ≠ j := by
        intro h; subst h; rw [List.getElem?_eq_getElem hj, hkj] at hkx
        exact Hif (by rw [Option.some.inj hkx])
      constructor <;> word
  · exfalso; simp at Hnll; word

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
