/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__ValidateConfigurationChange.lean`.
Lean-first (no Rocq counterpart); D43 M4 (2026-10-26): the backend's read by the caller's triple,
the removed id's check, then by the change's type: an `AddNode`'s context by `json.Unmarshal`'s
spec, the members' peer URLs gathered (a range over the members map, each member's URLs into a set)
and the new member's checked against them; a `RemoveNode`'s member looked up.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ValidateConfigurationChange
public import Spec.encoding.json.Unmarshal
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetNodeId
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetType

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- One of the package's error variables holds a fixed non-nil error (`membershipInit`). -/
theorem membership.errVar_cell (X msg : GoString)
    (h : (X, msg) ∈ go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ⊢
      ∃ x : Loc, globalAddr X ↦□ interface.mkOk
        (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x := by
  iintro #Hpkg
  ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, #Hev⟩
  ihave #N := EtcdGrove.errorsNewVars_mem h $$ Hev
  iunfold EtcdGrove.errorsNewVar at N
  icases N with ⟨%x, #Hx, -⟩
  iexists x
  iexact Hx

/-- A conf change's `Context` field, borrowed (its slice read-only). -/
theorem ownCCV1_context_acc (p : Loc) (dq : DFrac) (m : CCV1M) :
    ownCCV1 (GF := GF) p dq m ⊢ ∃ cs : GoSlice,
      p.[raftpb.ConfChange, go!"Context"] ↦{dq} cs ∗ cs ↦*□ m.context ∗
      (p.[raftpb.ConfChange, go!"Context"] ↦{dq} cs -∗ ownCCV1 p dq m) := by
  unfold ownCCV1
  iintro H
  iNamed H
  iexists cs
  iframe HC Hcs
  iintro HC
  iexists pt, pn, pi, cs, uf
  simp only [named]
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe #

set_option maxHeartbeats 2000000 in
theorem membership.RaftCluster.ValidateConfigurationChange.wp_proof
    (wp_Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG))
    (wp_GetNodeId : raftpb.ConfChange.GetNodeId.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.ConfChange.GetType.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.ValidateConfigurationChange.spec (GF := GF) (hG := hG) := by
  intro c cc dq m v3 bi Pr mems rmv Hty Hctx
  wp_start as ⟨#Hbe, Hcc, Hrd⟩
  ihave #Hraftpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hjson : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  cases v3
  · -- without `shouldApplyV3`: `nil`
    (try wp_auto)
    iapply HΦ
    iframe Hcc
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  simp only [↓reduceIte]
  icases Hrd with ⟨#Hread, HPr⟩
  iunfold membership.beReadOk at Hread
  (try wp_auto)
  -- `membersMap, removedMap := c.be.MustReadMembersFromBackend()`
  wp_bind (App (Val #(methods bi.ty go!"MustReadMembersFromBackend" bi.v)) (Val #()))
  iapply Hread $$ HPr
  inext
  iintro %mp %rp ⟨HPr, Hmr, Hrm⟩
  (try wp_auto)
  wp_apply wp_GetNodeId.1 cc dq m $$ [$Hraftpb $Hcc] as Hcc
  (try wp_auto)
  -- `if removedMap[id] { return ErrIDRemoved }`
  wp_apply wp_map_lookup1 _ _ rp rmv m.nodeId (DFrac.own 1) $$ [$Hrm] as Hrm
  rw [show (zero_val Bool) = false from rfl]
  cases hr : (rmv !! m.nodeId).getD false
  rotate_left
  · -- a removed id: `ErrIDRemoved`
    icases membership.errVar_cell (GF := GF) _ _ (by simp [go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs]
      : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrIDRemoved, go!"membership: ID removed") ∈ _) $$ Hpkg
      with ⟨%x, #Hx⟩
    (try wp_auto)
    iapply HΦ
    iframe Hcc HPr
    try simp only [↓reduceIte]
    ipureintro
    constructor
    · intro h; cases h
    · intro h; exact absurd h.1 (by rw [hr]; decide)
  (try wp_auto)
  -- `switch cc.GetType()`
  wp_apply wp_GetType.1 cc dq m $$ [$Hraftpb $Hcc] as Hcc
  (try wp_auto)
  rcases Hty with h0 | h1
  · rw [h0]
    (try wp_auto)
    obtain ⟨i, Hci⟩ := Hctx h0
    icases ownCCV1_context_acc cc dq m $$ Hcc with ⟨%cs, HC, #Hcs, Hcc⟩
    (try wp_auto)
    -- `json.Unmarshal(cc.Context, confChangeContext)`: the context's member, not a promotion
    irename «$r0» => Hcv
    wp_apply wp_Unmarshal cs m.context DFrac.discard _ _ i false Hci $$ [$Hjson $Hcs $Hcv]
      as %err ⟨%Herr, -, %v', %pus, Hcv, Hpus, %Hv'⟩
    subst Herr
    obtain ⟨Hvid, Hvprom, Hpus, Hvlrn⟩ := Hv'
    ihave Hcc := Hcc $$ HC
    (try wp_auto)
    rw [Hvprom]
    (try wp_auto)
    -- `if membersMap[id] != nil { return ErrIDExists }`
    iunfold membership.membersRead at Hmr
    icases Hmr with ⟨%ml, Hml, %Hdom, Hmls⟩
    wp_apply wp_map_lookup1 _ _ mp ml m.nodeId (DFrac.own 1) $$ [$Hml] as Hml
    cases hmn : ml !! m.nodeId with
    | some l =>
      -- a member already: `ErrIDExists`
      have hmems : (mems !! m.nodeId).isSome = true := by rw [← Hdom, hmn]; rfl
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun k l => iprop(∃ pus : List GoString,
          ⌜mems !! k = some pus⌝ ∗ membership.memberURLsAt (GF := GF) l pus)) hmn).1 $$ Hmls
        with ⟨⟨%pus0, -, Hl⟩, -⟩
      iunfold membership.memberURLsAt at Hl
      icases Hl with ⟨%pu0, %Hlnn, -⟩
      simp only [Option.getD_some, decide_eq_false Hlnn, Bool.not_false]
      icases membership.errVar_cell (GF := GF) _ _ (by simp [go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs]
        : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrIDExists, go!"membership: ID exists") ∈ _) $$ Hpkg
        with ⟨%x, #Hx⟩
      (try wp_auto)
      iapply HΦ
      iframe Hcc HPr
      try simp only [↓reduceIte]
      ipureintro
      constructor
      · intro h; cases h
      · intro h
        have h2 := h.2
        rw [h0, ite_eq_left rfl] at h2
        rw [h2.1] at hmems
        cases hmems
    | none =>
      simp only [Option.getD_none, show (zero_val Loc) = null from rfl, decide_true, Bool.not_true]
      have hmemN : mems !! m.nodeId = none := by
        have := Hdom m.nodeId; rw [hmn] at this
        cases h : mems !! m.nodeId
        · rfl
        · rw [h] at this; cases this
      (try wp_auto)
      wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %um Hum
      (try wp_auto)
      -- the members' peer URLs into `urls` (a range over the members map)
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(
          ∃ (sl : GoSlice) (ls : List Loc) (x : Loc) (U : GMap GoString Bool),
          "%Hi" ∷ ⌜0 ≤ i ∧ ∀ u, (U !! u).getD false = true ↔
            ∃ k, k ∈ keys.take i.toNat ∧ ∃ pus, mems !! k = some pus ∧ u ∈ pus⌝ ∗
          "members" ∷ members_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* ls ∗
          "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
          "m" ∷ m_ptr ↦ x ∗ "urls" ∷ urls_ptr ↦ um ∗ "Hum" ∷ um ↦$ U ∗
          "Hmls" ∷ ([∗map] k ↦ l ∈ ml, ∃ pus : List GoString, ⌜mems !! k = some pus⌝ ∗
            membership.memberURLsAt (GF := GF) l pus))) $$ Hml
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [members m urls Hum Hmls]
      · iexists slice.nil, [], null, ∅
        simp only [named]
        iframe members m urls Hum Hmls
        isplitl []
        · ipureintro; refine ⟨Int.le_refl _, fun u => ?_⟩; simp
        isplitl []
        · iapply ownSlice_nil
        iapply ownSliceCap_nil
      isplitr
      · imodintro
        iintro %i %key %l ⟨%Hkey, %Hl⟩ HP
        iNamed HP
        (try wp_auto)
        -- `members = append(members, m)`
        wp_apply wp_slice_literal (V := Loc) [l]
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        (try wp_auto)
        wp_apply wp_slice_append (V := Loc) _ _ _ _ _ $$ [$Hsl $Hcap $Hsl2] as %sl3 ⟨Hsl, Hcap, -⟩
        (try wp_auto)
        -- the member's peer URLs
        icases (BigSepM.bigSepM_lookup_acc (Φ := fun k l => iprop(∃ pus : List GoString,
            ⌜mems !! k = some pus⌝ ∗ membership.memberURLsAt (GF := GF) l pus)) Hl).1 $$ Hmls
          with ⟨⟨%pus, %Hpk, Hlu⟩, Hmcl⟩
        iunfold membership.memberURLsAt at Hlu
        icases Hlu with ⟨%pu, %Hlnn, Hpu, Hpus⟩
        (try wp_auto)
        ihave %Hpl := ownSlice_len _ _ _ $$ Hpus
        ihave IH : iprop(∃ (n : w64) (U' : GMap GoString Bool) (uv : GoString),
            "i" ∷ i_ptr ↦ n ∗ "u" ∷ u_ptr ↦ uv ∗ "Hum" ∷ um ↦$ U' ∗
            "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ ∀ u, (U' !! u).getD false = true ↔
              ((U !! u).getD false = true ∨ u ∈ pus.take (sint.nat n))⌝) $$ [i u Hum]
        · iexists W64 0, U, _
          iframe
          ipureintro
          refine ⟨by decide, fun u => ?_⟩
          simp [sint.nat]
        wp_for IH
        wp_if_destruct
        · -- `urls[u] = true` for the `n`th peer URL
          rw [ite_eq_left ⟨Hn.1, Hif⟩]
          have hlt : sint.nat n < pus.length := by have := Hpl.1; word
          obtain ⟨e, He⟩ : ∃ e, pus[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
          wp_apply wp_load_slice_index pu (sint.Z n) pus (DFrac.own 1) e Hn.1 $$ [$Hpus] as Hpus
          · ipureintro; exact He
          (try wp_auto)
          wp_apply wp_mapInsert _ um U' e true $$ [$Hum] as Hum
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, GMap.insert e true U', e
          iframe
          ipureintro
          have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
            show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1
            have : sint.Z (n + W64 1) = sint.Z n + 1 := by word
            rw [this]; omega
          refine ⟨by word, fun u => ?_⟩
          rw [hn1, List.take_add_one, He]
          by_cases hu : u = e
          · subst hu; simp
          · rw [GMap.lookup_insert_ne U' true (Ne.symm hu), Hn.2 u]
            simp [hu]
        · -- every peer URL of the member in: the next key's invariant
          have hall : pus.take (sint.nat n) = pus := by
            apply List.take_of_length_le
            have := Hpl.1
            have : ¬ (sint.Z n < sint.Z pu.len) := Hif
            word
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          have Hpure : 0 ≤ i + 1 ∧ ∀ u, (U' !! u).getD false = true ↔
              ∃ k, k ∈ keys.take (i + 1).toNat ∧ ∃ pus, mems !! k = some pus ∧ u ∈ pus := by
            obtain ⟨Hi0, Hiu⟩ := Hi
            refine ⟨by omega, fun u => ?_⟩
            have htk : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
              rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
            rw [htk, Hn.2 u, hall, Hiu u]
            constructor
            · rintro (⟨k, hk, pus', hp, hu⟩ | hu)
              · exact ⟨k, List.mem_append_left _ hk, pus', hp, hu⟩
              · exact ⟨key, List.mem_append_right _ (List.mem_singleton_self _), pus, Hpk, hu⟩
            · rintro ⟨k, hk, pus', hp, hu⟩
              rcases List.mem_append.1 hk with hk | hk
              · exact .inl ⟨k, hk, pus', hp, hu⟩
              · rw [List.mem_singleton] at hk
                subst hk
                rw [Hpk] at hp
                cases hp
                exact .inr hu
          iexists sl3, ls ++ [l], l, U'
          simp only [named]
          iframe
          isplitr
          · ipureintro; exact Hpure
          iapply Hmcl
          iexists pus
          isplitr
          · ipureintro; exact Hpk
          iunfold membership.memberURLsAt
          iexists pu
          iframe
          ipureintro; exact Hlnn
      -- after the range: `urls` holds exactly the members' peer URLs
      iintro HP Hml
      iNamed HP
      have HU : ∀ u, (U !! u).getD false = true ↔ membership.urlTaken mems u := by
        intro u
        rw [Hi.2 u, show ((GMap.size ml : Nat) : Int).toNat = keys.length by omega,
          List.take_of_length_le (Nat.le_refl _)]
        constructor
        · rintro ⟨k, -, pus, hp, hu⟩; exact ⟨k, pus, hp, hu⟩
        · rintro ⟨k, pus, hp, hu⟩
          refine ⟨k, (Hkset k).2 ?_, pus, hp, hu⟩
          rw [Hdom k, hp]; rfl
      (try wp_auto)
      -- the new member's peer URLs, each checked against `urls`
      ihave %Hpl := ownSlice_len _ _ _ $$ Hpus
      ihave IH : iprop(∃ (n : w64) (uv : GoString),
          "i" ∷ i_ptr ↦ n ∗ "u" ∷ u_ptr ↦ uv ∗ "Hum" ∷ um ↦$ U ∗
          "Hpus" ∷ v'.Member'.RaftAttributes'.PeerURLs' ↦* pus ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ ∀ u, u ∈ pus.take (sint.nat n) → ¬ membership.urlTaken mems u⌝)
        $$ [i u Hum Hpus]
      · iexists W64 0, _
        iframe
        ipureintro
        refine ⟨by decide, fun u hu => ?_⟩
        simp [sint.nat] at hu
      wp_for IH
      wp_if_destruct
      · rw [ite_eq_left ⟨Hn.1, Hif⟩]
        have hlt : sint.nat n < pus.length := by have := Hpl.1; word
        obtain ⟨e, He⟩ : ∃ e, pus[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
        wp_apply wp_load_slice_index _ (sint.Z n) pus (DFrac.own 1) e Hn.1 $$ [$Hpus] as Hpus
        · ipureintro; exact He
        (try wp_auto)
        wp_apply wp_map_lookup1 _ _ um U e (DFrac.own 1) $$ [$Hum] as Hum
        rw [show (zero_val Bool) = false from rfl]
        have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
          show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1
          have : sint.Z (n + W64 1) = sint.Z n + 1 := by word
          rw [this]; omega
        cases hU : (U !! e).getD false
        · -- not a member's: on
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, e
          iframe
          ipureintro
          refine ⟨by word, fun u hu => ?_⟩
          rw [hn1, List.take_add_one, He] at hu
          rcases List.mem_append.1 hu with hu | hu
          · exact Hn.2 u hu
          · simp only [Option.toList_some, List.mem_singleton] at hu
            subst hu
            intro ht
            have := (HU u).2 ht
            rw [hU] at this
            cases this
        · -- a member's: `ErrPeerURLexists`
          icases membership.errVar_cell (GF := GF) _ _ (by simp [go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs]
            : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrPeerURLexists, go!"membership: peerURL exists") ∈ _) $$ Hpkg
            with ⟨%x, #Hx⟩
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iframe Hcc HPr
          ipureintro
          constructor
          · intro h; cases h
          · intro h
            have h2 := h.2
            rw [h0, ite_eq_left rfl] at h2
            have hmem : e ∈ (membership.ccMemberOf m.context).peerURLs := by
              rw [← Hpus]; exact List.mem_of_getElem? He
            exact (h2.2 e hmem ((HU e).1 hU)).elim
      · -- every peer URL free; the learner check (`IsLearner` and an `AddLearnerNode`) fails
        have hall : pus.take (sint.nat n) = pus := by
          apply List.take_of_length_le
          have := Hpl.1
          have : ¬ (sint.Z n < sint.Z v'.Member'.RaftAttributes'.PeerURLs'.len) := by
            exact Hif
          word
        have Hfree : ∀ u, u ∈ pus → ¬ membership.urlTaken mems u := by
          intro u hu; rw [← hall] at hu; exact Hn.2 u hu
        cases hl : v'.Member'.RaftAttributes'.IsLearner'
        · (try wp_auto)
          iapply HΦ
          iframe Hcc HPr
          ipureintro
          refine ⟨fun _ => ⟨hr, ?_⟩, fun _ => rfl⟩
          rw [h0, ite_eq_left rfl]
          exact ⟨hmemN, fun u hu => Hfree u (by rw [Hpus]; exact hu)⟩
        · (try wp_auto)
          wp_apply wp_GetType.1 cc dq m $$ [$Hraftpb $Hcc] as Hcc
          rw [h0]
          (try wp_auto)
          iapply HΦ
          iframe Hcc HPr
          ipureintro
          refine ⟨fun _ => ⟨hr, ?_⟩, fun _ => rfl⟩
          rw [h0, ite_eq_left rfl]
          exact ⟨hmemN, fun u hu => Hfree u (by rw [Hpus]; exact hu)⟩
  · rw [h1]
    (try wp_auto)
    -- a `RemoveNode`: `if membersMap[id] == nil { return ErrIDNotFound }`
    iunfold membership.membersRead at Hmr
    icases Hmr with ⟨%ml, Hml, %Hdom, Hmls⟩
    wp_apply wp_map_lookup1 _ _ mp ml m.nodeId (DFrac.own 1) $$ [$Hml] as Hml
    cases hmn : ml !! m.nodeId with
    | some l =>
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun k l => iprop(∃ pus : List GoString,
          ⌜mems !! k = some pus⌝ ∗ membership.memberURLsAt (GF := GF) l pus)) hmn).1 $$ Hmls
        with ⟨⟨%pus0, -, Hl⟩, -⟩
      iunfold membership.memberURLsAt at Hl
      icases Hl with ⟨%pu0, %Hlnn, -⟩
      simp only [Option.getD_some, decide_eq_false Hlnn]
      (try wp_auto)
      iapply HΦ
      iframe Hcc HPr
      ipureintro
      have hmems : (mems !! m.nodeId).isSome = true := by rw [← Hdom, hmn]; rfl
      refine ⟨fun _ => ⟨hr, ?_⟩, fun _ => rfl⟩
      rw [h1, ite_eq_right (by intro h; cases h)]
      exact hmems
    | none =>
      simp only [Option.getD_none, show (zero_val Loc) = null from rfl, _root_.decide_true]
      icases membership.errVar_cell (GF := GF) _ _ (by simp [go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs]
        : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrIDNotFound, go!"membership: ID not found") ∈ _) $$ Hpkg
        with ⟨%x, #Hx⟩
      (try wp_auto)
      iapply HΦ
      iframe Hcc HPr
      ipureintro
      constructor
      · intro h; cases h
      · intro h
        have h2 := h.2
        rw [h1, ite_eq_right (by intro h; cases h)] at h2
        have := Hdom m.nodeId
        rw [hmn, h2] at this
        cases this

end proof

end EtcdGrove
end Perennial
