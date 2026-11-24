/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapRaftFromCluster.lean` (claim #34,
stage 4, 2026-11-25): this member by name, the peers' loop (each context `json.Marshal` of the member's
clone, `bootGo.memberJSON` of its value: `bootGo.memberJSON_eq`), the log line, the fresh
`MemoryStorage` registered, the record with `raftConfig`'s configuration. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRaftFromCluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftConfig
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__MemoryStorageFresh
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberByNameMem
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__MemberMem
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.encoding.json.MarshalMemberPtr
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Panic
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

attribute [-instance] pure_wp_slice_for_range

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (a copy of `DescribeConfChange.lean`'s, itself of
`Proof/k8s_io/api/DeepCopyBase.lean`'s `wp_slice_for_range`). -/
private theorem wp_slice_for_range_ro {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  unfold slice.forRange
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end loop

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Setting the first zero after a prefix. -/
private theorem set_mid {α : Type} (pre : List α) (k : Nat) (z p : α) :
    (pre ++ List.replicate (k + 1) z).set pre.length p = (pre ++ [p]) ++ List.replicate k z := by
  rw [List.replicate_succ, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
  simp

/-- `raftConfig`'s configuration, at a member id that is neither `0` nor one of raft's local targets,
with more than one election tick, meets `NewRawNode`'s premises (`rnStartCfg`'s configuration part). -/
private theorem raftCfgOf_valid (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (s : Loc) (lok : GoInterfaceOk) (h0 : id ≠ W64 0) (h1 : id ≠ W64 18446744073709551615)
    (h2 : id ≠ W64 18446744073709551614) (he : 1 < sint.Z cfg.ElectionTicks') :
    ConfigValid (raftCfgOf cfg id s lok) := by
  have hs : memStorIface s ≠ interface.nil := by simp [memStorIface, interface.mkOk]
  have hl : (interface.ok lok : GoInterface) ≠ interface.nil := by simp
  simp only [ConfigValid, raftCfgOf]
  refine ⟨h0, h1, h2, ⟨by decide, by
    have : sint.Z (W64 1) = 1 := by decide
    omega⟩, hs, by decide, Or.inl rfl, hl, Or.inl rfl⟩

private theorem raftCfgOf_start (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64)
    (ps : List w64) (bv : bootstrappedRaft) (s : Loc) (lok : GoInterfaceOk) (pv : List Peer)
    (hlg : bv.lg' ≠ null) (hs : bv.storage' = s)
    (hv : ConfigValid (raftCfgOf cfg id s lok))
    (hp : ps = pv.map Peer.ID') (hne : ps ≠ []) :
    rnStartCfg bv (raftCfgOf cfg id s lok) lok pv ps := by
  subst hs
  refine ⟨hlg, hv, rfl, rfl, ?_, rfl, rfl, rfl, Or.inr (by simp [raftCfgOf]), ?_, rfl, rfl, rfl, hp,
    hne⟩
  · simp only [raftCfgOf]; decide
  · simp only [raftCfgOf]; decide

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

theorem bootstrapRaftFromCluster.wp_proof
    (hByName : membership.RaftCluster.MemberByName.specMem (GF := GF) (hG := hG))
    (hMember : membership.RaftCluster.Member.specMem (GF := GF) (hG := hG))
    (hMarshal : encoding.json.MarshalMemberPtr.spec (GF := GF) (hG := hG))
    (hIDStrP : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hIDStr : types.ID.String.spec (GF := GF) (hG := hG))
    (hClID : membership.RaftCluster.ID.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hPanic : zap.Logger.Panic.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hMS : bootstrappedWAL.MemoryStorage.specFresh (GF := GF) (hG := hG))
    (hCfg : raftConfig.spec (GF := GF) (hG := hG)) :
    bootstrapRaftFromCluster.spec (GF := GF) (hG := hG) := by
  intro cfg U cl ids w bw dqi dqw Hcok Hmok Hidr Hune Hst Hents Hsnap
  wp_start as ⟨#Hzlg, Hids, Hw, #Hrc, #Hcid, Hmem, Hauth⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hjpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  ihave %Hlgnn := zapLoggerOk_ne_null _ $$ Hzlg
  ihave %Hidl := ownSlice_len _ _ _ $$ Hids
  have hself := bootGo.memMap_self cfg U Hmok
  wp_auto
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  try wp_auto
  -- `member := cl.MemberByName(cfg.Name)`
  wp_apply (hByName cl (bootGo.memMap U cfg.InitialClusterToken') cfg.Name' (bootGo.id cfg U)
      (bootGo.memberOf U cfg.InitialClusterToken' cfg.Name') hself rfl
      (fun k m' hk hn => bootGo.memMap_names U _ k (bootGo.id cfg U) m' _ hk hself hn))
    $$ [Hmem] as %mb ⟨%mv, Hmb, %Hmbid, Hmem⟩
  · iframe Hmem; iframe #
  icases typedPointsto_not_null_dup _ _ _ $$ Hmb with ⟨Hmb, %Hmbnn⟩
  iStructNamedPrefix Hmb "M"
  try wp_auto
  -- `peers := make([]raft.Peer, len(ids))`
  wp_apply (wp_slice_make2 (V := Peer) (st := go.GoType.SliceType Peer.ty) ids.len) as %psl ⟨Hpsl, -⟩
  · ipureintro; exact Hidl.2
  try wp_auto
  -- the peers' loop
  wp_apply (wp_slice_for_range_ro (V := w64) _ ids (bootGo.ps U cfg.InitialClusterToken') dqi _
    (fun j => iprop(∃ (pre : List Peer) (x y : w64), i_ptr ↦ x ∗ id_ptr ↦ y ∗
      psl ↦* (pre ++ List.replicate ((bootGo.ps U cfg.InitialClusterToken').length - j)
        (zero_val Peer)) ∗
      ⌜pre.length = j ∧ pre.map Peer.ID' = (bootGo.ps U cfg.InitialClusterToken').take j⌝ ∗
      peersCtx pre ((bootGo.ctxs U cfg.InitialClusterToken').take j) ∗
      membership.clusterMem cl (bootGo.memMap U cfg.InitialClusterToken') ∗
      peers_ptr ↦ psl ∗ cl_ptr ↦ cl))) $$ Hids [i id Hpsl Hmem peers cl]
  · iexists [], _, _
    iframe
    isplitl
    · rw [List.nil_append, Nat.sub_zero, Hidl.1]
      iframe
    isplitr
    · ipureintro; simp
    iunfold peersCtx
    simp only [List.take_zero]
    iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).mpr; iempintro
  · imodintro
    iintro %j %x %hx ⟨%pre, %x0, %y0, i, id, Hp, %Hpre, #Hctx, Hmem, peers, cl⟩ Hids
    have hj : j < (bootGo.ps U cfg.InitialClusterToken').length :=
      (List.getElem?_eq_some_iff.1 hx).1
    obtain ⟨mm, hmm, rfl⟩ : ∃ mm, (bootGo.members U cfg.InitialClusterToken')[j]? = some mm ∧
        mm.id = x := by
      simpa [bootGo.ps, List.getElem?_map, Option.map_eq_some_iff] using hx
    have hmem : mm ∈ bootGo.members U cfg.InitialClusterToken' := List.mem_of_getElem? hmm
    have hshape := bootGo.members_shape U _ mm hmem
    try wp_auto
    -- `json.Marshal((*cl).Member(id))`
    wp_apply (hMember cl (bootGo.memMap U cfg.InitialClusterToken') mm.id mm
        (bootGo.memMap_lookup U _ Hmok.2.1 mm hmem)) $$ [Hmem]
      as %ml ⟨%mvl, Hml, Hpu, Hcu, %Hmvl, Hmem⟩
    · iframe Hmem; iframe #
    try wp_auto
    wp_apply (hMarshal ml (DFrac.own 1) mvl (DFrac.own 1) (DFrac.own 1) mm.peerURLs
        mm.clientURLs) $$ [Hml Hpu Hcu] as %csl ⟨Hml, Hpu, Hcu, Hcsl⟩
    · iframe Hml Hpu Hcu
    ipersist Hcsl
    try wp_auto
    -- the context's bytes
    have hpu : mm.peerURLs ≠ [] := bootGo.members_urls U _ Hune mm hmem
    ihave %Hpul := ownSlice_len _ _ _ $$ Hpu
    have Hpunn : mvl.RaftAttributes'.PeerURLs' ≠ slice.nil := by
      intro h; rw [h] at Hpul; apply hpu; apply List.eq_nil_of_length_eq_zero; rw [Hpul.1]; rfl
    have hjson : membership.memberJson mvl mm.peerURLs mm.clientURLs = bootGo.memberJSON mm := by
      rw [bootGo.memberJSON_eq mvl _ _ Hpunn (fun h => absurd hshape.2 h)]
      obtain ⟨h1, h2, h3⟩ := Hmvl
      rw [h1, h2, h3]
    ihave #Hcj : (csl ↦*□ bootGo.memberJSON mm : IProp GF) $$ []
    · rw [← hjson]; iexact Hcsl
    -- `peers[i] = raft.Peer{ID: uint64(id), Context: ctx}`
    ihave %Hpl := ownSlice_len _ _ _ $$ Hp
    have hjn : j + ((bootGo.ps U cfg.InitialClusterToken').length - j) =
        (bootGo.ps U cfg.InitialClusterToken').length := by omega
    have hpl : (bootGo.ps U cfg.InitialClusterToken').length = sint.nat psl.len := by
      rw [← Hpl.1, List.length_append, List.length_replicate, Hpre.1, hjn]
    have hj63 : (j : Int) < sint.Z psl.len := by
      have := Hpl.2; have := hpl; have := hj; word
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    have hc : sint.Z (W64 (j : Int)) < sint.Z psl.len := by word
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    simp only [h0, hc, _root_.and_self]
    wp_apply (wp_store_slice_index (t := Peer.ty) psl (sint.Z (W64 (j : Int))) _
      (Peer.mk mm.id csl)) $$ [Hp] as Hp
    · iframe Hp; ipureintro; constructor
      · exact h0
      · rw [List.length_append, List.length_replicate, Hpre.1, hjn, hpl]; word
    try wp_auto
    have hk : (bootGo.ps U cfg.InitialClusterToken').length - j =
        ((bootGo.ps U cfg.InitialClusterToken').length - (j + 1)) + 1 := by omega
    rw [hsj, hk, ← Hpre.1, set_mid, Hpre.1]
    have hctxs : (bootGo.ctxs U cfg.InitialClusterToken').take (j + 1) =
        (bootGo.ctxs U cfg.InitialClusterToken').take j ++ [bootGo.memberJSON mm] := by
      rw [List.take_add_one]; simp [bootGo.ctxs, List.getElem?_map, hmm]
    iframe Hids
    isplitr
    · ipureintro; rfl
    iexists pre ++ [Peer.mk mm.id csl], W64 (j : Int), mm.id
    iframe Hp Hmem peers cl id i
    isplitr
    · ipureintro
      refine ⟨by simp [Hpre.1], ?_⟩
      rw [List.map_append, Hpre.2, List.take_add_one]
      simp [hx]
    iunfold peersCtx at Hctx
    iunfold peersCtx
    rw [hctxs]
    iapply (BigSepL2.bigSepL2_snoc (PROP := IProp GF)).mpr
    isplitl
    · iexact Hctx
    simp only
    iframe Hcj
    ipureintro; intro h; simp [bootGo.memberJSON] at h
  -- after the loop
  iintro ⟨%pre, %x1, %y1, i, id, Hp, %Hpre, #Hctx, Hmem, peers, cl⟩ Hids
  have hpre : pre.map Peer.ID' = bootGo.ps U cfg.InitialClusterToken' := by
    rw [Hpre.2, List.take_length]
  have hcl : (bootGo.ps U cfg.InitialClusterToken').length =
      (bootGo.ctxs U cfg.InitialClusterToken').length := by simp [bootGo.ps, bootGo.ctxs]
  rw [Nat.sub_self, List.replicate_zero, List.append_nil, hcl, List.take_length]
  have hidps : bootGo.id cfg U ∈ bootGo.ps U cfg.InitialClusterToken' := Hmok.2.2.2
  have hne : bootGo.ps U cfg.InitialClusterToken' ≠ [] := fun h => by rw [h] at hidps; simp at hidps
  try wp_auto
  -- the log line
  wp_apply (hIDStrP _ (DFrac.own 1) mv.ID') $$ [MID] as %s1 ⟨MID, -⟩
  · iframe MID
  wp_apply hStr as %f1 -
  try (· iframe #)
  try wp_auto
  wp_apply (hClID cl (bootGo.cid U cfg.InitialClusterToken')) as -
  try (· iframe #)
  wp_apply (hIDStr (bootGo.cid U cfg.InitialClusterToken')) as %s2 -
  try (· iframe #)
  wp_apply hStr as %f2 -
  try (· iframe #)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl -
  try wp_auto
  wp_apply hInfo
  try (· iframe #)
  try wp_auto
  -- `s := bwal.MemoryStorage()`
  wp_apply (hMS true w dqw bw Hsnap Hst Hents) $$ [Hw]
    as %ms %γs ⟨Hw, %Hsz, #Hlock, #Hd0, Hend, Hnone, Hmeta, Hfresh⟩
  try (· iframe Hw; iframe #)
  try (· iframe Hw)
  try wp_auto
  -- `raftConfig(cfg, uint64(member.ID), s)`
  wp_apply (hCfg cfg mv.ID' ms) as %cfgl ⟨%lok, Hcv, #Hlok⟩
  try (· iframe #)
  try wp_auto
  -- the storage registered
  imod (memStorReg_register (∅ : GMap Loc MemStorNamesRec) ms γs rfl) $$ Hauth with ⟨Hauth, #Hreg⟩
  have hid : mv.ID' = bootGo.id cfg U := Hmbid
  iapply HΦ
  iexists (bootstrappedRaft.mk cfg.Logger' (cfg.TickMs' * W64 1000000) psl cfgl ms)
  iframe
  iunfold bootRaftBuilt
  iexists raftCfgOf cfg mv.ID' ms lok, lok, γs, pre
  iframe
  isplitr
  · ipureintro
    have h0 : mv.ID' ≠ W64 0 := by
      rw [hid]; intro e; rw [e] at hidps; exact Hmok.2.2.1 hidps
    refine ⟨raftCfgOf_start cfg mv.ID' _ _ ms lok pre Hlgnn rfl
      (raftCfgOf_valid cfg mv.ID' ms lok h0 (by rw [hid]; exact Hidr.1) (by rw [hid]; exact Hidr.2)
        Hcok.2.2.2.2) hpre.symm hne, rfl, rfl, ?_⟩
    simp only [raftCfgOf]; exact hid
  ipureintro; exact Hsz

end proof

end EtcdGrove
end Perennial
