/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/BufferClient__Connect.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`b.Connect()` (`Client.Connect` through the embedding, client/client.go): `dialMaster`, the
master's `GetReplicaList` (`callMasterRL`), `findClosest`, no latency table (`defs.LatencyConf`
is `""`: the change log C6 record), the servers/readers/writers slices, the master's `GetLeader`
(`callMasterL`), the alive replicas' indices, and a connection to each (`dial`,
`sp.conn_register` of kind `client cid`, `bufio.NewReader`/`NewWriter`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Connect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.CodecG
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println

-- PORT: lab imports dropped: Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client.cn

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [net.Assumptions] [SwiftNetPkgState netDistGF]
  [net.FieldAssumptions] [net.rpc.Assumptions]

/-- One replica's end while connecting: none yet (a nil connection), or connected (the
`replicaEnd`'s second case). -/
def endI (γ : sp.Names) (γc γm : GName) (cid : w32) (srv : GoInterface) (rd wr : Loc) :
    IProp netDistGF :=
  iprop(⌜srv = interface.nil ∧ rd = null ∧ wr = null⌝ ∨
    ∃ c : Nat, net.rpc.connIface srv c false ∗ sp.connKind γ c (.client cid) ∗
      bufio.ownReader rd srv (recvTokL c false (sp.outQ γ γc γm)) [] ∗
      bufio.ownWriter wr srv (sendTok c false (sp.inP γ γc γm)) (sp.inP γ γc γm c) [] []
        interface.nil)

theorem endI_replicaEnd (γ : sp.Names) (γc γm : GName) (cid : w32) (srv : GoInterface) (rd wr : Loc) :
    endI γ γc γm cid srv rd wr ⊢ client.replicaEnd γ γc γm cid srv rd wr := by
  iintro H
  iapply (client.replicaEnd_unfold _ _ _ _ _ _ _).2
  unfold endI
  icases H with (%H | H)
  · ileft; ipureintro; exact H.2
  · iright; iexact H

theorem endI_srv (γ : sp.Names) (γc γm : GName) (cid : w32) (srv : GoInterface) (rd wr : Loc) :
    endI γ γc γm cid srv rd wr ⊢
      (⌜srv = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface srv c side) := by
  unfold endI
  iintro (%H | ⟨%c, #Hc, -⟩)
  · ileft; ipureintro; exact H.1
  · iright; iexists c, false; iexact Hc

theorem nil_srvs (n : Nat) :
    ⊢ ([∗list] s ∈ List.replicate n (interface.nil : GoInterface),
      (⌜s = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface (GF := netDistGF) s c side) : IProp netDistGF) := by
  induction n with
  | zero => simp only [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · ileft; ipureintro; rfl
    · iapply ih

theorem getD_replicate_null (n idx : Nat) : (List.replicate n null).getD idx null = null := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem endI_init (γ : sp.Names) (γc γm : GName) (cid : w32) (n : Nat) :
    ⊢ [∗list] idx ↦ s ∈ List.replicate n (interface.nil : GoInterface),
      endI γ γc γm cid s ((List.replicate n null).getD idx null)
        ((List.replicate n null).getD idx null) := by
  refine BigSepL.bigSepL_intro (P := (emp : IProp netDistGF)) fun k x hx => ?_
  have hx' : x = interface.nil := List.eq_of_mem_replicate (List.mem_of_getElem? hx)
  subst hx'
  rw [getD_replicate_null]
  unfold endI
  iintro -
  ileft; ipureintro; exact ⟨rfl, rfl, rfl⟩

/-- A replica's end, as a triple (connection, reader, writer). -/
abbrev endT (γ : sp.Names) (γc γm : GName) (cid : w32) (t : GoInterface × Loc × Loc) :
    IProp netDistGF :=
  endI γ γc γm cid t.1 t.2.1 t.2.2

theorem endT_init (γ : sp.Names) (γc γm : GName) (cid : w32) (n : Nat) :
    ⊢ [∗list] t ∈ List.replicate n ((interface.nil : GoInterface), null, null), endT γ γc γm cid t := by
  induction n with
  | zero => simp only [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; itrivial
  | succ n ih =>
    rw [List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · unfold endT endI; ileft; ipureintro; exact ⟨rfl, rfl, rfl⟩
    · iapply ih

theorem ends_final (γ : sp.Names) (γc γm : GName) (cid : w32) (ts : List (GoInterface × Loc × Loc)) :
    ([∗list] t ∈ ts, endT γ γc γm cid t) ⊢
      [∗list] i ↦ s ∈ ts.map Prod.fst, client.replicaEnd γ γc γm cid s
        ((ts.map (fun t => t.2.1)).getD i null) ((ts.map (fun t => t.2.2)).getD i null) := by
  rw [BigSepL.bigSepL_map]
  refine BigSepL.bigSepL_mono fun {k x} hx => ?_
  have h1 : (ts.map (fun t => t.2.1)).getD k null = x.2.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]; rfl
  have h2 : (ts.map (fun t => t.2.2)).getD k null = x.2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]; rfl
  rw [h1, h2]
  exact endI_replicaEnd γ γc γm cid x.1 x.2.1 x.2.2

theorem ends_failed (γ : sp.Names) (γc γm : GName) (cid : w32) (ts : List (GoInterface × Loc × Loc)) :
    ([∗list] t ∈ ts, endT γ γc γm cid t) ⊢
      [∗list] s ∈ ts.map Prod.fst, (⌜s = interface.nil⌝ ∨ ∃ c side, net.rpc.connIface s c side) := by
  rw [BigSepL.bigSepL_map]
  exact BigSepL.bigSepL_mono fun {_ x} _ => endI_srv γ γc γm cid x.1 x.2.1 x.2.2

end defs

end client.cn

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [client.Assumptions] [examples.swiftnet.Assumptions]
variable [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr netDistGF] [RpcHttpHyp netDistGF]
variable [bufio.Assumptions] [replica.defs.Assumptions] [dlog.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodec` for the frozen statement,
-- `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF]

set_option goose.wp.extras true

set_option hygiene false in
/-- `c.Println(...)` on the client's quiet logger (`Hq`). -/
local macro "println" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨-, -⟩
  (try wp_auto)
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_Println $$ Hq
  (try wp_auto)))

/-- `Connect` over the codec `C` (`Connect.specG`, Proof/client/CodecG.lean). -/
theorem client.BufferClient.Connect.wp_proofG (facts : swift.handler.ClientPkgFacts (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_dialMaster : client.Client.dialMaster.specI (hG := hG))
    (wp_callMasterRL : client.Client.callMasterRL.specI (hG := hG))
    (wp_callMasterL : client.Client.callMasterL.specI (hG := hG))
    (wp_findClosest : client.Client.findClosest.specI (hG := hG))
    (wp_dial : client.Client.dial.specI (hG := hG)) :
    client.BufferClient.Connect.specG (hG := hG) := by
  intro b cid maddr mport W γ γc γm γl
  wp_start as ⟨Hbf, %Haddr, #Hra, %HSS, #Hcs, #Hko, #Hprotos, #Hinv⟩
  ihave Hbf := (client.bufFresh_unfold _ _ _ _).1 $$ Hbf
  icases Hbf with ⟨%bv, %v, #Hb, Hcl, #Hq, %Hv, %γch, #Hch, Hoch⟩
  obtain ⟨Hcnn, Hseq, Hcid, Hma, Hmp, Hsn, Hfast, Hll, Hmnull, Hdt, Hping, Hsrv⟩ := Hv
  ihave #Hbf := Hb
  iStructNamed Hbf
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  println
  wp_apply wp_dialMaster bv.Client' v W $$ [$Hcl $Hq $Hra] as %m %err Hd
  · ipureintro; exact ⟨Hmnull, by rw [Hma, Hmp]; exact Haddr⟩
  icases Hd with (⟨%Herr, Hcl, #Hmc⟩ | ⟨%Herr, Hcl⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Herr
    iapply (client.failedG_unfold b).2
    iexists bv, v
    iframe Hb Hcl Hq
    isplitr
    · ipureintro; exact Hcnn
    isplitr
    · ileft; ipureintro; exact Hmnull
    iexists []
    rw [Hsrv]
    isplitl
    · iapply ownSlice_nil
    iapply BigSepL.bigSepL_nil.2; itrivial
  subst Herr
  wp_auto
  println
  wp_apply wp_callMasterRL bv.Client' _ W γc γm $$ [$Hcl $Hq $Hcs $Hko $Hmc] as %res %err ⟨Hcl, Hres⟩
  · ipureintro; exact HSS
  icases Hres with (⟨%Herr, %p, %s1, %s2, %nodes, %alive, %fr, %Hres, Hp, Hs1, Hs2, #Hcfg, %Hal⟩ | %Herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Herr
    iapply (client.failedG_unfold b).2
    iexists bv, _
    iframe Hb Hcl Hq
    isplitr
    · ipureintro; exact Hcnn
    isplitr
    · iright; iexists W, masterAddr; iexact Hmc
    iexists []
    rw [Hsrv]
    isplitl
    · iapply ownSlice_nil
    iapply BigSepL.bigSepL_nil.2; itrivial
  subst Herr Hres
  wp_auto
  println
  wp_apply wp_findClosest bv.Client' _ s2 alive nodes (DFrac.own 1) (DFrac.own 1)
    $$ [$Hcl $Hq $Hs1 $Hs2] as %err ⟨%Herr, ⟨%pg, %ci, Hcl⟩, Hs1, Hs2⟩
  · ipureintro; exact ⟨Hping, Hal⟩
  ihave Hcl : bv.Client' ↦ ({ v with master' := m, replicas' := s1, Ping' := pg, ClosestId' := ci } : client.Client) $$ [Hcl]
  · iExactEq Hcl; rfl
  subst Herr
  wp_auto
  println
  println
  ihave #Hdefs : (isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.replica.defs) $$ []
  · solve_pkg_init
  ihave #Hlat := facts.latencyConf $$ Hdefs
  ihave %Hs1l := ownSlice_len _ _ _ $$ Hs1
  wp_apply (IntoValTyped.wp_load (t := go.string) (globalAddr replica.defs.LatencyConf)
    DFrac.discard (go!"" : GoString)) $$ [$Hlat] as -
  wp_apply (wp_slice_make2 (V := GoInterface)) as %ssl ⟨Hssl, -⟩
  · ipureintro; word
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc)) as %rsl ⟨Hrsl, -⟩
  · ipureintro; word
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc)) as %wsl ⟨Hwsl, -⟩
  · ipureintro; word
  try wp_auto
  ihave Hcl : bv.Client' ↦ ({ v with master' := m, replicas' := s1, Ping' := pg, ClosestId' := ci, dt' := null, servers' := ssl, readers' := rsl, writers' := wsl } : client.Client) $$ [Hcl]
  · iExactEq Hcl; rfl
  rw [Hll]
  wp_auto
  println
  wp_apply wp_callMasterL bv.Client' _ W γc γm $$ [$Hcl $Hq $Hcs $Hko $Hmc] as %res %err ⟨Hcl, Hres⟩
  · ipureintro; exact HSS
  icases Hres with (⟨%Herr, %p2, %lid, %Hres, Hp2⟩ | %Herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Herr
    iapply (client.failedG_unfold b).2
    iexists bv, _
    iframe Hb Hcl Hq
    isplitr
    · ipureintro; exact Hcnn
    isplitr
    · iright; iexists W, masterAddr; iexact Hmc
    iexists _
    iframe Hssl
    iapply client.cn.nil_srvs
  subst Herr Hres
  wp_auto
  println
  wp_apply (wp_slice_literal (V := w64) [])
  isplitr
  · ipureintro; rfl
  iintro %csl0 ⟨Hcsl, Hcslc⟩
  wp_auto
  ihave %Hs2l := ownSlice_len _ _ _ $$ Hs2
  ihave HI : (∃ (i : w64) (csl : GoSlice) (cs : List w64), "Hi" ∷ i_ptr ↦ i ∗
      "Hconn" ∷ connect_ptr ↦ csl ∗ "Hcsl" ∷ csl ↦* cs ∗
      "Hcslc" ∷ ownSliceCap w64 csl (DFrac.own 1) ∗
      "%Hcs" ∷ ⌜∀ j ∈ cs, 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s1.len⌝ ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s1.len⌝ : IProp netDistGF) $$ [i connect Hcsl Hcslc]
  · iexists _, _, []
    iframe
    ipureintro; constructor
    · intro j hj; simp at hj
    · word
  wp_for HI
  wp_if_destruct
  · have hiA : sint.nat i < alive.length := by rw [Hal]; word
    list_elem alive (sint.nat i) as al
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    wp_apply wp_load_slice_index s2 (sint.Z i) alive (DFrac.own 1) al Hi.1 $$ [Hs2] as Hs2
    · iframe Hs2; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hal_lookup
    cases al
    · wp_auto
      wp_for_post
      iframe
      iexists _, csl, cs
      iframe
      ipureintro; exact ⟨Hcs, by word⟩
    · wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %isl ⟨Hisl, -⟩
      wp_apply wp_slice_append csl cs _ _ (DFrac.own 1) $$ [$Hcsl $Hcslc $Hisl] as %csl' ⟨Hcsl, Hcslc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists _, csl', _
      iframe
      ipureintro
      refine ⟨fun j hj => ?_, by word⟩
      rcases List.mem_append.1 hj with h | h
      · exact Hcs j h
      · simp at h; subst h; word
  rename_i ik_ptr
  irename : (ik_ptr ↦ (Perennial.zero_val w64 : w64)) => Hk
  ihave %Hcsll := ownSlice_len _ _ _ $$ Hcsl
  ihave Hmem := sp.cfg_memIs (γc := γc) (γm := γm) _ _ _ $$ Hcfg
  icases Hmem with ⟨#Hm, %-⟩
  ihave %Hok := memIs_ok γm nodes $$ Hm
  ihave Hends := client.cn.endT_init γ γc γm cid (sint.nat s1.len)
  ihave HJ : (∃ (j k : w64) (e : GoInterface) (ts : List (GoInterface × Loc × Loc)),
      "Hj" ∷ i_ptr ↦ j ∗ "Hk" ∷ ik_ptr ↦ k ∗ "err" ∷ err_ptr ↦ e ∗
      "Hssl" ∷ ssl ↦* ts.map Prod.fst ∗ "Hrsl" ∷ rsl ↦* ts.map (fun t => t.2.1) ∗
      "Hwsl" ∷ wsl ↦* ts.map (fun t => t.2.2) ∗
      "Hends" ∷ ([∗list] t ∈ ts, client.cn.endT γ γc γm cid t) ∗
      "%Hts" ∷ ⌜ts.length = nodes.length⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z csl.len⌝ : IProp netDistGF)
      $$ [i Hk err Hssl Hrsl Hwsl Hends]
  · iexists _, _, _, List.replicate (sint.nat s1.len) ((interface.nil : GoInterface), null, null)
    iframe
    simp only [List.map_replicate]
    iframe
    iframe Hends
    ipureintro; constructor
    · simp only [List.length_replicate]; exact Hs1l.1.symm
    · word
  wp_for HJ
  wp_if_destruct
  · have hjN : sint.nat j < cs.length := by rw [Hcsll.1]; word
    list_elem cs (sint.nat j) as x
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, by word⟩)]
    wp_apply wp_load_slice_index csl (sint.Z j) cs (DFrac.own 1) x Hj.1 $$ [Hcsl] as Hcsl
    · iframe Hcsl; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hx_lookup
    have hx := Hcs x (List.mem_of_getElem? Hx_lookup)
    have hxN : sint.nat x < nodes.length := by rw [Hs1l.1]; word
    list_elem nodes (sint.nat x) as a
    have hxb : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z s1.len := hx
    have hxl : (sint.Z x).toNat = sint.nat x := rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxb)]
    wp_apply wp_load_slice_index s1 (sint.Z x) nodes (DFrac.own 1) a hxb.1 $$ [Hs1] as Hs1
    · iframe Hs1; ipureintro; rw [hxl]; exact Ha_lookup
    try wp_auto
    println
    ihave %Hssll := ownSlice_len _ _ _ $$ Hssl
    ihave %Hrsll := ownSlice_len _ _ _ $$ Hrsl
    ihave %Hwsll := ownSlice_len _ _ _ $$ Hwsl
    simp only [List.length_map] at Hssll Hrsll Hwsll
    have hxs : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z ssl.len := by
      constructor; word
      have := Hssll.1; have := Hs1l.1; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxs)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxb)]
    wp_apply wp_load_slice_index s1 (sint.Z x) nodes (DFrac.own 1) a hxb.1 $$ [Hs1] as Hs1
    · iframe Hs1; ipureintro; rw [hxl]; exact Ha_lookup
    have haR : a ∈ replicaAddrs := Hok.2 a (List.mem_of_getElem? Ha_lookup)
    icases (BigSepL.bigSepL_mem_acc haR) $$ Hprotos with ⟨#Hpa, -⟩
    wp_apply wp_dial bv.Client' _ a (sp.inP γ γc γm) (sp.outQ γ γc γm) $$ [$Hcl $Hq $Hpa]
      as %cv %e2 ⟨Hcl, Hdr⟩
    have hxts : sint.nat x < ts.length := by rw [Hts]; exact hxN
    obtain ⟨t0, ht0⟩ : ∃ t0, ts[sint.nat x]? = some t0 :=
      ⟨_, List.getElem?_eq_getElem hxts⟩
    wp_apply wp_store_slice_index ssl (sint.Z x) (ts.map Prod.fst) cv $$ [$Hssl] as Hssl
    · ipureintro; constructor; word; simp only [List.length_map]; rw [Hts]; have := Hs1l.1; word
    rw [hxl]
    icases Hdr with (⟨%c0, %cid0, ⟨%Hcv, %He2⟩, #Hown, Hend, Hfr⟩ | ⟨%Hcv, %He2⟩)
    rotate_left
    · subst Hcv
      cases e2 with
      | nil => exact absurd rfl He2
      | ok ei => ?_
      wp_auto
      wp_for_post
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact He2
      iapply (client.failedG_unfold b).2
      iexists bv, _
      iframe Hb Hcl Hq
      isplitr
      · ipureintro; exact Hcnn
      isplitr
      · iright; iexists W, masterAddr; iexact Hmc
      iexists _
      iframe Hssl
      ihave Hf := client.cn.ends_failed γ γc γm cid ts $$ Hends
      have ht0' : (ts.map Prod.fst)[sint.nat x]? = some t0.1 := by
        rw [List.getElem?_map, ht0]; rfl
      icases (BigSepL.bigSepL_insert_acc ht0') $$ Hf with ⟨-, Hback⟩
      iapply Hback
      ileft; ipureintro; rfl
    obtain ⟨rfl, rfl⟩ := And.intro Hcv He2
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    wp_auto
    have hcv : ((ts.map Prod.fst).set (sint.nat x)
        (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c0))[(sint.Z x).toNat]? =
        some (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c0) := by
      rw [hxl, List.getElem?_set_self]; simp only [List.length_map]; exact hxts
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxs)]
    wp_apply wp_load_slice_index ssl (sint.Z x) _ (DFrac.own 1) _ hxs.1 $$ [Hssl] as Hssl
    · iframe Hssl; ipureintro; exact hcv
    ihave Hreg := sp.conn_register (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by simp) cid0
      (.client cid) $$ [$Hinv $Hfr]
    iapply fupd_wp
    imod Hreg with #Hkind
    imodintro
    ihave #Hci : net.rpc.connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c0)
      cid0 false $$ []
    · ihave #Hown' := Hown
      iunfold net.ownTCPConn at Hown'
      icases Hown' with ⟨%a0, %la0, %ra0, #Hat0, #Hcs0⟩
      unfold net.rpc.connIface; iexists c0, a0, la0, ra0; iframe Hat0 Hcs0; ipureintro; rfl
    ihave #Hnet : (isPkgInit (PROP := IProp netDistGF) pkg_id.net) $$ []
    · solve_pkg_init
    ihave #Hbufio : (isPkgInit (PROP := IProp netDistGF) pkg_id.bufio) $$ []
    · solve_pkg_init
    ihave #Hrdok := bufio.readerOk_conn _ cid0 false (sp.outQ γ γc γm) $$ [$Hnet $Hci]
    ihave Hrecv := recvTok_L _ _ _ _ $$ Hrecv
    wp_apply bufio.wp_NewReader _ _ [] $$ [$Hbufio $Hrdok $Hrecv] as %br Hrd
    have hxr : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z rsl.len := by
      constructor; word
      have := Hrsll.1; have := Hs1l.1; word
    have hxw : 0 ≤ sint.Z x ∧ sint.Z x < sint.Z wsl.len := by
      constructor; word
      have := Hwsll.1; have := Hs1l.1; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxr)]
    wp_apply wp_store_slice_index rsl (sint.Z x) _ br $$ [$Hrsl] as Hrsl
    · ipureintro; constructor; word; simp only [List.length_map]; rw [Hts]; have := Hs1l.1; word
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxs)]
    wp_apply wp_load_slice_index ssl (sint.Z x) _ (DFrac.own 1) _ hxs.1 $$ [Hssl] as Hssl
    · iframe Hssl; ipureintro; exact hcv
    ihave #Hpc := sp.inP_prefixClosed (γ := γ) (γc := γc) (γm := γm) cid0
    ihave #Hpc' : (bufio.prefixClosed (sp.inP γ γc γm cid0) : IProp netDistGF) $$ []
    · unfold bufio.prefixClosed; imodintro; iexact Hpc
    ihave #Hwok := bufio.writerOk_conn _ cid0 false (sp.inP γ γc γm) $$ [$Hnet $Hci $Hpc']
    ihave #Hq0 := sp.inP_nil (γ := γ) (γc := γc) (γm := γm) cid0
    try wp_auto
    wp_apply bufio.wp_NewWriter _ _ _ [] $$ [$Hbufio $Hwok $Hsend $Hq0] as %bw Hw
    rw [ite_eq_left_of_eq_true _ _ (eq_true hxw)]
    wp_apply wp_store_slice_index wsl (sint.Z x) _ bw $$ [$Hwsl] as Hwsl
    · ipureintro; constructor; word; simp only [List.length_map]; rw [Hts]; have := Hs1l.1; word
    icases (BigSepL.bigSepL_insert_acc ht0) $$ Hends with ⟨-, Hback⟩
    ihave Hends := Hback $$ %(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c0, br, bw) [Hrd Hw]
    · unfold client.cn.endT client.cn.endI
      iright
      iexists cid0
      iframe Hci Hkind Hrd Hw
    wp_for_post
    iframe
    iexists _, _, _, ts.set (sint.nat x) (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c0, br, bw)
    simp only [List.map_set, hxl]
    iframe
    ipureintro
    exact ⟨by rw [List.length_set]; exact Hts, by word⟩
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists nodes.length
    iapply (client.connected_unfold _ _ _ _ _ _).2
    iexists bv, _, nodes, fr, ts.map Prod.fst, ts.map (fun t => t.2.1), ts.map (fun t => t.2.2)
    iframe Hb Hcl Hq Hcfg Hs1 Hssl Hrsl Hwsl
    isplitr
    · ipureintro
      refine ⟨Hcnn, Hseq, Hcid, Hsn, Hfast, rfl, rfl, ?_, ?_, ?_⟩ <;> simp [Hts]
    isplitl [Hends]
    · iapply client.cn.ends_final $$ Hends
    iexists γch
    iframe Hch Hoch

end proof

section frozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [client.Assumptions] [examples.swiftnet.Assumptions]
variable [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr netDistGF] [RpcHttpHyp netDistGF]
variable [bufio.Assumptions] [replica.defs.Assumptions] [dlog.Assumptions]

/-- The frozen statement: `Connect.wp_proofG` at `kitCodec`. -/
theorem client.BufferClient.Connect.wp_proof (facts : swift.handler.ClientPkgFacts (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_dialMaster : client.Client.dialMaster.specI (hG := hG))
    (wp_callMasterRL : client.Client.callMasterRL.specI (hG := hG))
    (wp_callMasterL : client.Client.callMasterL.specI (hG := hG))
    (wp_findClosest : client.Client.findClosest.specI (hG := hG))
    (wp_dial : client.Client.dial.specI (hG := hG)) :
    client.BufferClient.Connect.spec (hG := hG) :=
  client.BufferClient.Connect.spec_of_G
    (client.BufferClient.Connect.wp_proofG facts wp_Println wp_dialMaster wp_callMasterRL
      wp_callMasterL wp_findClosest wp_dial)

end frozen

end Perennial.github_com.imdea_software.swiftpaxos
