/-
The hraft kit's orchestrator's vocabulary (notes/dsv-hraft.md, S5g):

* the masks of remote's `Check` (`pendN_kit`, `lintestN_kit`);
* `drawPre K`: what the orchestrator draws with, from the start: both sizes' protocol ghost state
  before its receipts (`gprot.alloc_names`'s `opsAuth`, `allocPre`), the clients' state before the
  draw (`kitPre`) and the frontier's list, empty;
* **`kit_draw`**: with the draw's token, a credit and two receipts, the orchestrator draws `n`
  (`chosen γc n`, persistent) and closes the draw's invariant in its drawn branch, with every
  server's package of the drawn protocol (`gprot.alloc_init`, `frInv_init`, `kitQ_linStep`); it
  keeps the drawn protocol's servers (`srvsOf`, for the admin's requests);
* `adminCtx K`: what the admin goroutine calls the servers' API with;
* `orchShare K γp`: the orchestrator's share of the start.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerShare
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ModelDefs
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireLen
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecDefs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto rpctransport

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Masks -/

theorem pendN_kit : (↑pendN : CoPset) ⊆ ⊤ \ kitE := by
  unfold kitE pendN remoteN service.frN escN; solve_ndisj

theorem lintestN_kit : (↑EtcdGrove.lintest.lintestN : CoPset) ⊆ ⊤ \ (kitE ∪ ↑pendN) := by
  unfold kitE pendN remoteN service.frN escN EtcdGrove.lintest.lintestN; solve_ndisj

/-! ## The six servers -/

theorem allSids_bigSepL {PROP : Type _} [BI PROP] (P : SID → PROP) :
    ([∗list] i ∈ allSids, P i) = [∗list] j ∈ List.range' 1 6, P (sidOf (W64 ((j : Nat) : Int))) := by
  unfold allSids sidsUpTo
  rw [BigSepL.bigSepL_map, List.range'_eq_map_range, BigSepL.bigSepL_map]
  have h : ∀ x : Nat, 1 + x = x + 1 := fun x => Nat.add_comm 1 x
  simp only [h]


/-! ## The admin's requests -/

section pure
variable [GooseExts]

/-- `adminMethods()`'s methods, by kind. -/
def adminMeths : List GoString :=
  [go!"API.AddVoter", go!"API.AddNonvoter", go!"API.DemoteVoter", go!"API.RemoveServer",
    go!"API.LeadershipTransfer", go!"API.Snapshot"]

/-- The admin's request of kind `k` naming server `s`: `s`'s ID at its address, or (a transfer,
`k = 4`) the empty ID. -/
def adminReq (k s : Nat) (v : AdminArgsV) : Prop :=
  1 ≤ s ∧ s ≤ 6 ∧
    (v = ⟨sidOf (W64 (s : Int)), sidOf (W64 (s : Int))⟩ ∨ (k = 4 ∧ v = ⟨[], []⟩))

theorem fStr_le (s : List w8) : (rpctransport.fStr s).length ≤ 9 + s.length :=
  Nat.le_trans (rpctransport.fld_le _ _)
    (by simp only [rpctransport.encStr, List.length_append, u64Le_length]; omega)

theorem encAdminArgs_length (v : AdminArgsV) (h1 : v.id.length ≤ 1000)
    (h2 : v.addr.length ≤ 1000) : (encAdminArgs v).length ≤ net.rpc.maxFrameN := by
  have hF := rpctransport.maxFrameN_eq
  have := fStr_le v.id
  have := fStr_le v.addr
  unfold encAdminArgs rpctransport.tagged rpctransport.encStr rpctransport.strct
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_cons,
    List.length_nil, u64Le_length, List.append_nil]
  omega

theorem adminReq_length (k s : Nat) (v : AdminArgsV) (h : adminReq k s v) :
    (encAdminArgs v).length ≤ net.rpc.maxFrameN := by
  obtain ⟨h1, h6, hv⟩ := h
  have hl : (sidOf (W64 (s : Int))).length = 1 := sidOf_length s (by omega)
  rcases hv with rfl | ⟨-, rfl⟩
  · exact encAdminArgs_length _ (by simp only [hl]; omega) (by simp only [hl]; omega)
  · exact encAdminArgs_length _ (by simp) (by simp)

theorem adminMeths_len (sm : GoString) (h : sm ∈ adminMeths) :
    sm.length + 16 ≤ net.rpc.maxFrameN := by
  rw [rpctransport.maxFrameN_eq]
  simp only [adminMeths, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [package_sem : github_com.hashicorp.raft.Assumptions]

/-- One size's protocol before its receipts (`gprot.alloc_names`'s). -/
def drawPre1 (K : HK GF) (m : Nat) : IProp GF := iprop(opsAuth (K.γs m) ∅ ∗ allocPre (K.γs m))

/-- **What the orchestrator draws with**: both sizes' protocols before their receipts, the clients'
state before the draw, the frontier's list (empty). -/
def drawPre (K : HK GF) : IProp GF :=
  iprop(drawPre1 K 3 ∗ drawPre1 K 5 ∗ kitPre K.g ∗ monoListAuthOwn (A := proto.Entry) K.fr 1 [])

/-- The drawn protocol's six servers. -/
def srvsOf (K : HK GF) (n : Nat) : IProp GF :=
  iprop([∗list] j ∈ List.range' 1 6, isSrv (K.γs n) (sidOf (W64 ((j : Nat) : Int))))

instance srvsOf_persistent (K : HK GF) (n : Nat) : Persistent (srvsOf K n) := by
  unfold srvsOf; infer_instance

/-- **What the admin goroutine calls the servers' API with**: the world's services and the server
addresses, the draw and the drawn protocol's servers. -/
def adminCtx (K : HK GF) : IProp GF :=
  iprop(⌜kitSS K ∧ γsOk K⌝ ∗ ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ∗
    ∃ n : Nat, ⌜N0Ok n⌝ ∗ chosen K.γc n ∗ srvsOf K n)

instance adminCtx_persistent (K : HK GF) : Persistent (adminCtx K) := by
  unfold adminCtx; infer_instance

theorem bundles_split (γ : GNames) (hs : γ.srvs = allSids) :
    ([∗list] i ∈ γ.srvs, srvBundle (GF := GF) γ i) ⊢
      ([∗list] j ∈ List.range' 1 6, srvBundle γ (sidOf (W64 ((j : Nat) : Int)))) ∗
      [∗list] j ∈ List.range' 1 6, isSrv γ (sidOf (W64 ((j : Nat) : Int))) := by
  rw [hs, allSids_bigSepL]
  iintro H
  iapply BigSepL.bigSepL_sep_eqv.1
  iapply BigSepL.bigSepL_mono (fun _ => ?_) $$ H
  unfold srvBundle
  iintro ⟨#Hv, H⟩
  isplitl
  · iframe Hv H
  · iexact Hv

/-- The first configuration's voters are a valid configuration over the six servers. -/
theorem cfgValid_boot (n : Nat) (hn : N0Ok n) :
    cfgValid allSids (cfgDec allSids (encodeServers (bootSrvs n))) := by
  have hn6 : 1 ≤ n ∧ n ≤ 6 := by unfold N0Ok at hn; omega
  rw [cfgDec_encode _ _ (srvsOkIn_bootSrvs n hn6), srvVoters_bootSrvs]
  refine ⟨?_, sidsUpTo_nodup n (by omega), ?_⟩
  · unfold sidsUpTo
    have : n ≠ 0 := by omega
    simp [this]
  · intro j hj
    unfold sidsUpTo at hj
    simp only [List.mem_map, List.mem_range] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact sidOf_mem_allSids (k + 1) ⟨by omega, by omega⟩

/-- **The draw**: with the draw's token, the protocols before their receipts, two receipts and a
credit, the orchestrator draws `n` for good and hands every server its package of the drawn
protocol (the draw's invariant's drawn branch); it keeps the drawn protocol's servers. -/
theorem kit_draw [hRB : ReceiptBoundLe GF (2 ^ 62)] (K : HK GF) (n : Nat) (hn : N0Ok n)
    (hγ : γsOk K) :
    £ 1 ∗ drawInv K ∗ drawTok K ∗ drawPre K ∗ ⧗ 2 ⊢ |={⊤}=> chosen K.γc n ∗ srvsOf K n := by
  iintro ⟨Hlc, #Hinv, Htok, Hpre, Hr⟩
  obtain ⟨hs, hg, hcv⟩ := hγ n hn
  unfold drawPre
  icases Hpre with ⟨H3, H5, Hkp, Hfr⟩
  ihave Hd : drawPre1 K n $$ [H3 H5]
  · rcases hn with rfl | rfl
    · iexact H3
    · iexact H5
  unfold drawPre1
  icases Hd with ⟨Hops, Hap⟩
  have hnd : (K.γs n).srvs.Nodup := by rw [hs]; exact allSids_nodup
  have hne : ∀ j ∈ (K.γs n).srvs, j ≠ [] := by rw [hs]; exact allSids_ne_nil
  have hg1 : (K.γs n).g.term = 1 := by rw [hg]; rfl
  have hgk : (K.γs n).g.kind = kConfig := by rw [hg]; rfl
  have hcvv : cfgValid (K.γs n).srvs ((K.γs n).cv (K.γs n).g.data) := by
    rw [hs, hcv, hg]; exact cfgValid_boot n hn
  imod alloc_init (K.γs n) ⊤ hnd hne hg1 hgk hcvv $$ [Hap Hr] with ⟨#HI, Hsrvs⟩
  · iframe Hap Hr
  imod frInv_init (K.γs n) K.g K.fr $$ [HI Hops Hkp Hfr] with #Hfi0
  · iframe HI Hops Hkp Hfr
  ihave #Hfi : service.frInv (K.γs n) (K.fcs n) $$ [Hfi0]
  · unfold HK.fcs; iexact Hfi0
  ihave #Hls0 := kitQ_linStep (K.γs n) K.g K.fr
  ihave #Hls : service.linStep (K.γs n) (K.fcs n) $$ [Hls0]
  · unfold HK.fcs; iexact Hls0
  ihave ⟨Hb, #Hsv⟩ := bundles_split (K.γs n) hs $$ [Hsrvs]
  · unfold srvBundle; iexact Hsrvs
  unfold drawInv
  iinv Hinv with ⟨%m, >Ha, Hcase⟩ Hclose
  imod lc_fupd_elim_later $$ Hlc Hcase with Hcase
  icases Hcase with (%Hm | ⟨%n', %Hm, Hd, -, -⟩)
  rotate_left
  · unfold drawTok
    ihave %hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hd Htok
    exfalso
    have := DFrac.valid_op_own hv.1
    simp at this
  subst Hm
  imod ghost_map_insert_persist (GF := GF) (K := Nat) (V := Nat) 0 n (by simp) $$ Ha with ⟨Ha, #Hc⟩
  imod Hclose $$ [Ha Htok Hb] with -
  · inext
    iexists _
    iframe Ha
    iright
    iexists n
    isplitr; · ipureintro; rfl
    iframe Htok Hfi
    iapply (BigSepL.bigSepL_impl (Φ := fun _ j => srvBundle (K.γs n) (sidOf (W64 ((j : Nat) : Int))))) $$ Hb
    imodintro
    iintro %k %j %hk Hj
    ileft
    unfold srvPkg
    iframe HI Hj Hfi Hls
  imodintro
  isplitr
  · unfold chosen; iexact Hc
  · unfold srvsOf; iexact Hsv


/-- What the admin's calls get back: an `AdminReply`'s encoding, when successful. -/
def adminAns : List w8 → GoString → IProp GF :=
  fun rep msg => iprop(⌜msg = [] → ∃ r : AdminReplyV, rep = encAdminReply r⌝)

/-- What a `Status` call gets back: a `StatusReply`'s encoding, when successful. -/
def statusAns : List w8 → GoString → IProp GF :=
  fun rep msg => iprop(⌜msg = [] → ∃ r : StatusReplyV, rep = encStatusReply r⌝)

theorem answers_admin :
    ⊢ answers (fun rep => iprop(∃ r : AdminReplyV, ⌜rep = encAdminReply r⌝))
      (adminAns (GF := GF)) := by
  unfold answers adminAns
  isplitl
  · iintro %rep ⟨%r, %h⟩; ipureintro; intro _; exact ⟨r, h⟩
  · iintro %msg %hmsg; ipureintro; intro h; exact absurd h hmsg

/-- **The admin's request's deposit** at the servers' API (`apiSvcK`), from what the admin knows. -/
theorem admin_dep (K : HK GF) (k s : Nat) (hk : k < 6) (v : AdminArgsV)
    (hv : adminReq k s v) :
    adminCtx K ⊢ ∃ M : GoString, ⌜net.rpc.splitSM (adminMeths.getD k go!"") = some (go!"API", M)⌝ ∗
      apiSvcK K M (encAdminArgs v) adminAns := by
  iintro #Hc
  unfold adminCtx
  icases Hc with ⟨%Hss, -, %n, %hn, #Hch, #Hsv⟩
  obtain ⟨hs1, hs6, hv'⟩ := hv
  obtain ⟨hsr, -, -⟩ := Hss.2 n hn
  have hmem : sidOf (W64 (s : Int)) ∈ (K.γs n).srvs := by
    rw [hsr]; exact sidOf_mem_allSids s ⟨hs1, hs6⟩
  have hlen : (K.γs n).srvs.length < 2 ^ 32 := by rw [hsr]; simp [allSids, sidsUpTo]
  have hsl : (sidOf (W64 (s : Int))).length < 2 ^ 63 := by rw [sidOf_length s (by omega)]; omega
  have hne := sidOf_ne_nil (W64 (s : Int))
  have hsv : v = ⟨sidOf (W64 (s : Int)), sidOf (W64 (s : Int))⟩ → addReqW (K.γs n) v ∧ srvReqW (K.γs n) v := by
    rintro rfl; exact ⟨⟨hmem, rfl, hne, hsl, hlen⟩, ⟨hmem, hne, hsl, hlen⟩⟩
  ihave #Hisrv : isSrv (K.γs n) (sidOf (W64 (s : Int))) $$ []
  · unfold srvsOf
    iapply (BigSepL.bigSepL_lookup (Φ := fun _ (j : Nat) => isSrv (K.γs n) (sidOf (W64 ((j : Nat) : Int))))
      (range6_get s ⟨hs1, hs6⟩)) $$ Hsv
  have hargs : ∀ M : GoString, M ∈ [go!"AddNonvoter", go!"AddVoter", go!"DemoteVoter",
      go!"LeadershipTransfer", go!"RemoveServer", go!"Snapshot", go!"Status"] →
      apiArgsOk M (encAdminArgs v) := by
    intro M hM
    refine ⟨fun h => ?_, fun h => ?_, fun _ => ⟨v, rfl⟩⟩ <;> (subst h; simp at hM)
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl
  · have hv1 := hsv (by rcases hv' with h | ⟨h, _⟩; exact h; omega)
    iexists go!"AddVoter"
    isplitr; · ipureintro; decide
    unfold apiSvcK svcKE
    isplitr; · ipureintro; exact hargs _ (by simp)
    iintro %m #Hm
    ihave %He := chosen_agree K.γc n m $$ [Hch Hm]
    · iframe Hch Hm
    subst He
    imodintro
    unfold apiSvc
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    unfold adminDep
    iexists v
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact hv1.1
    iapply answers_admin
  · have hv1 := hsv (by rcases hv' with h | ⟨h, _⟩; exact h; omega)
    iexists go!"AddNonvoter"
    isplitr; · ipureintro; decide
    unfold apiSvcK svcKE
    isplitr; · ipureintro; exact hargs _ (by simp)
    iintro %m #Hm
    ihave %He := chosen_agree K.γc n m $$ [Hch Hm]
    · iframe Hch Hm
    subst He
    imodintro
    unfold apiSvc
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    unfold adminDep
    iexists v
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact hv1.1
    iapply answers_admin
  · have hv1 := hsv (by rcases hv' with h | ⟨h, _⟩; exact h; omega)
    iexists go!"DemoteVoter"
    isplitr; · ipureintro; decide
    unfold apiSvcK svcKE
    isplitr; · ipureintro; exact hargs _ (by simp)
    iintro %m #Hm
    ihave %He := chosen_agree K.γc n m $$ [Hch Hm]
    · iframe Hch Hm
    subst He
    imodintro
    unfold apiSvc
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    unfold adminDep
    iexists v
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact hv1.2
    iapply answers_admin
  · have hv1 := hsv (by rcases hv' with h | ⟨h, _⟩; exact h; omega)
    iexists go!"RemoveServer"
    isplitr; · ipureintro; decide
    unfold apiSvcK svcKE
    isplitr; · ipureintro; exact hargs _ (by simp)
    iintro %m #Hm
    ihave %He := chosen_agree K.γc n m $$ [Hch Hm]
    · iframe Hch Hm
    subst He
    imodintro
    unfold apiSvc
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
    unfold adminDep
    iexists v
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; exact hv1.2
    iapply answers_admin
  · iexists go!"LeadershipTransfer"
    isplitr; · ipureintro; decide
    unfold apiSvcK svcKE
    isplitr; · ipureintro; exact hargs _ (by simp)
    iintro %m #Hm
    ihave %He := chosen_agree K.γc n m $$ [Hch Hm]
    · iframe Hch Hm
    subst He
    imodintro
    unfold apiSvc
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_pos rfl]
    unfold adminDep
    iexists v
    isplitr; · ipureintro; rfl
    isplitr
    · unfold transferReqW
      rcases hv' with rfl | ⟨-, rfl⟩
      · iright; iframe Hisrv; ipureintro; rfl
      · ileft; ipureintro; rfl
    iapply answers_admin
  · iexists go!"Snapshot"
    isplitr; · ipureintro; decide
    unfold apiSvcK svcKE
    isplitr; · ipureintro; exact hargs _ (by simp)
    iintro %m #Hm
    ihave %He := chosen_agree K.γc n m $$ [Hch Hm]
    · iframe Hch Hm
    subst He
    imodintro
    unfold apiSvc
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
    unfold adminDep
    iexists v
    isplitr; · ipureintro; rfl
    isplitr; · itrivial
    iapply answers_admin

/-- **A `Status` request's deposit** at the servers' API. -/
theorem status_dep (K : HK GF) :
    adminCtx K ⊢ apiSvcK K go!"Status" (encAdminArgs ⟨[], []⟩) statusAns := by
  iintro #Hc
  unfold adminCtx
  icases Hc with ⟨-, -, %n, %hn, #Hch, -⟩
  unfold apiSvcK svcKE
  isplitr
  · ipureintro
    refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨_, rfl⟩⟩
  iintro %m #Hm
  imodintro
  unfold apiSvc
  dsimp only
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  iexists ⟨[], []⟩
  isplitr; · ipureintro; rfl
  unfold answers statusAns
  isplitl
  · iintro %rep ⟨%r, %h⟩; ipureintro; intro _; exact ⟨r, h⟩
  · iintro %msg %hmsg; ipureintro; intro h; exact absurd h hmsg

/-- The client addresses' call budgets (remote's `Check`: `MaxOps` operations, `readTries` calls
each). -/
def orchBud : Nat := 3 * 2 ^ 20

/-- **The orchestrator's share of the start**: the configuration addresses' protocols, the world's
services and server addresses, the draw's invariant, token and what it draws with, and remote's:
the client machines' addresses serving the far side's store `regR K.g.st`, the slot map, the
pending library's invariant and state, the client addresses' call units. -/
def orchShare [ρ : RemoteGS] (K : HK GF) (γp : PendNames) : IProp GF :=
  iprop(confProtos K.γc ∗ ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ∗
    ⌜kitSS K ∧ γsOk K⌝ ∗ drawInv K ∗ drawTok K ∗ drawPre K ∗
    ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (regR K.g.st) a) ∗
    mapCtx (Gg := hG.goose_globalGS) (I := HIn) ∗
    pendCtx (Gg := hG.goose_globalGS) (regR K.g.st) (regS (GF := GF)) γp ∗
    pendLib (Gg := hG.goose_globalGS) (regS (GF := GF)) γp (regS (GF := GF)).M.init ∗
    [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a orchBud)

end defs

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
