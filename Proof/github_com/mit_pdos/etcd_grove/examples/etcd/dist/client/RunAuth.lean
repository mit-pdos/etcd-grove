/-
Proof of `RunAuth.specWith PS` (the dist auth workload; authkv's `Run.wp_proof`,
`Proof/.../examples/etcd/auth/Run.lean`, at the cluster view), over the principals' service share `PS` and
`remotePrincipals.specWith PS` (a hypothesis: the principal service is the open contract, `notes/etcd-dist-f7.md`,
"Handoff RA-1"): the history invariant `akHistInv` allocated over the orchestrator's `etcdKV Γ.kv σ0` (the boot
state, no event); the set-up's puts under it (`akHist_writeAu`, `opHistOk_setupPut`); barrier 1's floors; root's
and u's clients; the principals at their machines, handed `akDistEnv`; root's Put of `z/end` (`opHistOk_endPut`);
root's watch of everything (`WatchOn_dist` with the history's read update, `akHist_readAu`; each event admitted,
`root_resp`), checked by `CheckHistory`; u's watch of `[a, b)` (`u_resp`: the range is u's). The watches' auth
rows are not used. Lean-first (no Rocq counterpart); F7 stage S6.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remotePrincipals
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.collectFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barriers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.SetUpDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.CheckHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.LastIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Permitted
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchOnDist
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Perennial.Spec.context.Background
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRunLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.RootWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkCalls
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.view etcd_dist.authd etcd_auth

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A write the history admits, under the history invariant, is an auth-on write update** (its grant
ignored: `akHist_writeAu` at `G := opGrantD …`). -/
theorem akHist_writeAuD (γk : KVNames) (P : Option GoString) (op : KVOp) (L₀ : List EntryModel)
    (hop : opHistOk op) :
    akHistInv (GF := GF) γk ⊢ writeAuD γk P op L₀ (fun _ => iprop(True)) := by
  iintro #Hinv
  ihave #Hau := akHist_writeAu γk op (opGrantD γk P op L₀) (fun _ => iprop(True)) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    · iintro !> %σ -
      imodintro
      isplitl []
      · ipureintro; exact hop
      · itrivial
  iunfold writeAuD
  imodintro
  iexact Hau

/-- A user client of one endpoint is a watch client of it. -/
theorem watchClient_of_userCli [π : NetProtoGS] (cl : Loc) (a : GoString) (V : WEnv GF)
    (cfg : go_etcd_io.etcd.client.v3.Config) (Γ : DistView) :
    userCli cl a V cfg ∗ membersAt (Gg := hG.goose_globalGS) [a] Γ ⊢
      ∃ w : Loc, watchClientAt cl w [a] V Γ := by
  iintro ⟨#Hu, #Hms⟩
  iunfold userCli at Hu
  icases Hu with ⟨#Hnc, #Hnp, -, -⟩
  iapply watchClient_of_new cl [a] V Γ
  iframe #

/-- Barrier 1's floor at one endpoint is `WatchOn_dist`'s floors there. -/
theorem watchFloorsD_one [π : NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (L₀ : List EntryModel)
    (a : GoString) :
    barrierFloor (GF := GF) Γ γR L₀ a ⊢ watchFloorsD [a] Γ γR L₀ := by
  unfold watchFloorsD barrierFloor
  exact (BigSepL.bigSepL_singleton (PROP := IProp GF)
    (Φ := fun _ a => iprop(∃ (mid : w64) (m : Nat),
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid ∗ authFloorD Γ γR mid L₀ m))).2

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 10000 in
/-- See the file header. -/
theorem RunAuth.wp_proof
    (PS : ∀ [NetProtoGS] [github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS],
      DistView → ServerRaftNames → List GoString → List GoString → IProp GF)
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_SetUp : etcd_auth.SetUp.spec_dist (GF := GF) (hG := hG))
    (wp_barriers : barriers.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_rp : remotePrincipals.specWith (GF := GF) (hG := hG) PS)
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Put : KV_PutOn_dist.spec (GF := GF) (hG := hG))
    (wp_Watch : WatchOn_dist.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_collectFor : collectFor.spec (GF := GF) (hG := hG))
    (wp_CheckHistory : etcd_auth.CheckHistory.spec (GF := GF) (hG := hG))
    (wp_LastIn : etcd_auth.LastIn.spec (GF := GF) (hG := hG))
    (wp_Permitted : etcd_auth.Permitted.spec (GF := GF) (hG := hG)) :
    RunAuth.specWith (GF := GF) (hG := hG) PS := by
  intro π ρ _ _ _ Γ eps nodes addrs ns ready γR σ0 hV Htb hAs hne hauth hγR hau hσ0
  wp_start as ⟨Hlt, #Heps, #Hnodes, #Hms, #Hready, #HkvI, #HL0, HkV, Hview, HPS⟩
  ihave %Hlen := ownSlice_len $$ Heps
  have hpos : 0 < addrs.length := List.length_pos_iff.2 hne
  ihave %Hok := addrOk_of_leaseMembers Γ addrs $$ Hms
  ihave #Hmem := membersAt_of_leaseMembers Γ addrs $$ Hms
  -- the history invariant, over the boot state (no event)
  imod (akHist_alloc Γ.kv σ0 (stateHistOk_of_changes_nil σ0 hσ0)) $$ HkV with #Hhist
  -- `a0, au := eps[0], eps[1%k]`
  have hkl : uint.nat eps.len = addrs.length := by word
  have hk63 : addrs.length < 2 ^ 63 := by word
  have hmodZ := fun c hc => mod_len_sintD eps.len addrs.length c hkl hpos hk63 hc
  obtain ⟨a0, hx0⟩ : ∃ x, addrs[0]? = some x := ⟨_, List.getElem?_eq_getElem hpos⟩
  obtain ⟨au, hxu⟩ : ∃ x, addrs[1 % addrs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩
  have hepsZ : sint.Z eps.len = (addrs.length : Int) := by word
  have hu : sint.Z (W64 1 % eps.len) = ((1 % addrs.length : Nat) : Int) := hmodZ 1 (by omega)
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z eps.len := by constructor <;> word
  have Hbu : 0 ≤ sint.Z (W64 1 % eps.len) ∧ sint.Z (W64 1 % eps.len) < sint.Z eps.len := by
    rw [hu, hepsZ]; have := Nat.mod_lt 1 hpos; omega
  have hpe : ∀ a ∈ addrs, plainEndpoint a := fun a ha => etcd_dist.addrOk_plainEndpoint (Hok a ha)
  (try wp_auto)
  (try simp only [Hb0, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index eps (sint.Z (W64 0)) _ _ a0 Hb0.1 $$ [Heps] as -
  · iframe #; ipureintro; exact hx0
  (try wp_auto)
  have hk0' : ¬ (sint.Z eps.len = 0) := by word
  have hsr1 : BitVec.srem (W64 1) eps.len = W64 1 % eps.len := srem_eq_umodD _ _ (by decide) (by word)
  simp only [hk0', ↓reduceIte]
  rw [hsr1]
  (try wp_auto)
  simp only [Hbu, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index eps (sint.Z (W64 1 % eps.len)) _ _ au Hbu.1 $$ [Heps] as -
  · iframe #; ipureintro; rw [hu, Int.toNat_natCast]; exact hxu
  (try wp_auto)
  have hx0m : a0 ∈ addrs := List.mem_of_getElem? hx0
  have hxum : au ∈ addrs := List.mem_of_getElem? hxu
  ihave #Hlm0 := BigSepL.bigSepL_lookup hx0 $$ Hms
  ihave ⟨%mid0', #Hat0'⟩ := leaseMember_member Γ a0 $$ Hlm0
  ihave #Hm0' := membersAt_one (Gg := hG.goose_globalGS) a0 Γ mid0' $$ Hat0'
  let V : WEnv GF := Classical.choice hV
  -- `cli, err := newClient([]string{a0})`: the anonymous client, at `a0`
  wp_apply wp_slice_literal (V := GoString) (l := [a0])
  isplitr
  · ipureintro; rfl
  iintro %lit0 ⟨Hlit0, -⟩
  imod ownSlice_persist _ _ _ $$ Hlit0 with #Hlit0
  (try wp_auto)
  wp_apply (wp_newClient _ [a0] V Htb (plainEndpoints_singleton _ (hpe a0 hx0m))) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp, #Hcfg⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hcerr
  ihave ⟨%cfg0, #Hu0, %hP0⟩ := anonCli_of_new cl a0 V $$ [Hnc Hnp Hcfg]
  · iframe #
  (try wp_auto)
  -- `auth.SetUp(cli)` through `a0`, the set-up puts under the history invariant
  ihave #Pauth : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth $$ []
  · iPkgInit
  ihave ⟨%api0, #Huc0⟩ := userClientAt_of_userCli cl a0 V cfg0 Γ $$ [Hu0 Hm0']
  · iframe #
  ihave ⟨%ap0, #Hac0⟩ := authClientAt_of_userCli cl a0 V cfg0 Γ $$ [Hu0 Hm0']
  · iframe #
  ihave #Hsau : iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      writeAuD Γ.kv none (.put (putWireOf (opPutModel k go!"setup" []))) ([] : List EntryModel)
        (fun _ => iprop(True))) $$ []
  · iintro !> %k %hk
    rw [show putWireOf (opPutModel k go!"setup" []) = client.putKeyOp k go!"setup" from rfl]
    iapply akHist_writeAuD Γ.kv none _ [] (opHistOk_setupPut k hk)
    iexact Hhist
  wp_apply (wp_SetUp cl api0 ap0 [a0] V Γ cfg0 γR [] hauth hγR hP0 hAs) $$ [$Hlt Hview] as %ok ⟨Hlt, Hok⟩
  · iframe Hview; iframe #
  cases ok
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %rr, #Hfz, #HLset, %Hset⟩
  (try wp_auto)
  -- `barriers(eps)`: each member's floor after the set-up
  wp_apply (wp_barriers eps addrs V Γ γR Lset Htb hpe hAs hau hauth hγR) $$ [$Hlt] as %ok1 ⟨Hlt, Hb1⟩
  · iframe #
  icases Hb1 with (%Hb1 | ⟨%Hb1, #Hfl⟩) <;> subst Hb1
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  ihave #Hf0 := BigSepL.bigSepL_lookup hx0 $$ Hfl
  ihave #Hfu := BigSepL.bigSepL_lookup hxu $$ Hfl
  ihave #Hwf0 := watchFloorsD_one Γ γR Lset a0 $$ Hf0
  ihave #Hwfu := watchFloorsD_one Γ γR Lset au $$ Hfu
  iunfold barrierFloor at Hf0 Hfu
  icases Hf0 with ⟨%mid0, %m0, #Hat0, -⟩
  icases Hfu with ⟨%midu, %mu, #Hatu, -⟩
  ihave #Hm0 := membersAt_one (Gg := hG.goose_globalGS) a0 Γ mid0 $$ Hat0
  ihave #Hmu := membersAt_one (Gg := hG.goose_globalGS) au Γ midu $$ Hatu
  -- the clients: root at `a0`, u at `au`
  wp_apply (wp_newUserClient a0 go!"root" go!"root-pw" V Γ Htb (hpe a0 hx0m) (by decide) (by decide)
      (by decide) hau hauth) $$ [$Hlt] as %rcl %rerr ⟨Hlt, Hr⟩
  · iframe #
  icases Hr with (⟨%Hrerr, %rcfg, #Hru, %hPr⟩ | %Hrfail)
  rotate_left
  · obtain ⟨Hrerr, -⟩ := Hrfail
    cases rerr with
    | nil => exact absurd rfl Hrerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hrerr
  (try wp_auto)
  wp_apply (wp_newUserClient au go!"u" go!"u-pw" V Γ Htb (hpe au hxum) (by decide) (by decide)
      (by decide) hau hauth) $$ [$Hlt] as %ucl %uerr ⟨Hlt, Hu⟩
  · iframe #
  icases Hu with (⟨%Huerr, %ucfg, #Huu, %hPu⟩ | %Hufail)
  rotate_left
  · obtain ⟨Huerr, -⟩ := Hufail
    cases uerr with
    | nil => exact absurd rfl Huerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Huerr
  (try wp_auto)
  -- `ready()`
  ihave #Hready' := Hready
  iunfold readySpec at Hready'
  wp_apply Hready'
  (try wp_auto)
  -- `remotePrincipals(nodes)`: the principals at their machines, each handed `akDistEnv`
  ihave #Henv : akDistEnv (GF := GF) addrs Γ γR $$ []
  · iunfold akDistEnv
    iexists γz, hs, Lset, rr
    iframe #
    isplitl []
    · iunfold watchFloorsD
      iapply BigSepL.bigSepL_mono _ $$ Hfl
      intro i a _
      iintro #H
      iunfold barrierFloor at H
      iexact H
    ipureintro; exact Hset
  wp_apply (wp_rp nodes ns addrs Γ γR Htb) $$ [$Hlt HPS] as %np Hlt
  · iframe HPS; iframe #
  (try wp_auto)
  -- `end, err := root.Put(ctx, "z/end", "end")` at `a0`: the history admits it (`opHistOk_endPut`)
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hcci : _root_.Perennial.context.isClosedchanInit (GF := GF) $$ []
  · iapply _root_.Perennial.context.isClosedchanInit_of_init
    iPkgInit
  ihave ⟨%rapi, #Hrcu⟩ := userClientAt_of_userCli rcl a0 V rcfg Γ $$ [Hru Hm0]
  · iframe #
  ihave #Hrcu' := Hrcu
  iunfold etcd_dist.authd.userClientAt at Hrcu'
  icases Hrcu' with ⟨#Hrkc, -⟩
  iunfold kvClientAt at Hrkc
  icases Hrkc with ⟨-, -, #Hrkvf, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -, #Heout, -⟩
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  ihave #Hopts0 := optsAt_nil (GF := GF)
  ihave #Hwend := akHist_writeAuD Γ.kv (principalOf rcfg) (.put (client.putKeyOp endKey go!"end")) Lset
    (opHistOk_endPut _) $$ Hhist
  wp_apply (wp_Put rcl rapi [a0] V Γ rcfg γR Lset ectx ecd none endKey go!"end" slice.nil []
      (fun _ => iprop(True)) hauth hγR (outTokOk_none _)) $$ [$Hlt] as %eresp %eerr ⟨Hlt, Hend'⟩
  · iframe #
    isplitl []
    · ipureintro
      refine ⟨?_, rfl, Or.inl ?_⟩
      · simp [opPutModel, OpFull.putPanics, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]
      · simp [opPutModel, putWireOf, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]
    isplitl []
    · rw [show putWireOf (opPutModel endKey go!"end" []) = client.putKeyOp endKey go!"end" from rfl]
      iexact Hwend
    ipureintro
    exact opSizeOk_opPutModel (K := 2 ^ 28) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _) (by decide)
      (by decide) (by decide)
  (try wp_auto)
  wp_apply Hecancel
  (try wp_auto)
  icases Hend' with (⟨%Heerr, %em, %σe, Hemsg, -, -, -, -⟩ | %Heerr)
  rotate_left
  · cases eerr with
    | nil => exact absurd rfl Heerr.1
    | ok ei =>
      (try wp_auto)
      wp_apply wp_ended as %r -
      (try wp_auto)
      iapply HΦ; iframe Hlt
  subst Heerr
  (try wp_auto)
  -- root's watch of every key from revision 1 (`hctx, hcancel := context.WithCancel(...)`;
  -- `root.Watcher.Watch(hctx, "", WithPrefix(), WithRev(1))`) at `a0`, with the history's read update
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %hctx %γhctx %hcancel ⟨#Hhcancel, #Hhctx, -, #hctxFrom⟩
  ihave #hctxO := metadata.outgoingCtxOkC_bgFrom hctx $$ hctxFrom
  ihave #hctxM := metadata.outMD_bgFrom hctx $$ hctxFrom
  ihave #Hhc : iprop(□ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #hcancel) (Val #())) {{ Ψ }})) $$ []
  · iintro !> %Ψ HΨ
    iapply Hhcancel
    · itrivial
    inext; iintro -; iexact HΨ
  (try wp_auto)
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 1) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %hosl ⟨Hhosl, -⟩
  ipersist Hhosl
  ihave #Hhopts := etcd_auth.optsAt_two (GF := GF) _
      ([f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2) f1 f2 withPrefixM (withRevM (W64 1))
      rfl $$ [Hhosl Hf1 Hf2]
  · iframe #
  ihave #Hru' := Hru
  iunfold userCli at Hru'
  icases Hru' with ⟨-, -, #Hrcfg, %Hrtok⟩
  ihave ⟨%rw, #Hrwc⟩ := watchClient_of_userCli rcl a0 V rcfg Γ $$ [Hru Hm0]
  · iframe #
  ihave #Hrwc' := Hrwc
  iunfold watchClientAt at Hrwc'
  icases Hrwc' with ⟨-, -, #Hrwf, -⟩
  ihave #Hrau := akHist_readAu Γ.kv $$ Hhist
  iunfold kvReadAu at Hrau
  iunfold kvAu at Hrau
  (try wp_auto)
  wp_apply (wp_Watch rcl rw [a0] V Γ rcfg γR Lset hctx
      ({ Values := ∅, Deadline := none, Done_gn := γhctx, PDone := iprop(True) } :
        _root_.Perennial.context.ContextDesc (IProp GF)) none
      _ _ [withPrefixM, withRevM (W64 1)] (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) hau hauth hγR
      (outTokOkS_none _)) $$ []
    as %hch %γh ⟨#Hhsp, Hhcons, Hhcur⟩
  · iframe #
    isplitr
    · ipureintro; exact Hrtok
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    ipureintro; exact watch_all_okD
  ihave #Hhch := etcdstart.isRespChan_of_state hch _ γh _ (fun σ => iprop(⌜stateHistOk σ⌝)) _ $$ Hhsp
  (try wp_auto)
  -- `evs, ok := collectFor(hch, hcancel, end.Header.Revision)`: every event admitted (`root_resp`)
  iunfold putRespMsg at Hemsg
  icases Hemsg with ⟨%Hnn, %eh, %epk, #Hehd, #Hehf, -⟩
  iunfold hdrFull at Hehf
  icases Hehf with ⟨%Hhn, -, -, #Herevf, -, -⟩
  (try wp_auto)
  have h10 : (W64 1 - W64 1 : w64) = W64 0 := by decide
  ihave Hhcons : etcdWatchConsumer γh 0 (W64 0) $$ [Hhcons Hhcur]
  · unfold etcdWatchConsumer
    iexists []
    rw [← h10]
    iframe Hhcons Hhcur
    ipureintro; rfl
  wp_apply (wp_collectFor (etcdstart.stateOk _ (fun σ => iprop(⌜stateHistOk σ⌝))) (fun _ _ => True)
      (fun _ e => iprop(⌜rootEvOk e⌝)) iprop(True) hch γh hcancel _ (W64 0) trivial
      (fun _ _ _ _ => inferInstance)
      (fun c c' v r => etcdstart.stateOk_closeErr _ _ c c' v r)
      (fun n c c' v r hne hI => root_resp _ n c c' v r hne hI))
    $$ [Hhcons] as %esl %eok Hcol
  · iframe; iframe #
    iintro !>; itrivial
  (try wp_auto)
  cases eok
  · -- the watch ended before root's last write
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  ihave ⟨%evs, Hes, -, #Hevs⟩ := Hcol $$ %rfl
  ihave %Hhist' := histOk_of_collected evs $$ Hevs
  (try wp_auto)
  -- `auth.CheckHistory(evs, "z/end")`
  wp_apply (wp_CheckHistory esl evs (DFrac.own 1) endKey Hhist') $$ [Hes] as Hes
  · iframe; try iframe #
  (try wp_auto)
  -- u's watch of `[a, b)` from revision 1 at `au` (`uctx, ucancel := context.WithCancel(...)`;
  -- `ucli.Watcher.Watch(uctx, "a", WithRange("b"), WithRev(1))`): its events are of `[a, b)` (`u_resp`)
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %uctx %γuctx %ucancel ⟨#Hucancel, #Huctx, -, #uctxFrom⟩
  ihave #uctxO := metadata.outgoingCtxOkC_bgFrom uctx $$ uctxFrom
  ihave #uctxM := metadata.outMD_bgFrom uctx $$ uctxFrom
  ihave #Huc : iprop(□ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #ucancel) (Val #())) {{ Ψ }})) $$ []
  · iintro !> %Ψ HΨ
    iapply Hucancel
    · itrivial
    inext; iintro -; iexact HΨ
  (try wp_auto)
  wp_apply wp_WithRange hi as %g1 #Hg1
  wp_apply wp_WithRev (W64 1) as %g2 #Hg2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %uosl ⟨Huosl, -⟩
  ipersist Huosl
  ihave #Huopts := etcd_auth.optsAt_two (GF := GF) _
      ([g1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) g2) g1 g2 (withRangeM hi) (withRevM (W64 1))
      rfl $$ [Huosl Hg1 Hg2]
  · iframe #
  ihave #Huu' := Huu
  iunfold userCli at Huu'
  icases Huu' with ⟨-, -, #Hucfg, %Hutok⟩
  ihave ⟨%uw, #Huwc⟩ := watchClient_of_userCli ucl au V ucfg Γ $$ [Huu Hmu]
  · iframe #
  ihave #Huwc' := Huwc
  iunfold watchClientAt at Huwc'
  icases Huwc' with ⟨-, -, #Huwf, -⟩
  (try wp_auto)
  wp_apply (wp_Watch ucl uw [au] V Γ ucfg γR Lset uctx
      ({ Values := ∅, Deadline := none, Done_gn := γuctx, PDone := iprop(True) } :
        _root_.Perennial.context.ContextDesc (IProp GF)) none
      _ _ [withRangeM hi, withRevM (W64 1)] (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) hau hauth hγR
      (outTokOkS_none _)) $$ []
    as %uch %γu ⟨#Husp, Hucons, Hucur⟩
  · iframe #
    isplitr
    · ipureintro; exact Hutok
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    ipureintro; exact watch_ab_okD
  rw [OpFull.watchNorm_of_ne (opWatchModel lo [withRangeM hi, withRevM (W64 1)])
    (by rw [watch_ab_ok.2.1]; decide)]
  ihave #Huch := etcdstart.isRespChan_of_state uch _ γu _ (fun σ => iprop(⌜stateHistOk σ⌝)) _ $$ Husp
  (try wp_auto)
  -- `uevs, ok := collectFor(uch, ucancel, auth.LastIn(evs))`
  wp_apply (wp_LastIn esl evs (DFrac.own 1)) $$ [Hes] as Hes
  · iframe; try iframe #
  ihave Hucons : etcdWatchConsumer γu 0 (W64 0) $$ [Hucons Hucur]
  · unfold etcdWatchConsumer
    iexists []
    rw [← h10]
    iframe Hucons Hucur
    ipureintro; rfl
  wp_apply (wp_collectFor (etcdstart.stateOk _ (fun σ => iprop(⌜stateHistOk σ⌝))) (fun _ _ => True)
      (fun _ e => iprop(⌜permittedK go!"u" e.Key'⌝)) iprop(True) uch γu ucancel _ (W64 0) trivial
      (fun _ _ _ _ => inferInstance)
      (fun c c' v r => etcdstart.stateOk_closeErr _ _ c c' v r)
      (fun n c c' v r hne hI => u_resp _ ⟨watch_ab_ok.2.1, watch_ab_ok.2.2⟩ _ n c c' v r hne hI))
    $$ [Hucons] as %usl %uok Hucol
  · iframe; iframe #
    iintro !>; itrivial
  (try wp_auto)
  cases uok
  · -- the watch ended before the history's last event in `[a, b)`
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  ihave ⟨%uevs, Hues, -, #Huevs⟩ := Hucol $$ %rfl
  (try wp_auto)
  -- `for _, e := range uevs { if !auth.Permitted("u", e.Key) { panic(...) } }`: every event's key is
  -- u's (`Huevs`)
  ihave %Huel := ownSlice_len $$ Hues
  ihave HU : (∃ (j : w64) (e0 : etcdstart.wev),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "Hues" ∷ usl ↦* uevs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z usl.len⌝ : IProp GF) $$ [i e Hues]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HU
  wp_if_destruct
  · have Hlt' : sint.Z j < sint.Z usl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z usl.len := ⟨Hj.1, Hlt'⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem uevs (sint.nat j) as x
    wp_apply wp_load_slice_index usl (sint.Z j) uevs (DFrac.own 1) x Hj.1 $$ [Hues] as Hues
    · iframe; ipureintro; exact Hx_lookup
    ihave %Hux := Huevs $$ %(sint.nat j) %x %Hx_lookup
    (try wp_auto)
    wp_apply wp_Permitted
    rw [decide_eq_true Hux]
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, x
    iframe
    ipureintro; constructor <;> word
  · (try wp_auto)
    wp_apply wp_checked as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
