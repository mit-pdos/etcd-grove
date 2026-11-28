/-
Proof of `RunAuthLease.spec` (the dist authLease workload; authlease's `run.wp_proof`,
`Proof/.../examples/etcd/authlease/run.lean`, at the cluster view): the driver's cell allocated over the
orchestrator's `etcdKV Γ.kv σ0`, the set-up's puts offered from it (`cell_setupAuD`); barrier 1's floors name
the member of each address used, root's and u's grants recorded in the cell (`fixZD`, `fixAD`), u's leased
transaction (`cell_txnTAu`); then the checks: `noAuth`'s refutations from the frozen floor
(`noAuth_refutesD`), u's refused put/txn (`refused_updateD`), `foreign`'s revocations (`refused_updateD`,
`revokeLu_updateD`) and its TimeToLive checks (`foreign_refutesD`, from the frozen floor; the lessor lower bound
its calls take at u's member from u's grant, at v's from v's own lease, `ownLease`, recorded in the cell's grant
ids only), root's reads from the cell (`seenD_z`, `seenD_gone`).
Lean-first (no Rocq counterpart); F7 stage S5.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuthLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barriers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.grantPut
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.noAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.foreign
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ownLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.absent
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.authwork.SetUpDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseRevokeOnDist
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.TxnPlainSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.ClientCallDistLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRunLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRefusals
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ForeignRefutes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.WorkCalls
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.KeyOps
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
open etcd_dist etcd_dist.view etcd_dist.authd etcd_authlease

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
theorem RunAuthLease.wp_proof
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_SetUp : etcd_auth.SetUp.spec_dist (GF := GF) (hG := hG))
    (wp_barriers : barriers.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_grantPut : grantPut.spec (GF := GF) (hG := hG))
    (wp_noAuth : noAuth.spec (GF := GF) (hG := hG))
    (wp_foreign : foreign.spec (GF := GF) (hG := hG))
    (wp_ownLease : ownLease.spec (GF := GF) (hG := hG))
    (wp_absent : absent.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithLease : WithLease.spec (GF := GF) (hG := hG))
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG))
    (wp_Txn : etcd_txnlin.client_Txn_dist.law (GF := GF) (hG := hG))
    (wp_Then : txn.Then.specPlain (GF := GF) (hG := hG))
    (wp_Commit : Txn_CommitOn_dist.spec (GF := GF) (hG := hG))
    (wp_Put : KV_PutOn_dist.spec (GF := GF) (hG := hG))
    (wp_Get : KV_GetOn_dist.spec (GF := GF) (hG := hG))
    (wp_Revoke : Lease_RevokeOn_dist.spec (GF := GF) (hG := hG)) :
    RunAuthLease.spec (GF := GF) (hG := hG) := by
  intro π _ _ _ Γ eps addrs ready γR σ0 hV Htb hAs hne hauth hlm hγR hau hls hx
  wp_start as ⟨Hlt, #Heps, #Hms, #Hready, #HkvI, #HL0, HkV, Hview⟩
  ihave %Hlen := ownSlice_len $$ Heps
  have hpos : 0 < addrs.length := List.length_pos_iff.2 hne
  ihave %Hok := addrOk_of_leaseMembers Γ addrs $$ Hms
  ihave #Hmem := membersAt_of_leaseMembers Γ addrs $$ Hms
  imod (cell_alloc Γ.kv σ0 hx) $$ HkV with ⟨%γc, #Hinv, #Hi0, #Hp0, #Hg0, #Hd0, Ha, Hids⟩
  -- `a0, au, av := eps[0], eps[1%k], eps[2%k]`
  have hkl : uint.nat eps.len = addrs.length := by word
  have hk63 : addrs.length < 2 ^ 63 := by word
  have hmodZ := fun c hc => mod_len_sintD eps.len addrs.length c hkl hpos hk63 hc
  obtain ⟨a0, hx0⟩ : ∃ x, addrs[0]? = some x := ⟨_, List.getElem?_eq_getElem hpos⟩
  obtain ⟨au, hxu⟩ : ∃ x, addrs[1 % addrs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩
  obtain ⟨av, hxv⟩ : ∃ x, addrs[2 % addrs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hpos)⟩
  have hepsZ : sint.Z eps.len = (addrs.length : Int) := by word
  have hu : sint.Z (W64 1 % eps.len) = ((1 % addrs.length : Nat) : Int) := hmodZ 1 (by omega)
  have hv : sint.Z (W64 2 % eps.len) = ((2 % addrs.length : Nat) : Int) := hmodZ 2 (by omega)
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z eps.len := by constructor <;> word
  have Hbu : 0 ≤ sint.Z (W64 1 % eps.len) ∧ sint.Z (W64 1 % eps.len) < sint.Z eps.len := by
    rw [hu, hepsZ]; have := Nat.mod_lt 1 hpos; omega
  have Hbv : 0 ≤ sint.Z (W64 2 % eps.len) ∧ sint.Z (W64 2 % eps.len) < sint.Z eps.len := by
    rw [hv, hepsZ]; have := Nat.mod_lt 2 hpos; omega
  have hk0 : ¬ (uint.Z eps.len = 0) := by word
  have hpe : ∀ a ∈ addrs, plainEndpoint a := fun a ha => etcd_dist.addrOk_plainEndpoint (Hok a ha)
  (try wp_auto)
  (try simp only [Hb0, _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index eps (sint.Z (W64 0)) _ _ a0 Hb0.1 $$ [Heps] as -
  · iframe #; ipureintro; exact hx0
  (try wp_auto)
  have hk0' : ¬ (sint.Z eps.len = 0) := by word
  have hsr1 : BitVec.srem (W64 1) eps.len = W64 1 % eps.len := srem_eq_umodD _ _ (by decide) (by word)
  have hsr2 : BitVec.srem (W64 2) eps.len = W64 2 % eps.len := srem_eq_umodD _ _ (by decide) (by word)
  simp only [hk0', ↓reduceIte]
  rw [hsr1]
  (try wp_auto)
  simp only [Hbu, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index eps (sint.Z (W64 1 % eps.len)) _ _ au Hbu.1 $$ [Heps] as -
  · iframe #; ipureintro; rw [hu, Int.toNat_natCast]; exact hxu
  (try wp_auto)
  simp only [hk0', ↓reduceIte]
  rw [hsr2]
  (try wp_auto)
  simp only [Hbv, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index eps (sint.Z (W64 2 % eps.len)) _ _ av Hbv.1 $$ [Heps] as -
  · iframe #; ipureintro; rw [hv, Int.toNat_natCast]; exact hxv
  (try wp_auto)
  have hx0m : a0 ∈ addrs := List.mem_of_getElem? hx0
  have hxum : au ∈ addrs := List.mem_of_getElem? hxu
  have hxvm : av ∈ addrs := List.mem_of_getElem? hxv
  ihave #Hlm0 := BigSepL.bigSepL_lookup hx0 $$ Hms
  ihave #Hlmu := BigSepL.bigSepL_lookup hxu $$ Hms
  ihave ⟨%mid0', #Hat0'⟩ := leaseMember_member Γ a0 $$ Hlm0
  ihave ⟨%midu', #Hatu'⟩ := leaseMember_member Γ au $$ Hlmu
  ihave #Hm0' := membersAt_one (Gg := hG.goose_globalGS) a0 Γ mid0' $$ Hat0'
  ihave #Hmu' := membersAt_one (Gg := hG.goose_globalGS) au Γ midu' $$ Hatu'
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
  -- `auth.SetUp(cli)` through `a0`, the set-up puts offered from the cell
  ihave #Pauth : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.authwork $$ []
  · iPkgInit
  ihave ⟨%api0, #Huc0⟩ := userClientAt_of_userCli cl a0 V cfg0 Γ $$ [Hu0 Hm0']
  · iframe #
  ihave ⟨%ap0, #Hac0⟩ := authClientAt_of_userCli cl a0 V cfg0 Γ $$ [Hu0 Hm0']
  · iframe #
  ihave #Hsau := cell_setupAuD Γ.kv γc ([] : List EntryModel) $$ Hinv
  wp_apply (wp_SetUp cl api0 ap0 [a0] V Γ cfg0 γR [] hauth hγR hP0 hAs) $$ [$Hlt Hview] as %ok ⟨Hlt, Hok⟩
  · iframe Hview; iframe #
  cases ok
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %rr, #Hfz, #HLset, %Hset⟩
  obtain ⟨hadm, hst⟩ := Hset
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
  ihave #Hfv := BigSepL.bigSepL_lookup hxv $$ Hfl
  iunfold barrierFloor at Hf0 Hfu Hfv
  icases Hf0 with ⟨%mid0, %m0, #Hat0, #Hfd0⟩
  icases Hfu with ⟨%midu, %mu, #Hatu, #Hfdu⟩
  icases Hfv with ⟨%midv, %mv, #Hatv, #Hfdv⟩
  ihave #Hm0 := membersAt_one (Gg := hG.goose_globalGS) a0 Γ mid0 $$ Hat0
  ihave #Hmu := membersAt_one (Gg := hG.goose_globalGS) au Γ midu $$ Hatu
  ihave #Hmv := membersAt_one (Gg := hG.goose_globalGS) av Γ midv $$ Hatv
  -- the clients: root at `a0`, u at `au`, v at `av`
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
  wp_apply (wp_newUserClient av go!"v" go!"v-pw" V Γ Htb (hpe av hxvm) (by decide) (by decide)
      (by decide) hau hauth) $$ [$Hlt] as %vcl %verr ⟨Hlt, Hv⟩
  · iframe #
  icases Hv with (⟨%Hverr, %vcfg, #Hvu, %hPv⟩ | %Hvfail)
  rotate_left
  · obtain ⟨Hverr, -⟩ := Hvfail
    cases verr with
    | nil => exact absurd rfl Hverr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hverr
  (try wp_auto)
  -- `bcli, err := newClient([]string{au})`: bad's client (no token of its own), at `au`
  wp_apply wp_slice_literal (V := GoString) (l := [au])
  isplitr
  · ipureintro; rfl
  iintro %litu ⟨Hlitu, -⟩
  imod ownSlice_persist _ _ _ $$ Hlitu with #Hlitu
  (try wp_auto)
  wp_apply (wp_newClient _ [au] V Htb (plainEndpoints_singleton _ (hpe au hxum))) $$ [$Hlt] as %bcl %berr ⟨Hlt, Hbc⟩
  · iframe #
  icases Hbc with (⟨%Hberr, #Hbnc, #Hbnp, #Hbcfg⟩ | %Hbfail)
  rotate_left
  · obtain ⟨Hberr, -⟩ := Hbfail
    cases berr with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hberr
  ihave ⟨%bcfg, #Hbu, %hPb⟩ := anonCli_of_new bcl au V $$ [Hbnc Hbnp Hbcfg]
  · iframe #
  (try wp_auto)
  -- `lz, ok := grantPut(root, zKey)`: root's lease `Lz` on `z/lease` at `a0` (`fixZD`)
  have hszL : ∀ (k : GoString) (id : w64), k.length ≤ 2 ^ 20 →
      opSizeOk (opPutModel k go!"v" [withLeaseM id]) := by
    intro k id hk
    simp [opSizeOk, opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]
    omega
  ihave #Hpub0 : auth.authPubLbM (.on (Γ.au mid0)) m0 $$ []
  · iunfold authFloorD at Hfd0; icases Hfd0 with ⟨#H, -⟩; iexact H
  ihave #Hpubu : auth.authPubLbM (.on (Γ.au midu)) mu $$ []
  · iunfold authFloorD at Hfdu; icases Hfdu with ⟨#H, -⟩; iexact H
  ihave #Hpubv : auth.authPubLbM (.on (Γ.au midv)) mv $$ []
  · iunfold authFloorD at Hfdv; icases Hfdv with ⟨#H, -⟩; iexact H
  ihave #Hgor := cell_grantWriteAuD Γ.kv γc (principalOf rcfg) (W64 9000000000) Lset (by decide) hlm $$ Hinv
  ihave HFz := fixZD Γ.kv γc (principalOf rcfg) Lset $$ [Hinv Hp0]
  · iframe #
  wp_apply (wp_grantPut rcl a0 zK V Γ mid0 rcfg γR Lset m0 (gsHas γc) (fun _ => psAtLeast γc 1)
      (monoListAuthOwn γc.ids (1 : Qp).half ([] : List w64))
      (fun id => iprop(monoListAuthOwn γc.ids (1 : Qp).half [id] ∗ monoListLbOwn γc.ids [id] ∗
        ⌜id ≠ W64 0⌝))
      hau hls hauth hlm hγR (fun id => hszL zK id (by decide)) hAs) $$ [$Hlt Hids HFz] as %lz %okz ⟨Hlt, Hz⟩
  · iframe Hids HFz; iframe #
  icases Hz with (%Hz | ⟨%Hz, ⟨HidsZ, #HlbZ, %hlz0⟩, ⟨%σz, #HpsZ⟩, ⟨%iz, %lzl, #Hlvz⟩, #Hckz⟩)
  · subst Hz
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  obtain ⟨Hz, -⟩ := Hz
  subst Hz
  (try wp_auto)
  -- `lu, ok := grantPut(ucli, aKey)`: u's lease `Lu` on `a/lease` at `au` (`fixAD`)
  iunfold psAtLeast at HpsZ
  icases HpsZ with ⟨%ps1, #Hps1, %hps1⟩
  ihave #Hgou := cell_grantWriteAuD Γ.kv γc (principalOf ucfg) (W64 9000000000) Lset (by decide) hlm $$ Hinv
  ihave HFa := fixAD Γ.kv γc γz hs Lset rr hadm hst lz hlz0 ps1 hps1 $$ [Hinv Hps1 Hfz]
  · iframe #
  wp_apply (wp_grantPut ucl au aK V Γ midu ucfg γR Lset mu (gsHas γc) (fun _ => psAtLeast γc 2)
      (monoListAuthOwn γc.ids (1 : Qp).half [lz])
      (fun id => iprop(monoListAuthOwn γc.ids (1 : Qp).half [lz, id] ∗ monoListLbOwn γc.ids [lz, id] ∗
        ⌜id ≠ W64 0⌝))
      hau hls hauth hlm hγR (fun id => hszL aK id (by decide)) hAs) $$ [$Hlt HidsZ HFa] as %lu %oku ⟨Hlt, Hu⟩
  · iframe HidsZ; iframe #
    rw [hPu]
    iexact HFa
  icases Hu with (%Hu | ⟨%Hu, ⟨HidsU, #HlbU, %hlu0⟩, ⟨%σu, #HpsU⟩, ⟨%iu, %lul, #Hlvu⟩, #Hcku⟩)
  · subst Hu
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  obtain ⟨Hu, -⟩ := Hu
  subst Hu
  (try wp_auto)
  -- u's transaction `Txn().Then(OpPut(txnKey, "v", WithLease(lu))).Commit()` at `au` (`cell_txnTAu`)
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave ⟨%uapi, #Hucu⟩ := userClientAt_of_userCli ucl au V ucfg Γ $$ [Huu Hmu]
  · iframe #
  ihave #Hucu' := Hucu
  iunfold etcd_dist.authd.userClientAt at Hucu'
  icases Hucu' with ⟨#Hukc, -⟩
  ihave #Hukc' := Hukc
  iunfold kvClientAt at Hukc'
  icases Hukc' with ⟨-, -, #Hukvf, -⟩
  iunfold psAtLeast at HpsU
  icases HpsU with ⟨%ps2, #Hps2, %hps2⟩
  obtain ⟨hro, htsz, htpl, htnz⟩ := leaseTxnD_ok tK lu (by decide)
  obtain ⟨htpm, htin⟩ := leaseTxnD_model tK lu
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %tctx %tcd %tcancel ⟨#Htcancel, #Htctx, #Htce, -, #Htout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease lu as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts := etcd_auth.optsAt_one (GF := GF) _ f (withLeaseM lu) $$ [Hslo Hf]
  · iframe #
  (try wp_auto)
  wp_apply (wp_OpPut tK go!"v" _ [withLeaseM lu]) as %op1 #Hop1
  · iframe #
    ipureintro
    simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [op1])
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  ipersist Htsl
  ihave #Hops := etcd_auth.opsAt_one (GF := GF) _ op1 (opPutModel tK go!"v" [withLeaseM lu]) $$ [Htsl Hop1]
  · iframe #
  (try wp_auto)
  wp_apply (wp_Txn ucl uapi [au] V Γ tctx tcd) $$ [$Hlt] as %tv ⟨Hlt, %tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (wp_Then tp _ tctx tcd TxnBuild.empty _ _ [.put tK go!"v" lu]) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_leasePutD], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [au] tctx tcd ⟨leaseTxn tK lu, false, true, false⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, leaseTxn]
  (try wp_auto)
  wp_apply (wp_Commit ucl uapi tp [au] V Γ ucfg γR Lset tctx tcd none ⟨leaseTxn tK lu, false, true, false⟩
      (psAtLeast γc 3) hau hauth hγR (outTokOk_none _)) $$ [$Hlt Hobj] as %tresp %terr ⟨Hlt, Ht⟩
  · iframe Hobj; iframe #
    isplitl []
    · ipureintro; exact htin
    isplitl []
    · iright
      isplitl []
      · ipureintro; exact ⟨hro, Or.inr ⟨hlm, htpl⟩, htnz,
          txnNestOk_of_plain _ (txnWireOf_plain _ htpm) htin, leaseTxnD_shape tK lu (by decide)⟩
      iunfold writeAuD
      ihave #Htx := cell_txnTAu Γ.kv γc lz lu ps2 hps2 (opGrantD Γ.kv (principalOf ucfg)
        (.txn (txnWireOf (leaseTxn tK lu))) Lset) $$ []
      · iframe #
      iexact Htx
    ipureintro; exact htsz
  (try wp_auto)
  wp_apply Htcancel
  (try wp_auto)
  icases Ht with (⟨%Hterr, %mt, %σt, -, HQt, -⟩ | %Hterr)
  rotate_left
  · cases terr with
    | nil => exact absurd rfl Hterr.1
    | ok ei =>
      (try wp_auto)
      wp_apply wp_ended as %r -
      (try wp_auto)
      iapply HΦ; iframe Hlt
  subst Hterr
  isimp only [hro, Bool.false_eq_true, ↓reduceIte] at HQt
  iunfold psAtLeast at HQt
  icases HQt with ⟨%ps3, #Hps3, %hps3⟩
  (try wp_auto)
  -- `ownLease(vcli)`: v's own lease at `av`, holding no key (its grant recorded in the cell's `gs` only); its
  -- lessor lower bound at v's member is what `foreign`'s calls there take
  ihave #Hgov := cell_grantWriteAuD Γ.kv γc (principalOf vcfg) (W64 9000000000) Lset (by decide) hlm $$ Hinv
  wp_apply (wp_ownLease vcl av V Γ midv vcfg γR Lset mv (gsHas γc) hau hls hauth hlm hγR hAs) $$ [$Hlt]
    as %okv ⟨Hlt, Hov⟩
  · iframe #
  icases Hov with (%Hov | ⟨%Hov, %mvl, #Hlbv⟩)
  · subst Hov
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hov
  (try wp_auto)
  -- `barriers(eps)` again: only its result is used
  wp_apply (wp_barriers eps addrs V Γ γR Lset Htb hpe hAs hau hauth hγR) $$ [$Hlt] as %ok2 ⟨Hlt, Hb2⟩
  · iframe #
  icases Hb2 with (%Hb2 | ⟨%Hb2, -⟩) <;> subst Hb2
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  -- `ready()`
  ihave #Hready' := Hready
  iunfold readySpec at Hready'
  wp_apply Hready'
  (try wp_auto)
  -- `noAuth(cli, "anon", lu)` at `a0`, `noAuth(bcli, "bad", lu)` at `au`: the frozen floor refutes
  -- every anonymous lease check; the revocation's update from the cell (`revokeLu_updateD`)
  ihave ⟨%mz', -, #Hlbz, -⟩ := lease.leaseLiveFrom_lb (Γ.ls mid0) iz lz lzl $$ Hlvz
  ihave ⟨%mu', -, #Hlbu, -⟩ := lease.leaseLiveFrom_lb (Γ.ls midu) iu lu lul $$ Hlvu
  ihave #HnoA := noAuth_refutesD Γ γR mid0 Lset m0 γz hs rr hadm hst $$ HkvI Hfz Hfd0
  ihave #HnoB := noAuth_refutesD Γ γR midu Lset mu γz hs rr hadm hst $$ HkvI Hfz Hfdu
  ihave #HgoN := cell_grantWriteAuD Γ.kv γc none (W64 9000000000) Lset (by decide) hlm $$ Hinv
  ihave #HrvA := revokeLu_updateD Γ.kv γc γz hs Lset Lset rr none go!"anon" lz lu ps3 hps3 hlu0
    (List.prefix_refl _) hadm hst (userOk_none_akUser _) (Or.inl rfl) $$ [Hinv HlbU Hps3 Hfz]
  · iframe #
  ihave #HrvB := revokeLu_updateD Γ.kv γc γz hs Lset Lset rr none go!"bad" lz lu ps3 hps3 hlu0
    (List.prefix_refl _) hadm hst (userOk_none_akUser _) (Or.inr (Or.inl rfl)) $$ [Hinv HlbU Hps3 Hfz]
  · iframe #
  wp_apply (wp_noAuth cl go!"anon" a0 lu V Γ mid0 cfg0 γR Lset m0 mz' (gsHas γc) (revoked γc)
      hau hls hauth hlm hγR hP0 hAs) $$ [$Hlt] as Hlt
  · rw [hP0]; iframe #
  (try wp_auto)
  wp_apply (wp_noAuth bcl go!"bad" au lu V Γ midu bcfg γR Lset mu mu' (gsHas γc) (revoked γc)
      hau hls hauth hlm hγR hPb hAs) $$ [$Hlt] as Hlt
  · rw [hPb]; iframe #
  (try wp_auto)
  -- u's put of `a/x` with root's lease `Lz`, refused (`refused_updateD`: `Lz` holds `z/lease`)
  have hcellZ : ∀ σ ids ps gs d, CellOk σ ids ps gs d → [lz] <+: ids → ps1.length ≤ ps.length →
      leaseOf zK σ.kvs = some lz ∧ lz ≠ W64 0 := by
    intro σ ids ps gs d h hpre hps
    obtain ⟨t, rfl⟩ := hpre
    have hz := h.1.z_at (by omega)
    simp [lzOf] at hz
    exact ⟨hz, hlz0⟩
  have hwu : (go!"u" : GoString) = go!"anon" ∨ (go!"u" : GoString) = go!"bad" ∨ (go!"u" : GoString) = go!"v" ∨
      ((go!"u" : GoString) = go!"u" ∧ ¬ etcd_auth.inRangeK zK) :=
    Or.inr (Or.inr (Or.inr ⟨rfl, not_inRangeK_zK⟩))
  ihave #Hrfp := refused_updateD Γ.kv γc γz hs Lset Lset rr (some go!"u") go!"u" (.put (leasePutOp xK lz)) zK lz
    [lz] ps1 (fun _ => iprop(False)) (List.prefix_refl _) hadm hst
    (opChecksLeaseD_put Γ.kv _ (leasePutOp xK lz)) (userOk_some_akUser _ (Or.inl rfl)) hcellZ hwu
    $$ [Hinv HlbZ Hps1 Hfz]
  · iframe #
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -, #Hpout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease lz as %f2 #Hf2
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f2])
  isplitr
  · ipureintro; rfl
  iintro %slo2 ⟨Hslo2, -⟩
  ipersist Hslo2
  ihave #Hopts2 := etcd_auth.optsAt_one (GF := GF) _ f2 (withLeaseM lz) $$ [Hslo2 Hf2]
  · iframe #
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  have hokx : ¬ (opPutModel xK go!"v" [withLeaseM lz]).putPanics ∧
      (opPutModel xK go!"v" [withLeaseM lz]).t = W64 2 :=
    ⟨by simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero],
      rfl⟩
  wp_apply (wp_Put ucl uapi [au] V Γ ucfg γR Lset pctx pcd none xK go!"v" _ [withLeaseM lz]
      (fun _ => iprop(False)) hauth hγR (outTokOk_none _)) $$ [$Hlt] as %presp %perr ⟨Hlt, Hp⟩
  · rw [leasePut_wire, hPu]
    iframe #
    ipureintro
    exact ⟨⟨hokx.1, hokx.2, Or.inr hlm⟩, hszL xK lz (by decide)⟩
  (try wp_auto)
  wp_apply Hpcancel
  (try wp_auto)
  icases Hp with (⟨%Hperr, %mp, %σp, -, Hf, -⟩ | %Hperr)
  · iexfalso
    iexact Hf
  wp_apply (wp_refused go!"u" _ perr Hperr.1)
  (try wp_auto)
  -- u's transaction putting `a/x` with `Lz`, refused (`refused_updateD`, `opChecksLeaseD_txn`)
  ihave #Hrft := refused_updateD Γ.kv γc γz hs Lset Lset rr (some go!"u") go!"u"
    (.txn (txnWireOf (leaseTxn xK lz))) zK lz [lz] ps1 (fun _ => iprop(False)) (List.prefix_refl _) hadm hst
    (opChecksLeaseD_txn Γ.kv _ xK lz) (userOk_some_akUser _ (Or.inl rfl)) hcellZ hwu
    $$ [Hinv HlbZ Hps1 Hfz]
  · iframe #
  obtain ⟨hro', htsz', htpl', htnz'⟩ := leaseTxnD_ok xK lz (by decide)
  obtain ⟨htpm', htin'⟩ := leaseTxnD_model xK lz
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %xctx %xcd %xcancel ⟨#Hxcancel, #Hxctx, #Hxce, -, #Hxout, -⟩
  (try wp_auto)
  wp_apply wp_WithLease lz as %f3 #Hf3
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f3])
  isplitr
  · ipureintro; rfl
  iintro %slo3 ⟨Hslo3, -⟩
  ipersist Hslo3
  ihave #Hopts3 := etcd_auth.optsAt_one (GF := GF) _ f3 (withLeaseM lz) $$ [Hslo3 Hf3]
  · iframe #
  (try wp_auto)
  wp_apply (wp_OpPut xK go!"v" _ [withLeaseM lz]) as %op3 #Hop3
  · iframe #
    ipureintro
    simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]
  (try wp_auto)
  wp_apply wp_slice_literal (l := [op3])
  isplitr
  · ipureintro; rfl
  iintro %tsl3 ⟨Htsl3, -⟩
  ipersist Htsl3
  ihave #Hops3 := etcd_auth.opsAt_one (GF := GF) _ op3 (opPutModel xK go!"v" [withLeaseM lz]) $$ [Htsl3 Hop3]
  · iframe #
  (try wp_auto)
  wp_apply (wp_Txn ucl uapi [au] V Γ xctx xcd) $$ [$Hlt] as %tv3 ⟨Hlt, %tp3, %Htv3, Hobj3, #Hkt3⟩
  · iframe #
  subst Htv3
  (try wp_auto)
  wp_apply (wp_Then tp3 _ xctx xcd TxnBuild.empty _ _ [.put xK go!"v" lz]) $$ [Hobj3] as Hobj3
  · iframe #
    iframe Hobj3
    ipureintro
    exact ⟨by simp [txnOpOf_leasePutD], rfl, rfl⟩
  ihave Hobj3 : txnObjAt (GF := GF) tp3 [au] xctx xcd ⟨leaseTxn xK lz, false, true, false⟩ $$ [Hobj3]
  · iExactEq Hobj3
    simp [TxnModel.empty, leaseTxn]
  (try wp_auto)
  wp_apply (wp_Commit ucl uapi tp3 [au] V Γ ucfg γR Lset xctx xcd none ⟨leaseTxn xK lz, false, true, false⟩
      (fun _ => iprop(False)) hau hauth hγR (outTokOk_none _)) $$ [$Hlt Hobj3] as %xresp %xerr ⟨Hlt, Hx⟩
  · iframe Hobj3; iframe #
    isplitl []
    · ipureintro; exact htin'
    isplitl []
    · iright
      isplitl []
      · ipureintro; exact ⟨hro', Or.inr ⟨hlm, htpl'⟩, htnz',
          txnNestOk_of_plain _ (txnWireOf_plain _ htpm') htin', leaseTxnD_shape xK lz (by decide)⟩
      rw [hPu]
      iexact Hrft
    ipureintro; exact htsz'
  (try wp_auto)
  wp_apply Hxcancel
  (try wp_auto)
  icases Hx with (⟨%Hxerr, %mx, %σx, -, Hf, -⟩ | %Hxerr)
  · isimp only [hro', Bool.false_eq_true, ↓reduceIte] at Hf
    iexfalso
    iexact Hf
  wp_apply (wp_refused go!"u" _ xerr Hxerr.1)
  (try wp_auto)
  -- `absent(root, xKey, ...)` at `a0` (the read update `cellSeen`: `a/x` is never written)
  have hszG : ∀ k : GoString, k.length ≤ 2 ^ 20 → opSizeOk (opGetModel k []) := fun k hk =>
    opSizeOk_opGetModel (K := 2 ^ 28) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by omega) (by decide)
  have hnone : ∀ (k : GoString) (σ : KVState), mvcc.findKey k σ.kvs = none → ∀ v ∈ σ.kvs, v.key ≠ k :=
    fun k σ h v hv hk => by
      have := List.filter_eq_nil_iff.1 (client.filter_key_of_findKey_none _ _ h) v hv
      simp [hk] at this
  wp_apply (wp_absent rcl a0 xK _ V Γ rcfg γR Lset (cellSeen γc ps3 0) hau hauth hγR (hszG xK (by decide)) hAs)
    $$ [$Hlt] as %okx ⟨Hlt, -⟩
  · iframe #
    isplitl []
    · iintro !>
      iright
      ihave H := cell_readAu Γ.kv γc ps3 0 $$ [Hinv Hps3 Hd0]
      · iframe #
      iunfold kvReadAu at H
      iunfold kvAu at H
      icases H with #H
      iexact H
    iintro !> %σ #HQ
    iunfold cellSeen at HQ
    icases HQ with ⟨%ids, %ps, %gs, %d, %h, -⟩
    ipureintro
    exact hnone xK σ h.1.1.x_none
  cases okx
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  -- `foreign(ucli, "u", lz, zKey)` at `au`: its revocation refused (`Lz` holds `z/lease`), its TimeToLive check
  -- at `z/lease` refuted from the frozen floor (`foreign_refutesD`)
  ihave #Hrfr := refused_updateD Γ.kv γc γz hs Lset Lset rr (some go!"u") go!"u" (.leaseRevoke lz) zK lz
    [lz] ps1 (fun _ => iprop(False)) (List.prefix_refl _) hadm hst
    (opChecksLeaseD_revoke Γ.kv _ lz) (userOk_some_akUser _ (Or.inl rfl)) hcellZ hwu
    $$ [Hinv HlbZ Hps1 Hfz]
  · iframe #
  ihave #Hru := foreign_refutesD Γ γR midu Lset mu γz hs rr hadm hst (some go!"u") zK (Or.inl ⟨rfl, rfl⟩)
    $$ HkvI Hfz Hfdu
  ihave #HnoTu : □ (∀ n : Nat, ⌜mu ≤ n⌝ -∗
      leaseCheckD (Γ.au midu) (some go!"u") n
        (fun info => auth.permVerdictFrom (.on (Γ.au midu)) n info zK [] .read GoInterface.nil) -∗
      monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False) $$ []
  · iintro !> %n %hn Hc _
    iapply Hru $$ %n %hn Hc
  wp_apply (wp_foreign ucl go!"u" au lz zK V Γ midu ucfg γR Lset mu mu' (fun _ => iprop(False))
      (monoNatAuthOwn γc.a (1 : Qp).half 0) hau hls hauth hlm hγR (fun h => absurd h (by decide)) hAs)
    $$ [$Hlt Ha] as ⟨Hlt, Ha⟩
  · rw [hPu]
    iframe Ha; iframe #
    iintro !> %σ Hf _
    iexfalso; iexact Hf
  (try wp_auto)
  -- `foreign(vcli, "v", lu, aKey)` at `av`: a revocation of `Lu` tells `revoked`, refuted while the main
  -- thread holds u's revocation unpermitted (`cell_not_revoked`); its TimeToLive check at `a/lease` refuted from
  -- the frozen floor, its lessor lower bound v's own lease's (`Hlbv`)
  ihave #Hrvv := revokeLu_updateD Γ.kv γc γz hs Lset Lset rr (some go!"v") go!"v" lz lu ps3 hps3 hlu0
    (List.prefix_refl _) hadm hst (userOk_some_akUser _ (Or.inr rfl)) (Or.inr (Or.inr rfl))
    $$ [Hinv HlbU Hps3 Hfz]
  · iframe #
  ihave #Hrv := foreign_refutesD Γ γR midv Lset mv γz hs rr hadm hst (some go!"v") aK (Or.inr ⟨rfl, rfl⟩)
    $$ HkvI Hfz Hfdv
  ihave #HnoTv : □ (∀ n : Nat, ⌜mv ≤ n⌝ -∗
      leaseCheckD (Γ.au midv) (some go!"v") n
        (fun info => auth.permVerdictFrom (.on (Γ.au midv)) n info aK [] .read GoInterface.nil) -∗
      monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False) $$ []
  · iintro !> %n %hn Hc _
    iapply Hrv $$ %n %hn Hc
  wp_apply (wp_foreign vcl go!"v" av lu aK V Γ midv vcfg γR Lset mv mvl (revoked γc)
      (monoNatAuthOwn γc.a (1 : Qp).half 0) hau hls hauth hlm hγR (fun h => absurd h (by decide)) hAs)
    $$ [$Hlt Ha] as ⟨Hlt, Ha⟩
  · rw [hPv]
    iframe Ha; iframe #
    iintro !> %σ #Hr _ Ha
    iapply (cell_not_revoked Γ.kv γc σ ⊤ (by simp))
    iframe Ha; iframe #
  (try wp_auto)
  -- root's `Get(zKey)` at `a0`: `z/lease` on `Lz` (the read update `cellSeen`, `seenD_z`)
  ihave ⟨%rapi, #Hruc⟩ := userClientAt_of_userCli rcl a0 V rcfg Γ $$ [Hru Hm0]
  · iframe #
  ihave #Hruc' := Hruc
  iunfold etcd_dist.authd.userClientAt at Hruc'
  icases Hruc' with ⟨#Hrkc, -⟩
  iunfold kvClientAt at Hrkc
  icases Hrkc with ⟨-, -, #Hrkvf, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -, #Hgout, -⟩
  (try wp_auto)
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave Hres := optsAt_res slice.nil [] iprop(True) $$ Hnil
  wp_apply (wp_Get rcl rapi [a0] V Γ rcfg γR Lset gctx gcd none zK slice.nil [] iprop(True) (cellSeen γc ps1 0)
      hau hauth hγR (outTokOk_none _)) $$ [$Hlt $Hres] as %gresp %gerr ⟨Hlt, -, Hgo⟩
  · iframe #
    isplitl []
    · itrivial
    isplitl []
    · (try rw [show (opGetModel zK []).base.sortSet = false from rfl])
      iapply sortNamesIf_false
    isplitl []
    · ipureintro; exact ⟨by simp [opGetPanics, opFold, OpFull.newOp, OpModel.zero], rfl, rfl⟩
    isplitl []
    · iintro !>
      iright
      ihave H := cell_readAu Γ.kv γc ps1 0 $$ [Hinv Hps1 Hd0]
      · iframe #
      iunfold kvReadAu at H
      iunfold kvAu at H
      icases H with #H
      iexact H
    ipureintro
    exact hszG zK (by decide)
  (try wp_auto)
  wp_apply Hgcancel
  (try wp_auto)
  icases Hgo with (⟨%Hgerr, %mg, %σg, Hmg, #HQg, %Hs, -⟩ | %Hgerr)
  rotate_left
  · cases gerr with
    | nil => exact absurd rfl Hgerr.1
    | ok e =>
      (try wp_auto)
      wp_apply wp_ended as %r -
      (try wp_auto)
      iapply HΦ; iframe Hlt
  subst Hgerr
  (try wp_auto)
  ihave %Hzg := seenD_z γc ps1 0 σg lz hps1 $$ [HQg HlbZ]
  · iframe #
  obtain ⟨kvz, hfz, hlz⟩ := leaseOf_some_findKey Hzg
  have hkvs : mg.kvs = [kvz] := by
    obtain ⟨-, hsel, -, -, hlog⟩ := Hs
    have hrr : σg.readRev (W64 0) = σg.rev := by simp [KVState.readRev]
    have hkv : (σg.at (σg.readRev (W64 0))).kvs = σg.kvs := by
      rw [hrr]
      rfl
    try rw [show (rangeWireOf (opGetModel zK [])).base.rev = W64 0 from rfl] at hsel
    rw [hkv] at hsel
    rw [(srvRangeOk_getKey zK σg.kvs mg.kvs mg.more hsel).1]
    have hsort : σg.kvs.Pairwise etcdKvLess := by
      rw [kvLogOk_kvs σg hlog]; exact mvcc.stateAfter_sorted _
    exact client.filter_key_of_findKey zK _ hsort kvz hfz
  iunfold rangeRespMsg at Hmg
  icases Hmg with ⟨%Hnn, %h, %sl, %kvps, #Hh, #Hhf, #Hkvf', #Hsl, #Hkvs, #Hmore, #Hcount⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen', #Hall⟩
  obtain ⟨p0, Hp0⟩ : ∃ p0, kvps[0]? = some p0 := by
    have : 0 < kvps.length := by rw [Hlen', hkvs]; simp
    exact ⟨kvps[0], List.getElem?_eq_getElem this⟩
  ihave #Hkv := Hall $$ %0 %p0 %kvz %Hp0 %(by rw [hkvs]; rfl)
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, -, -, #HlF, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have H1 : sl.len = W64 1 := by
    have hl := Hsll.1
    rw [Hlen', hkvs] at hl
    simp at hl
    word
  (try wp_auto)
  simp only [H1]
  (try wp_auto)
  have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by rw [H1]; constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hp0
  (try wp_auto)
  simp only [hlz]
  (try wp_auto)
  -- u revokes its own lease `Lu` (`cell_permit`, then `cell_revokeUAu`): the update tells `revoked`
  imod (cell_permit Γ.kv γc ⊤ (by simp)) $$ [Ha] with ⟨Ha1, #Hal1⟩
  · iframe Ha; iframe #
  ihave ⟨%ulp, #Hulu⟩ := leaseUserAt_of_userCli ucl au V ucfg Γ midu $$ [Huu Hatu]
  · iframe #
  ihave #Hulu' := Hulu
  iunfold leaseUserAt at Hulu'
  icases Hulu' with ⟨#Hulc, -, -⟩
  iunfold view.leaseClientAt at Hulc
  icases Hulc with ⟨-, -, #Hulf, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %rctx %rcd %rcancel ⟨#Hrcancel, #Hrctx, #Hrce, -, #Hrout, -⟩
  (try wp_auto)
  wp_apply (wp_Revoke ucl ulp au V Γ midu ucfg γR Lset mu rctx rcd none lu (revoked γc) hau hauth hlm hγR
      (outTokOk_none _)) $$ [$Hlt] as %rresp %rerr ⟨Hlt, Hrv⟩
  · iframe #
    iunfold writeAuD
    ihave #Hrvk := cell_revokeUAu Γ.kv γc lz lu ps3 hps3
      (opGrantD Γ.kv (principalOf ucfg) (.leaseRevoke lu) Lset) $$ [Hinv HlbU Hps3 Hal1]
    · iframe #
    iexact Hrvk
  (try wp_auto)
  wp_apply Hrcancel
  (try wp_auto)
  icases Hrv with (⟨%Hrerr, %mr, -, ⟨%σr, #Hrvd⟩, -⟩ | %Hrerr)
  rotate_left
  · cases rerr with
    | nil => exact absurd rfl Hrerr.1
    | ok e =>
      (try wp_auto)
      wp_apply wp_ended as %r -
      (try wp_auto)
      iapply HΦ; iframe Hlt
  subst Hrerr
  iunfold revoked at Hrvd
  (try wp_auto)
  -- `absent(root, aKey, ...)`, `absent(root, txnKey, ...)` (the read update `cellSeen … 1`: `seenD_gone`)
  wp_apply (wp_absent rcl a0 aK _ V Γ rcfg γR Lset (cellSeen γc ps3 1) hau hauth hγR (hszG aK (by decide)) hAs)
    $$ [$Hlt] as %oka ⟨Hlt, -⟩
  · iframe #
    isplitl []
    · iintro !>
      iright
      ihave H := cell_readAu Γ.kv γc ps3 1 $$ [Hinv Hps3 Hrvd]
      · iframe #
      iunfold kvReadAu at H
      iunfold kvAu at H
      icases H with #H
      iexact H
    iintro !> %σ #HQ
    ihave %Hg := seenD_gone γc ps3 σ $$ HQ
    ipureintro
    exact hnone aK σ Hg.1
  cases oka
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  wp_apply (wp_absent rcl a0 tK _ V Γ rcfg γR Lset (cellSeen γc ps3 1) hau hauth hγR (hszG tK (by decide)) hAs)
    $$ [$Hlt] as %okt ⟨Hlt, -⟩
  · iframe #
    isplitl []
    · iintro !>
      iright
      ihave H := cell_readAu Γ.kv γc ps3 1 $$ [Hinv Hps3 Hrvd]
      · iframe #
      iunfold kvReadAu at H
      iunfold kvAu at H
      icases H with #H
      iexact H
    iintro !> %σ #HQ
    ihave %Hg := seenD_gone γc ps3 σ $$ HQ
    ipureintro
    exact hnone tK σ Hg.2
  cases okt
  · (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  wp_apply wp_checked as %r -
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
