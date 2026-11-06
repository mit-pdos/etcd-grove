/-
**A replayed normal entry: `applyEntryNormal(e, false)` at a restart** (R2d'a A3, 2026-11-06; DRAFT,
nothing frozen: `notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", "R2d'a Draft"). The
proof of `ApplyRDefs.lean`'s `EtcdServer.applyEntryNormal.specRepOff` from the translated body, over
the callee specs `EtcdServer__applyEntryNormal.lean`'s `wp_proofOff` uses, at `shouldApplyV3 =
false`: `apply.Apply`'s premises that only `dispatch`'s `v3` cases read are guarded by `v3` (Q22 (1)
(a)), so the replay gives them nothing; the rest buckets at the backend's table (`srvRestRp`) are
`apply.Apply`'s `E.RO`, half and ids, and come back with the attribute write (`restEntryV2`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
  go_etcd_io.etcd.server.v3.etcdserver.cindex

section lemmas
variable [GooseExts]

/-- **`Apply`'s rest image at `v3 = false`** (R2d'a A3, DRAFT): the request's attribute write
(`restAfter … false`), whatever the outcome, for a request of a committed entry's shape. -/
theorem restOutA_false (lm : lease.Mode) (rq : apply.IRRModel) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (T : List w64) (t : w64) (r : apply.RestM) (hp : plainOrCmpG lm rq)
    (hs : apply.applyStep rq false x x' out) :
    apply.revokeRestA T rq false out (apply.grantRestA t rq false out (apply.restOut rq false out r)) =
      apply.restAfter rq false r := by
  rw [restOut_plainOrCmpG lm rq false x x' out r hp hs]
  cases out <;> simp [apply.revokeRestA, apply.grantRestA, apply.revokeRest_noV3,
    apply.grantRest_noV3]

/-- `Apply`'s ids at `v3 = false`: unchanged. -/
theorem idsA_false (rq : apply.IRRModel) (out : apply.ApplyOut) (L : List w64) :
    apply.revokeIdsA rq false out (apply.grantIdsA rq false out L) = L ∧
      apply.grantIdsA rq false out L = L := by
  cases out <;> simp [apply.revokeIdsA, apply.grantIdsA, apply.revokeIds_noV3, apply.grantIds_noV3]

/-- A request's v2-only step is the entry's (`restEntryV2`). -/
theorem restEntryV2_req (m : EntryModel) (rq : apply.IRRModel) (r : apply.RestM)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    restEntryV2 m r = apply.restAfter rq false r := by
  unfold restEntryV2; rw [if_pos ht, if_neg hd, hdec]

/-- An entry with no data: nothing. -/
theorem restEntryV2_nodata (m : EntryModel) (r : apply.RestM) (ht : m.typ = W32 0)
    (hd : m.data = []) : restEntryV2 m r = r := by
  unfold restEntryV2; rw [if_pos ht, if_pos hd]

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 1600000 in
/-- **`applyEntryNormal.specRepOff`** (R2d'a A3, DRAFT): a replayed normal entry, from the body. -/
theorem EtcdServer.applyEntryNormal.wp_proofRepOff
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hE : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG))
    (hA0 : apply.Apply.spec (GF := GF) (hG := hG))
    (hUb : apply.uberApplier.Apply.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specRepOff (GF := GF) (hG := hG) := by
  have hA := apply.Apply.spec_rec hA0 hUb
  have hGI := wp_entryAt_GetIndex hGI
  intro s γ ci TM E ρ b e m st x γr A₀ r _hoff
  wp_start as ⟨#Hsrv, #Hewo, #He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, HFS, #Hcm, HRS, #HA0, %HmA,
    %Hpo⟩
  obtain ⟨Hp, Hok, Htyp, Hci, Hmem⟩ := Hpo
  wp_apply wp_with_defer as %defer defer
  iunfold isServer at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
  ihave #Hat' := Hat
  iunfold srvAtomics at Hat'
  icases Hat' with ⟨-, -, #Hkvi⟩
  ihave #Hkvi' := Hkvi
  iunfold srvKVInvs at Hkvi'
  icases Hkvi' with ⟨#HkI, -, #HrI, -, -, %Hlmt, -⟩
  -- the committed entry's shape (the KV invariant's, `kv_log_plain`)
  imod kv_log_plain γr.raft γr.kv A₀ $$ HkI HrI HA0 with %Hpc0
  have Hpe : plainEntryM γr.kv.cmp E.lm m := Hlmt.2 ▸ Hpc0.1 m HmA
  icases srvApplyKV_idxCert s E ρ.wait x $$ HKV with ⟨HKV, #Hcx⟩
  iunfold srvFieldsAt at Hfv
  icases Hfv with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl, #Hrc, #Hq,
    #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  have Hpl : ∀ rq, m.data ≠ [] → apply.irrDecode m.data = some rq → plainOrCmpG E.lm rq :=
    fun rq hd hdec => plainOrCmpG_of_entryM _ _ m Hpe Htyp hd rq hdec
  ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
  ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  iunfold lessorOk at Hlok
  icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
  wp_auto
  wp_if_destruct
  · -- no data: the first commit's notice, the lessor's promotion at a leader
    have hnil : m.data = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
    ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
        ⌜entryStep m false x x' out⌝) $$ [HKV]
    · iexists x, apply.ApplyOut.skipped
      iframe HKV
      ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
    ihave HRS : srvRestRp E γr A₀ (restEntryV2 m r) $$ [HRS]
    · rw [restEntryV2_nodata m r Htyp hnil]; iexact HRS
    wp_apply hN fv.firstCommit
    · iexact Hnot
    wp_apply hL s fv.memberID as %ldr -
    · iframe Hmid Hlead
    cases ldr
    · (try wp_auto)
      iapply HΦ
      iframe Hbe Hst Hlr Hgr HFS HKV HRS
    · (try wp_auto)
      wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
      · iframe Het Htm
      rw [Hli]
      (try wp_auto)
      (try dsimp only)
      ihave #HP := HPromote $$ %dur
      wp_apply HP
      (try wp_auto)
      iapply HΦ
      iframe Hbe Hst Hlr Hgr HFS HKV HRS
  · -- data: the applier, v2-only
    have hdata : m.data ≠ [] := by
      intro h; apply Hif
      have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
      have h2 := Hdlen.2
      have h1' : (sint.Z d.len).toNat = 0 := h1.symm
      have h3 : sint.Z d.len = 0 := by omega
      word
    obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
    iunfold srvApplyKV at HKV
    icases HKV with ⟨%ua, Hua, #Happl, HKV, Hbo, HRA, HAR, ⟨%w', %RD, #Hw', #Hwok', HRD⟩, Hrdat⟩
    icombine Hw Hw' gives %Hweq
    subst Hweq
    ihave ⟨HKV, %HaOn⟩ := applyKV_authOn E ua x $$ HKV
    ihave #Hcp : apply.certPreV false E x.chain rq x.log $$ []
    · iunfold apply.certPreV; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    ihave HFSE : E.FS $$ [HFS]
    · rw [HEo.2.1]; iexact HFS
    ihave HSpF : iprop(if false = true then apply.ciSplit E iprop(True) else iprop(True)) $$ []
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    iapply wp_fupd
    -- the rest buckets at the backend's table: `apply.Apply`'s image, half and ids
    ihave ⟨HRS, HEv⟩ := (srvRestRp_eq_at E γr A₀ r).1 $$ HRS
    ihave ⟨%f, %Hfb, HRS, HLt, #HGI, #HRq⟩ := (srvRestAt_open E _ _).1 $$ HRS
    ihave ⟨%U, HEv, %HUok⟩ := srvEver_open E A₀ $$ HEv
    ihave #HGf : iprop(□ (⌜false = true⌝ → apply.grantFresh E rq U)) $$ []
    · iintro !> %h; cases h
    ihave #Hgpq : iprop(□ (⌜false = true⌝ → apply.grantPermRq E rq)) $$ []
    · iintro !> %h; cases h
    ihave #Hcpq : iprop(□ (⌜false = true⌝ → apply.cmpPermRq E rq)) $$ []
    · iintro !> %h; cases h
    (try wp_auto)
    ihave %Hat := entryWaitOk_attr ρ E m Htyp $$ Hewo
    have Hrr : apply.restReqOk rq r := by
      intro hk a ha'
      have hin := ((Hat Htyp hdata rq hdec) hk).2 a ha'
      have hin' : a.memberID ∈ γr.raft.raft.cfg := by rw [← Hrd]; exact hin
      exact Hmem _ hin'
    ihave ⟨Hrv, Hrdb⟩ := revokeOwn_take E rq (Hpl rq hdata hdec) $$ [Hrdat]
    · iframe Hrdat HGI
    wp_apply hA fv.lg e m ua fv.w false E iprop(True) iprop(True) iprop(True) x rq id0 RD
      (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) none x.log
      _ _ U $$ [HKV Hwt HRD HFSE HSpF HRS HLt HEv Hrv]
      as %ar %id ⟨HRD, HFS, -, #Har, -, %Hid, %x', %out, HKV, HLt, HEv, Hrv, HRS, %Hgo, -, -,
        %Hstep0, -, -, -⟩
    · iframe Happl Hwok' HRD He HKV Hwt Hcp HFSE HSpF HRS HLt HEv HGf Hrv Hgpq
      isplitr
      · simp only [waitRegdOpt]; itrivial
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr
      · ipureintro; exact Hlgnn
      isplitr
      · itrivial
      iframe Hcx
      iframe Hcpq
      ipureintro
      exact ⟨hdec, hid, hrq, HaOn ▸ hdk, fun h => absurd h (by decide), by
        unfold apply.restReqOk; rw [apply.restLeasesWith_mem]; exact Hrr⟩
    ihave HFS : srvFS s $$ [HFS]
    · rw [← HEo.2.1]; iexact HFS
    have Hstep := Hstep0.1
    ihave Hrdat := Hrdb $$ Hrv
    -- the rest buckets back, with the attribute write
    rw [(idsA_false rq out _).1, (idsA_false rq out U).2]
    icases HRS with ⟨%t, -, HRS⟩
    rw [restOutA_false E.lm rq x x' out _ t _ (Hpl rq hdata hdec) Hstep,
      apply.restLeasesWith_comm (apply.restAfter rq false) (apply.restAfter_restGrantT rq false),
      ← restEntryV2_req m rq r Htyp hdata hdec]
    ihave HRS : srvRestRp E γr A₀ (restEntryV2 m r) $$ [HRS HLt HEv]
    · iapply (srvRestRp_eq_at E γr A₀ _).2
      isplitl [HRS HLt]
      · iapply (srvRestAt_open E _ _).2
        iexists f
        iframe HRS HLt HGI HRq
        ipureintro; exact Hfb
      iunfold srvEver; iexists U; iframe HEv; ipureintro; exact HUok
    ihave ⟨HKV, #Hcert⟩ := applyKV_idxCert E ua x' $$ HKV
    ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
    imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, -⟩
    (try wp_auto)
    imodintro
    wp_pures
    iapply HΦ
    iframe Hbe Hst Hlr Hgr HFS HRS
    iexists x', out
    isplitl
    · iunfold srvApplyKV; iexists ua; isplitl [Hua]; · iexact Hua
      isplitr; · iexact Happl
      isplitl [HKV]; · iexact HKV
      isplitl [Hbo]; · iexact Hbo
      isplitl [HRA]; · iexact HRA
      isplitl [HAR]; · iexact HAR
      isplitr [Hrdat]
      · iexists fv.w, RD; iframe Hw Hwok' HRD
      iexact Hrdat
    ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩

end proof

end EtcdGrove
end Perennial
