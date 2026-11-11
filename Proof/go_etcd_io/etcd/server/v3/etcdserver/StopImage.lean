/-
**The stopped backend's data, observed** (the restart plan's R2b-3d stage 3, 2026-11-04;
`notes/restart-plan.md`, "R2b-3d stage 3"; over mvcc's API since R6, 2026-11-07). Lean-first (no
Rocq counterpart).

`Cleanup`'s `backend.Close`, given the server's request of the stop's commit (`commitReq_freeze`:
the idle apply thread's state for the frozen protocol, `freezeY`), returns what the stopped batch
lock held at the data `D` its file holds (`bStopView`, at the store's write invariant `mvccW d.gx`
and the server's batch-lock invariant). Two observations of it make `D`'s image, as the merged
snapshot's window (`SnapSendBranch.mergedCreate_window`) makes the snapshot's:
* the store's part: mvcc's `mvccImage_stop.law` at the writer's state (`srvApi.stopImageG`, the
  stop's `snapImageG`), with the apply thread's whole share of the store's backend;
* the server's parts: the meta keys and the tracked buckets, read by the window's observation
  (`snapObsA`) on the stopped lock's pieces (`stop_obs`), the rest buckets by `bkRestAtM_of_obs`.
`stop_imageAt` turns the two into the image clause of the applied log (`srvDiskImage`'s).
(R6: until then, `lean`'s `stop_mergedObs` read the stopped `Key` bucket through mvcc's internals,
`txn.kvWriter_keyObs`, `apply.cmpObs`, `txn.kvWriter_noCmp`, at the writer's internal `lateWD`.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace srvApi
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

section stop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The stopped backend's image at the writer's state, generic** (`snapImageG`'s analogue for the
stop): `mvccImage_stop.law` at the update the store invariant and the writer's half `wSt γs log c`
make (`au_snap`, the half given back), with the whole share of the store's backend: the data `D`
the stopped lock held (`backend.Close`'s `bStopView`, at the store's write invariant) is the image
of `(log, c)`, a state the store reaches (`writer_facts`). -/
theorem stopImageG (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (hStop : mvccImage_stop.law (GF := GF))
    (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF)
    [∀ l, Persistent (Nx l)] [∀ l, Timeless (Nx l)] [∀ c, Persistent (Cp c)]
    [∀ c, Timeless (Cp c)] (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (bk : mvcc.KBReal) (Pk : IProp GF)
    (D : backend.Data) :
    kvStoreInvG kv γ Nx Cp γs ∗ wSt γs log c ∗ mvccBackend γ 1 (etcdStorage bk) Pk ∗
      backend.bStopView bk.γB bk.P (mvccW bk.gx) Pk D ⊢
    |={⊤}=> wSt γs log c ∗ mvccBackend γ 1 (etcdStorage bk) Pk ∗
      backend.bStopView bk.γB bk.P (mvccW bk.gx) Pk D ∗ ⌜imageStOk log c⌝ ∗
      ∃ u : Bool, mvccImage D log c u := by
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro ⟨#Hk, Hw, HB, Hsv⟩
  imod writer_facts Nx Cp Hp Hr kv γ γs log c $$ Hk Hw with ⟨Hw, -, -, -, %Hre⟩
  ihave HAU := au_snap Nx Cp Hp kv γ γs log c (wSt γs log c) $$ Hk Hw []
  · iintro H; iexact H
  ihave #Hk' := Hk
  iunfold kvStoreInvG at Hk'
  icases Hk' with ⟨#Hm, -⟩
  iunfold auSnap at HAU
  imod (hStop kv γ bk Pk D (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs log c))) $$ [HB Hsv HAU]
    with ⟨HB, Hsv, %σ, %u, ⟨%Hσ, Hw⟩, #Him⟩
  · iframe Hm HB Hsv HAU
  subst Hσ
  imodintro
  iframe Hw HB Hsv
  isplitr
  · ipureintro; exact Hre
  iexists u
  rw [show (stAt log c).log = log from rfl, show (stAt log c).crev = c from rfl]
  iexact Him

end stop

end srvApi

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The stopped lock's meta keys and tracked buckets** (see the file header): with the frozen
protocol at the apply thread's state `st` (`freezeY`, the stop's commit stored `ciEff γA st.k = ai`)
and its halves of the tracked buckets at the rest model's, what `Close` returned of the stopped lock
at `D` (at any client resource `W`) holds the consistent index `ai`, some term and the rest buckets
of the applied log (`bkRestAtM`, `mergedImgM`'s). -/
theorem stop_obs (γA : ApplyNames) (E : apply.AEnv GF) (γr : ReadNames) (ai : w64)
    (A : List EntryModel) (d : mvcc.KBReal) (f : w64 → w64) (st : ApplyState) (W : IProp GF)
    (D : backend.Data) (hcK : ciKeys d.P) (hRB : ∀ n ∈ restBuckets, d.P.RB n = true)
    (hci : ciEff γA st.k = ai) (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    freezeY γA st ∗
      backend.rbOwnIn d.γB membership.clusterBkts
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
      backend.rbPart d.γB (restSet E.authMode)
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
      backend.bStopView d.γB d.P W (batchLockInv γA (metaTM d.γB d.P)) D ⊢
    ⌜backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
        go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes = encMeta ai ∧
      (∃ t : w64, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName
        go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes = encMeta t) ∧
      bkRestAtM E.authMode (if E.lg then kvLeases γr.kv (γr.raft.pre ++ A) else []) γr.kv.c0
        γr.raft.raft.boot (γr.raft.pre ++ A) D⌝ := by
  iintro ⟨HY, Hrc, Hrn, Hsv⟩
  iunfold backend.bStopView at Hsv
  icases Hsv with ⟨-, HPk, -, Hhk, Hr, -, -⟩
  ihave Hnone := backend.rbPart_none (GF := GF) d.γB (∅ : GMap GoString backend.BktData)
  ihave %h := snapObsA γA d.γB d.P hcK st (restSet E.authMode)
    (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk (fun _ => False) ∅
    $$ %(backend.hkData d.P D) %(backend.rbData d.P D) [HY Hrc Hrn Hnone] HPk Hhk Hr
  · iframe HY Hrc Hrn Hnone
  ipureintro
  obtain ⟨⟨hci1, t1, ht1⟩, hrbD, -⟩ := h
  rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inl rfl)] at hci1
  rw [backend.hkData_lookup, ciKeys_hk hcK (Or.inr rfl)] at ht1
  exact ⟨by rw [← hci]; simpa using hci1, ⟨t1, by simpa using ht1⟩,
    bkRestAtM_of_obs E γr A d f D hRB hrbD hfb⟩

/-- **The image clause of the stopped backend's data** (the restart plan's R2b-3d stage 5a; the
pure part of `merged_image`; R6, 2026-11-07: over `mergedImgM` and mvcc's `mvccImage`, until then
`mergedObs` and `imageAt`): the window's image `mergedImgM` (auth off) of `D` at the applied index
`ai` of the applied log `A`, at the server with the KV's start values, is `srvDiskImage`'s backend
clause at the KV names: the server's parts `imageRestAt`, the state reachable and short, and mvcc's
image of the KV model's history at its compaction revision. -/
theorem stop_imageAt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hM : E.authMode = .off)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) :
    mergedImgM E.authMode E.lg γr ai A x.log x.crev D ∗ isServer s γ ci TM E ρ γr ∗
      kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗
        ⌜imageRestAt γr.kv γr.raft.raft.boot ai (γr.raft.pre ++ A) D ∧
          imageStOk (kvModel γr.kv A) (crevOf γr.kv A)⌝ ∗
        ∃ u : Bool, mvcc.api.mvccImage D (kvModel γr.kv A) (crevOf γr.kv A) u := by
  iintro ⟨#Hmi, #Hsrv, Hka⟩
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -, #Hrl, -, -, -, %Hlmk⟩
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ Hrl
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
  imod kv_log_plain γr.raft γr.kv A $$ Hki Hrl HA with %Hpl0
  imodintro
  isplitl [Hhi Hcert]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hcert
    ipureintro; exact ⟨hlog, hx⟩
  iunfold mergedImgM at Hmi
  icases Hmi with ⟨%hmi, %u, #Him⟩
  obtain ⟨hci', hterm, hrest, hre⟩ := hmi
  rw [hM] at hrest
  have hpre : γr.raft.pre = [] := by rw [hraft]
  have hn : E.lg = false → (kvLeases γr.kv (γr.raft.pre ++ A)).ids = [] := by
    intro hlg
    have hpl : plainLogM γr.kv.cmp .none A := by
      have := Hpl0.1
      rw [Hlmk, apply.AEnv.lm_of_lg_false hlg] at this
      exact this
    rw [hpre, List.nil_append]; unfold kvLeases; rw [kvTableOf_plainM _ _ _ A hpl]; rfl
  have hrestL := bkRestAtL_of_M_off E.lg hn hrest
  rw [← hlog, ← hx.2]
  isplitr
  · ipureintro; exact ⟨⟨hci', hterm, hrestL⟩, hre⟩
  iexists u
  iexact Him

end proof

end EtcdGrove
end Perennial
