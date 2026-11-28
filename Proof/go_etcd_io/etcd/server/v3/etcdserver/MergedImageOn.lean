/-
**The merged snapshot's image with auth on** (#7-on, 2026-11-03): `merged_image`'s mode-on twin.
The window's image (`mergedCreate_window` with the auth row's lend of the auth buckets,
`srvAuthApplyResB_lend`) gives every clause of `imageRestAtOn` (the rest buckets but the auth ones,
`bkRestAtM`; the auth buckets at the latest auth state, which the applied log determines,
`kvAppliedOn`) and mvcc's image of the history (`mergedImgM`; R4, 2026-11-07: until then the `Key`
bucket and the records at the store's mode). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The auth buckets are tracked rest buckets. -/
theorem authBkts_rest (n : GoString) (h : auth.authBkts n) : n ∈ restBuckets := by
  rcases h with rfl | rfl | rfl <;> simp [mvcc.restBuckets]

/-- **The auth buckets agree with a part of them** (`authBucketsAt` reads only them). -/
theorem authBucketsAt_congr (st : auth.AuthState) (D r : GMap GoString backend.BktData)
    (h : ∀ n, auth.authBkts n → D.lookup n = r.lookup n) (hr : authBucketsAt st r) :
    authBucketsAt st D := by
  have e : authDataOf D = authDataOf r := by
    unfold authDataOf
    rw [h go!"auth" (Or.inl rfl), h go!"authUsers" (Or.inr (Or.inl rfl)),
      h go!"authRoles" (Or.inr (Or.inr rfl))]
  unfold authBucketsAt at hr ⊢
  rw [e]; exact hr

/-- **(S2, #7-on) The merged snapshot's image with auth on** (the network's image certificate,
`srvNet`'s `img`, which the cluster's mode makes `srvImageOn`): the window's image `mergedImgM` at
the applied index `ai` of the applied log `A` (`kvAppliedOn`: the KV log and the auth state `sa`
the mode-on model's), at the apply thread's compaction revision, the model's (`hcr`), with the auth
buckets at `sa` (the lent part's), of a server with auth on and the KV's start values: the rest
buckets but the auth ones the rest model's (an auth-on log grants no lease, `kvTableOf_plainOn`),
mvcc's image of the history. (R4, 2026-11-07: over `mergedImgM` and the restated `dbImageOn`; until
then `mergedObsM`'s key image at the store's mode, off with auth on, and the receipt. `hcr`: the
on-mode apply thread's compaction revision `-1`, which its caller reads off the applier row and the
on-mode invariants, `srvApplyKVOn_crev`; R6, 2026-11-07: until then the model's `crevOf γr.kv A`,
which is `-1` too, `crevOf_plainOn`.) -/
theorem merged_imageOn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γa : auth.AuthNames) (ai : w64)
    (A : List EntryModel) (x : apply.ApplyKV) (sa : auth.AuthState) (D : backend.Data)
    (hM : E.authMode = .on γa) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) (hcr : x.crev = -1) :
    mergedImgM E.authMode E.lg γr ai A x.log x.crev D ∗ ⌜authBucketsAt sa D⌝ ∗
      isServerM true s γ ci TM E ρ γr ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) ⊢
      |={⊤}=> kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) ∗
        □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  iintro ⟨#Hmi, %hau, #Hsrv, Hka⟩
  iunfold mergedImgM at Hmi
  icases Hmi with ⟨%hobs, ⟨%u, #Him⟩, #Hrow⟩
  obtain ⟨hci, hterm, hrest, hre⟩ := hobs
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomicsM at Hat
  icases Hat with ⟨-, -, Hki⟩
  ihave %Hrw := srvKVInvsM_rows true s E γr $$ Hki
  ihave #Hinvs := srvKVInvsM_true s E γr $$ Hki
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, -, #HrI, -, -, -, %Hrows0, %Hrows1, -⟩
  have Hrows := And.intro Hrows0 Hrows1
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ HrI
  imod (kvInvOn_ch0 γr.raft γr.kv srvAuthSt0) $$ HkI with %hch
  imod (kvInvOn_authOn γr.raft γr.kv srvAuthSt0) $$ HkI with %hao
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨Hal, %Hch'⟩
  iunfold kvAppliedLOn at Hal
  icases Hal with ⟨#HA, Hhi, Hc, %Hl⟩
  imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A $$ HkI HrI HA with %Hpl
  -- (auth-lease S3a, Draft rev 5 §5) the model's lease mode the environment's
  have hlm : γr.kv.lm = E.lm := (Hrw rfl).1
  imodintro
  isplitl [Hhi Hc]
  · iunfold kvAppliedOn
    isplitl [Hhi Hc]
    · iunfold kvAppliedLOn
      iframe HA Hhi Hc
      ipureintro; exact Hl
    ipureintro; exact Hch'
  ihave #HA' : srvRLogLb (GF := GF) ⟨γr.raft.raft, [], W64 0⟩ A $$ []
  · rw [← hraft]; iexact HA
  have hxl : x.log = kvModelOn γr.kv srvAuthSt0 A := by unfold kvModelOn; rw [← Hl]
  have hsa : sa = srvAuthAtLog γr.kv srvAuthSt0 A := by unfold srvAuthAtLog; rw [← Hl]
  iintro !>
  simp only [srvNet]
  rw [hao, srvImageM_on]
  iunfold srvImageOn
  -- (keepfix (c) step 1, G5) the term row, the window's (`mergedImgM`)
  iframe Hrow
  iexists γr.kv
  isplitr
  · ipureintro; exact ⟨h0.1, hch, h0.2⟩
  iunfold dbImageOn
  iexists A, u
  iframe HA'
  rw [← hxl, crevOf_plainOn γr.kv A Hpl, ← hcr]
  iframe Him
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [hM] at hrest
  -- (auth-lease S3a §5) the window's table is the mode-`on` model's (empty in a cluster granting none)
  have hT : (if E.lg then appliedTableM (auth.AuthMode.on γa).isOn γr A else []) =
      kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) := by
    cases hlg : E.lg
    · have hl0 : γr.kv.lm = .none := hlm.trans (apply.AEnv.lm_of_lg_false hlg)
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hpre, List.nil_append, kvLeasesOn_none _ _ A (hl0 ▸ Hpl)]
    · simp only [↓reduceIte, auth.AuthMode.isOn, appliedTableM_true]
  rw [hT] at hrest
  obtain ⟨f, hf, hb⟩ := hrest
  refine ⟨by simp only []; omega, ⟨hci, hterm, ⟨f, ?_, fun n hn hna => ?_⟩, ?_⟩, ?_⟩
  · simpa [hpre] using hf
  · have h := hb n hn (by
      by_cases hc : membership.clusterBkts n
      · exact Or.inl hc
      · exact Or.inr ⟨hc, hna⟩)
    simpa [hpre] using h
  · rw [← hsa]; exact hau
  · exact hre

end proof

end EtcdGrove
end Perennial
