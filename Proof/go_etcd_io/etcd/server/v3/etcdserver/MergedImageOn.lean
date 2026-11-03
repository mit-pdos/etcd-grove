/-
**The merged snapshot's image with auth on** (#7-on, 2026-11-03): `merged_image`'s mode-on twin.
The window's observation (`mergedCreate_window` with the auth row's lend of the auth buckets,
`srvAuthApplyResB_lend`) gives every clause of `imageAtOn` but the KV log's: the `Key` bucket and
the records at the store's mode (off with auth on: `srvKVInvsOn`), the rest buckets but the auth ones
(`bkRestAtM`), and the auth buckets at the latest auth state, which the applied log determines
(`kvAppliedOn`). Lean-first (no Rocq counterpart).
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

/-- **A mode-on entry changes no lease table** (`kvTable_plainM`'s twin: an auth-on log's entries are
plain KV requests or auth admin ones, none a lease's). -/
theorem kvTable_plainOn (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel)
    (hp : plainEntryOn m) : kvTable c₀ ch lt m = lt := by
  unfold kvTable
  split
  · rename_i ht
    split
    · rfl
    · rename_i hd
      split
      · rename_i rq hdec
        unfold dispatchTable
        split
        · rfl
        · rcases hp ht hd rq hdec with h | ⟨hk, -⟩
          · exact chainTable_plain rq lt h.1.1 ch
          · refine chainTable_nonwrite rq lt (fun hw => ?_) ch
            unfold apply.adminKindOk at hk
            rcases hw with hw | hw | hw | hw | hw <;> simp [hw] at hk
      · rfl
  · rfl

/-- **A mode-on log grants no lease** (`kvTableOf_plainM`'s twin). -/
theorem kvTableOf_plainOn (c₀ : w64) (ch : apply.Chain) (A : List EntryModel)
    (hp : plainLogOn A) : ∀ lt, kvTableOf c₀ ch lt A = lt := by
  induction A with
  | nil => intro lt; rfl
  | cons m A ih =>
    intro lt
    show kvTableOf c₀ ch (kvTable c₀ ch lt m) A = lt
    rw [kvTable_plainOn c₀ ch lt m (hp m (List.mem_cons_self ..))]
    exact ih (fun m' hm' => hp m' (List.mem_cons_of_mem _ hm')) lt

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
`srvNet`'s `img`, which the cluster's mode makes `srvImageOn`): an observation `mergedObsM` at the
applied index `ai` of the applied log `A` (`kvAppliedOn`: the KV log and the auth state `sa` the
mode-on model's), with the auth buckets at `sa` (the lent part's), of a server with auth on and the
KV's start values. The `Key` bucket and the records: the store's mode is off (`srvKVInvsOn`), so the
image is the whole bucket and no record, which `imageAtOn`'s mode (the KV names') reads either way,
and a mode-on log compacts nothing (`crevOf_plainOn`). -/
theorem merged_imageOn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γa : auth.AuthNames) (ai : w64)
    (A : List EntryModel) (x : apply.ApplyKV) (sa : auth.AuthState) (D : backend.Data)
    (hM : E.authMode = .on γa) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) :
    ⌜mergedObsM E.authMode γr E.cmp E.lg ai A x.log x.crev D ∧ authBucketsAt sa D⌝ ∗
      ⧖ (mvcc.logCh x.log) ∗ isServerM true s γ ci TM E ρ γr ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ⊢
      |={⊤}=> kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗
        □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  iintro ⟨%hobs, #Hrc, #Hsrv, Hka⟩
  obtain ⟨⟨⟨r, hkI, -⟩, hci, hterm, ⟨f, hrest⟩, hwf⟩, hau⟩ := hobs
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomicsM at Hat
  icases Hat with ⟨-, -, Hki⟩
  ihave #Hinvs := srvKVInvsM_true s E γr $$ Hki
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, -, #HrI, -, -, -, %Hcmlg⟩
  have Hcm := Hcmlg.1
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ HrI
  imod (kvInvOn_ch0 γr.raft γr.kv srvAuthSt0) $$ HkI with %hch
  imod (kvInvOn_authOn γr.raft γr.kv srvAuthSt0) $$ HkI with %hao
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨Hal, %Hch'⟩
  iunfold kvAppliedLOn at Hal
  icases Hal with ⟨#HA, Hhi, Hc, %Hl⟩
  imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A $$ HkI HrI HA with %Hpl
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
  iexists γr.kv
  isplitr
  · ipureintro; exact ⟨h0.1, hch, h0.2⟩
  iunfold dbImageOn
  iexists A
  iframe HA'
  rw [← hxl]
  iframe Hrc
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [Hcm] at hkI
  rw [hxl] at hkI hwf
  obtain ⟨-, hr0⟩ := (mvcc.keyImageM_off _ _ D).1 hkI
  rw [hM] at hrest
  have hT : (if E.lg then (kvLeases γr.kv (γr.raft.pre ++ A)).ids else []) = [] := by
    split
    · unfold kvLeases; rw [hpre, List.nil_append, kvTableOf_plainOn _ _ A Hpl]; rfl
    · rfl
  rw [hT] at hrest
  refine ⟨by simp only []; omega, ⟨r, ?_, ?_⟩, hci, hterm, ?_, ?_, hwf⟩
  · cases hk : γr.kv.cmp
    · exact hkI
    · exact mvcc.keyImageM_on_of_off _ _ _ hkI
  · rw [hr0, mvcc.CmpRecs.crev_empty, crevOf_plainOn γr.kv A Hpl]
  · intro n hn hna
    have h := hrest n hn (by
      by_cases hc : membership.clusterBkts n
      · exact Or.inl hc
      · exact Or.inr ⟨hc, hna⟩)
    simpa [hpre, apply.restLeasesWith_nil, bkRestOf] using h
  · rw [← hsa]; exact hau

end proof

end EtcdGrove
end Perennial
