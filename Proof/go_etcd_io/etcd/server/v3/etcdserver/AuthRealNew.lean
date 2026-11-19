/-
**The auth realization's creation** (auth-schema-srv A6 (e), 2026-11-19): the per-backend invariant
(`AuthRealInv.lean`) allocated from what `authSchemaSrv`'s boot premise and `authSchemaSnap`'s premise hand the
realization: the auth buckets' idle part and claim tokens (claimed for good, `rbOwnIn_claim`), the store's share of
the reader slots and the open share `authOpenQ` (split into the two pools' slots and the rest `q0`), the lock's
share of the history at its last state (the buckets' state), and the publication share (`liveP`: at boot a
quarter of the premise's half and a fresh live token; at a snapshot the store's vault's, for the succession right,
V-pub). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealWr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

section create
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-! ## Replicated resources -/

theorem rep_zip (P Q : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), P) ∗ ([∗list] _x ∈ List.replicate n (), Q) ⊢
      [∗list] _x ∈ List.replicate n (), iprop(P ∗ Q) := by
  induction n with
  | zero => iintro -; iapply rep_zero
  | succ n ih =>
    iintro ⟨HP, HQ⟩
    icases (rep_succ P n).1 $$ HP with ⟨Hp, HP⟩
    icases (rep_succ Q n).1 $$ HQ with ⟨Hq, HQ⟩
    iapply (rep_succ _ n).2
    iframe Hp Hq
    iapply ih $$ [$HP $HQ]

theorem rep_split (P : IProp GF) (a b : Nat) :
    ([∗list] _x ∈ List.replicate (a + b) (), P) ⊢
      ([∗list] _x ∈ List.replicate a (), P) ∗ ([∗list] _x ∈ List.replicate b (), P) := by
  induction a with
  | zero =>
    simp only [Nat.zero_add]
    iintro H
    iframe H
    iapply rep_zero
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    iintro H
    icases (rep_succ P (a + b)).1 $$ H with ⟨Hx, H⟩
    icases ih $$ H with ⟨Ha, Hb⟩
    iframe Hb
    iapply (rep_succ P a).2
    iframe Hx Ha

/-! ## The history -/

/-- The lock's share of the history keeps a recorded state of it. -/
theorem lockQ_stateAt_keep (γa : auth.AuthNames) (hs : List auth.AuthState) (i : Nat) (st : auth.AuthState)
    (h : hs[i]? = some st) :
    auth.authLockQ (GF := GF) γa hs ⊢ auth.authLockQ γa hs ∗ auth.authStateAt γa i st := by
  unfold auth.authLockQ auth.authStateAt
  iintro ⟨H, %Hk⟩
  ihave #Hlb := monoListLbOwn_get γa.hist _ hs $$ H
  iframe H
  isplitr
  · ipureintro; exact Hk
  isplitl []
  · iapply (monoListIdxOwn_get i st h) $$ Hlb
  · ipureintro; exact Hk st (List.mem_of_getElem? h)

/-- A recorded state is in the lock's share of the history. -/
theorem lockQ_lookup (γa : auth.AuthNames) (hs : List auth.AuthState) (j : Nat) (s : auth.AuthState) :
    auth.authLockQ (GF := GF) γa hs ∗ auth.authStateAt γa j s ⊢
      auth.authLockQ γa hs ∗ ⌜hs[j]? = some s⌝ := by
  unfold auth.authLockQ auth.authStateAt
  iintro ⟨⟨H, %Hk⟩, ⟨Hi, -⟩⟩
  ihave %h := mono_list_auth_idx_lookup γa.hist _ hs j s $$ H Hi
  iframe H
  ipureintro; exact ⟨Hk, h⟩

theorem getLast_idx {hs : List auth.AuthState} {st : auth.AuthState} (h : hs.getLast? = some st) :
    hs[hs.length - 1]? = some st := by
  rw [List.getLast?_eq_getElem?] at h; exact h

theorem getLast_len {hs : List auth.AuthState} {st : auth.AuthState} (h : hs.getLast? = some st) :
    1 ≤ hs.length := by
  cases hs with
  | nil => simp at h
  | cons _ _ => simp

/-! ## The buckets of a snapshot -/

/-- **Buckets holding a state are at its view** (the converse of `viewAt_bucketsAre`, for `authSchemaSnap`'s
`authBucketsAt`): each user's and role's record chosen from the bucket's value. -/
theorem bucketsAre_viewAt {st : auth.AuthState} {D : schema.AuthData} (h : schema.authBucketsAre st D)
    (h64 : st.revision < 2 ^ 64) : viewAt ⟨st, st, st⟩ D := by
  classical
  obtain ⟨hwf, hen, hrev, hu1, hu2, hr1, hr2⟩ := h
  refine ⟨⟨(enabledOf_auth D).symm.trans hen, ?_, hwf.2.2⟩, ?_, ?_⟩
  · have e : schema.revisionOf ⟨D.auth, ∅, ∅⟩ = W64 st.revision := by
      simp only [schema.revisionOf]; rw [hrev]; exact beToU64_u64Be _
    dsimp only
    rw [e]; word
  · refine ⟨fun n => if hn : ∃ v, D.users.lookup n = some v then Classical.choose (hu2 n _ hn.choose_spec)
      else default, hu1, fun n v hl => ?_⟩
    have hn : ∃ v, D.users.lookup n = some v := ⟨v, hl⟩
    simp only [dif_pos hn]
    have hc := Classical.choose_spec (hu2 n _ hn.choose_spec)
    have hv : hn.choose = v := Option.some.inj (hn.choose_spec.symm.trans hl)
    rw [← hv]
    exact hc
  · refine ⟨fun n => if hn : ∃ v, D.roles.lookup n = some v then Classical.choose (hr2 n _ hn.choose_spec)
      else default, hr1, fun n v hl => ?_⟩
    have hn : ∃ v, D.roles.lookup n = some v := ⟨v, hl⟩
    simp only [dif_pos hn]
    have hc := Classical.choose_spec (hr2 n _ hn.choose_spec)
    have hv : hn.choose = v := Option.some.inj (hn.choose_spec.symm.trans hl)
    rw [← hv]
    exact hc

/-- `authBucketsAt` of the buckets `r` is the view of their auth buckets. -/
theorem bucketsAt_viewAt {st : auth.AuthState} {r : GMap GoString BktData} (h : authBucketsAt st r) :
    viewAt ⟨st, st, st⟩ ⟨bktOf r go!"auth", bktOf r go!"authUsers", bktOf r go!"authRoles"⟩ :=
  bucketsAre_viewAt h.1 h.2

/-! ## The publication vault (V-pub) -/

/-- **The vault at boot**: the succession right deposited, a fresh live token kept. -/
theorem vault_alloc (γa : auth.AuthNames) :
    auth.authSucc (GF := GF) γa ⊢ |={⊤}=> ∃ γv : GName, vaultInv γa γv ∗ token γv := by
  iintro Hs
  imod token_alloc (GF := GF) with ⟨%γv, Hlv⟩
  imod inv_alloc pubVN ⊤ (pubVault γa γv) $$ [Hs] with #Hvi
  · inext
    iunfold pubVault
    iright
    iexact Hs
  imodintro
  iexists γv
  iframe Hlv
  iunfold vaultInv
  iexact Hvi

/-- **The vault at a snapshot**: the succession right deposited for the publication quarter and the live token; the
quarter's index is below the history's length (the vault's recorded state). -/
theorem vault_take (γa : auth.AuthNames) (γv : GName) (hs : List auth.AuthState) :
    vaultInv (GF := GF) γa γv ∗ auth.authSucc γa ∗ auth.authLockQ γa hs ⊢
      |={⊤}=> ∃ p : Nat, auth.authPubQ γa (1 : Qp).half.half p ∗ token γv ∗ auth.authLockQ γa hs ∗
        ⌜p + 1 ≤ hs.length⌝ := by
  iintro ⟨#Hvi, Hs, Hlq⟩
  iunfold vaultInv at Hvi
  iinv Hvi with Hv Hvclose
  iunfold pubVault at Hv
  icases Hv with (⟨⟨%p, %j, %s, >Hpq, #Hsj, >%hpj⟩, >Hlv⟩ | >Hs')
  · ihave Hsj' := (show (▷ auth.authStateAt (GF := GF) γa j s) ⊢ ◇ auth.authStateAt γa j s by
      unfold auth.authStateAt; exact Iris.BI.Timeless.timeless) $$ Hsj
    imod Hsj' with #Hsj'
    icases lockQ_lookup γa hs j s $$ [$Hlq $Hsj'] with ⟨Hlq, %hj⟩
    imod Hvclose $$ [Hs] with -
    · inext
      iunfold pubVault
      iright
      iexact Hs
    imodintro
    iexists p
    iframe Hpq Hlv Hlq
    ipureintro
    have := (List.getElem?_eq_some_iff.1 hj).1
    omega
  · iexfalso
    iunfold auth.authSucc at Hs Hs'
    iapply token_exclusive $$ Hs Hs'

/-! ## The invariant -/

/-- The auth buckets as the list. -/
theorem authBkts_iff (n : GoString) : authBkts n ↔ n ∈ authBktL := by
  simp [authBkts, auth.authBkts, authBktL]

/-- **The realization's creation** (boot and snapshot): the claim, the pools, the backend's fresh names `γc`, the
batch and session tokens, and the invariant, live and idle at the history's last state `st`, whose encoding the
buckets `r` hold; the client gets the write token and the whole currency. -/
theorem real_create (γa : auth.AuthNames) (γt γv : GName) (d : mvcc.KBReal) (s0 q0 : Qp)
    (hq : authOpenQ = qpRep q0 s0 authRdN) (st : auth.AuthState) (hs : List auth.AuthState) (p : Nat)
    (r : GMap GoString BktData) (hl : hs.getLast? = some st) (hp : p + 1 ≤ hs.length)
    (hv : viewAt ⟨st, st, st⟩ ⟨bktOf r go!"auth", bktOf r go!"authUsers", bktOf r go!"authRoles"⟩)
    (hT : d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI) :
    ownTokAuthDfrac γt DFrac.discard ticketN ∗ auth.authPubQ γa (1 : Qp).half.half p ∗ token γv ∗
      bOpen d.γB authOpenQ ∗ authRdSlots d ∗ rbOwnIn d.γB authBkts r ∗ auth.authLockQ γa hs ⊢
      |={⊤}=> ∃ γ : RNames, ⌜γ.γa = γa ∧ γ.γt = γt ∧ γ.γv = γv⌝ ∗ realInv γ d s0 q0 ∗
        auth.authWTok γ.γc ∗ auth.authCur γ.γc 1 := by
  iintro ⟨#Ht, Hpq, Hlv, Hq, Hsl, Hro, Hlq⟩
  iunfold authRdSlots at Hsl
  icases Hsl with ⟨Hrd, Htk⟩
  -- the claim of the auth buckets
  ihave Hro := (rbOwnIn_set d.γB authBkts (fun n => n ∈ authBktL) r authBkts_iff).1 $$ Hro
  ihave Htk := (rbClaimToks_set d.γB d.P authBkts (fun n => n ∈ authBktL) authBkts_iff).1 $$ Htk
  have hS : ∀ n, n ∈ authBktL → (∃ i, d.P.BT.lookup n = some i) ∧ d.P.RB n = true := by
    intro n hn
    refine ⟨?_, rb_auth d n hn⟩
    simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨_, hT.1⟩
    · exact ⟨_, hT.2.1⟩
    · exact ⟨_, hT.2.2⟩
  imod rbOwnIn_claim d.γB d.P r ⊤ (fun _ _ => CoPset.mem_full) authBktL (by unfold authBktL; decide) hS
    $$ [$Hro $Htk] with ⟨Hro, Hrds⟩
  simp only [authBktL]
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Ha, Hrds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hu, Hrds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hr, -⟩
  -- the backend's names, the batch and session tokens
  imod token_alloc (GF := GF) with ⟨%γ1, HT⟩
  imod ghostVar_alloc (GF := GF) () with ⟨%γ2, Hcur⟩
  imod token_alloc (GF := GF) with ⟨%γ3, HR⟩
  imod ghostVar_alloc (GF := GF) (csT (fun n => bktOf r n)) with ⟨%γk, Hbt⟩
  imod ghostVar_alloc (GF := GF) (encW auth.AuthSess.init.users, encW auth.AuthSess.init.roles) with ⟨%γw, Hsw⟩
  -- the pools: the slots with the open share's parts
  rw [hq]
  icases (bOpen_rep d.γB q0 s0 authRdN).1 $$ Hq with ⟨Hq, Hss⟩
  iunfold rdAuth at Hrd
  ihave Hsl := rep_zip _ _ authRdN $$ [$Hrd $Hss]
  have hn : authRdN = ticketN + 1 := by unfold ticketN authRdN; omega
  rw [hn]
  icases rep_split _ ticketN 1 $$ Hsl with ⟨Hs1, Hs2⟩
  imod ownToks_0 (GF := GF) γt with Ht0
  imod pool_alloc ⊤ (ticketsIn γt ticketN)
      (depT ⟨γa, (γ1, γ2, γ3), γt, γt, γt, γt, γt, γk, γw, γv⟩) (rdTok d.γB d.P d.be) (bOpen d.γB s0) ticketN
    $$ [Ht0 $Hs1] with ⟨%γm, %γh, Hp1⟩
  · iunfold ticketsIn; iframe Ht Ht0
  imod pool_alloc ⊤ (tokIn (auth.authWTok (γ1, γ2, γ3))) (fun _ => iprop(True)) (rdTok d.γB d.P d.be)
      (bOpen d.γB s0) 1 $$ [$Hs2] with ⟨%γm', %γh', Hp2⟩
  · simp only [tokIn]; itrivial
  -- the invariant
  have hj := getLast_idx hl
  icases lockQ_stateAt_keep γa hs (hs.length - 1) st hj $$ Hlq with ⟨Hlq, #Hst⟩
  imod inv_alloc authRealN ⊤ (realSt ⟨γa, (γ1, γ2, γ3), γt, γm, γh, γm', γh', γk, γw, γv⟩ d s0 q0)
    $$ [Ha Hu Hr Hpq Hlv HR Hp1 Hp2 Hlq Hro Hbt Hsw Hq] with #Hinv
  · inext
    iunfold realSt
    iexists (fun n => bktOf r n), st, st, st, hs.length - 1, hs.length - 1, hs.length - 1, p
    isplitl [Ha Hu Hr]
    · iunfold bkCommon
      iframe Ha Hu Hr Hst
      ipureintro
      exact ⟨hv, Nat.le_refl _, Nat.le_refl _, by omega, by omega⟩
    ileft
    isplitl [Hpq Hlv]
    · iunfold liveP; iframe Hpq Hlv
    isplitl [HR]
    · iunfold auth.authRetired; iexact HR
    isplitl [Hp1 Hp2]
    · iunfold pools
      iframe Hp2
      iapply (show poolSt γm γh (ticketsIn γt ticketN)
          (depT ⟨γa, (γ1, γ2, γ3), γt, γt, γt, γt, γt, γk, γw, γv⟩) (rdTok d.γB d.P d.be) (bOpen d.γB s0) ticketN ⊢
        poolSt γm γh (ticketsIn γt ticketN)
          (depT ⟨γa, (γ1, γ2, γ3), γt, γm, γh, γm', γh', γk, γw, γv⟩) (rdTok d.γB d.P d.be) (bOpen d.γB s0) ticketN
        from .rfl) $$ Hp1
    ileft
    iunfold bkIdle
    iexists hs, r, auth.AuthSess.init
    iframe Hlq Hq
    isplitl [Hro]
    · iapply (show rbOwnInR (GF := GF) d.γB (fun k => k ∈ [go!"auth", go!"authUsers", go!"authRoles"]) r ⊢
        rbOwnInR d.γB (fun n => n ∈ authBktL) r from .rfl) $$ Hro
    isplitl [Hbt]
    · iunfold bkTok; iexact Hbt
    isplitl [Hsw]
    · iunfold bkSw; iexact Hsw
    ipureintro
    exact ⟨hl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  imodintro
  iexists ⟨γa, (γ1, γ2, γ3), γt, γm, γh, γm', γh', γk, γw, γv⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iunfold realInv
  iframe Hinv
  isplitl [HT]
  · iapply (show token (GF := GF) γ1 ⊢ auth.authWTok (γ1, γ2, γ3) from .rfl) $$ HT
  · iapply (show ghostVar (GF := GF) γ2 1 () ⊢ auth.authCur (γ1, γ2, γ3) 1 from .rfl) $$ Hcur

end create

end authReal
end EtcdGrove
end Perennial
