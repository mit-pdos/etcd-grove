/-
**The auth realization's per-backend invariant** (auth-schema-srv A6, 2026-11-18;
`notes/auth-schema-srv-handoff.md`, "A6 invariant, refined"). One invariant per backend `γc`, in the namespace
`authRealN` (disjoint from the backend's `rbClaimN` and from the store's `nroot.@"authRev"`), holding:
- **the buckets** (`bkCommon`, `bkIdle`): the claimed halves of the three auth buckets' readers' contents (`rbRd ½`), each a
  recorded state (`authStateAt`), the `auth` bucket the latest (`j_u, j_r ≤ j_a`), all no older than the
  realization's quarter of the published index; idle (the batch lock's share of the history, the claimed part,
  the batch token: every bucket at the history's last), in a batch (the write token deposited), or gone (after
  the retirement);
- **the life** (`realSt`): live (the succession right and the retired token, the two reader pools and the rest of
  the open share), retired (the write token and the publication quarter, the pools), released (the write token,
  the whole currency, the retired token; the pools' remains).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealPool
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSnapKit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClaimedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

/-! ## The buckets' encodings -/

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]

/-- The auth buckets, as a list (the claim's `Sc`). -/
def authBktL : List GoString := [go!"auth", go!"authUsers", go!"authRoles"]

/-- **The `auth` bucket `ca` holds the state `st`'s flag and revision**: what `unsafeReadAuthEnabled` and
`unsafeReadAuthRevision` read of it, and a revision of 8 bytes if any. Unlike `schema.authBucketsAre`, true of
the boot buckets (empty: disabled, revision `0`). -/
def authAt (st : auth.AuthState) (ca : BktData) : Prop :=
  schema.enabledOf ⟨ca, ∅, ∅⟩ = st.enabled ∧ uint.nat (schema.revisionOf ⟨ca, ∅, ∅⟩) = st.revision ∧
    schema.revWf ca

/-- **The auth buckets `D` hold the view `v`**: each bucket its state's. -/
def viewAt (v : auth.BkView) (D : schema.AuthData) : Prop :=
  authAt v.atAuth D.auth ∧ (∃ dU, schema.usersAt v.atUsers D.users dU) ∧
    (∃ dR, schema.rolesAt v.atRoles D.roles dR)

theorem enabledOf_auth (D : schema.AuthData) : schema.enabledOf D = schema.enabledOf ⟨D.auth, ∅, ∅⟩ := rfl
theorem revisionOf_auth (D : schema.AuthData) : schema.revisionOf D = schema.revisionOf ⟨D.auth, ∅, ∅⟩ := rfl

theorem viewAt_wf {v : auth.BkView} {D : schema.AuthData} (h : viewAt v D) : schema.authWf D := by
  obtain ⟨⟨-, -, hr⟩, ⟨dU, hu⟩, ⟨dR, hrl⟩⟩ := h
  exact ⟨schema.usersDec_wf (schema.usersAt_dec hu), schema.rolesDec_wf (schema.rolesAt_dec hrl), hr⟩

end pure

/-! ## The ghost names -/

/-- **The realization's names of one backend**: the store's (`γa`), the backend's auth names (`γc`), the
tickets' (`γt`), the ticket pool's (`γm`, `γh`), the reserved pool's (`γm'`, `γh'`) and the batch token's (`γk`). -/
structure RNames where
  γa : auth.AuthNames
  γc : auth.AuthBkNames
  γt : GName
  γm : GName
  γh : GName
  γm' : GName
  γh' : GName
  γk : GName

/-- The realization's invariants' namespace. -/
def authRealN : Namespace := nroot.@"authReal"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The reader slots' count of the ticket pool (one slot of the store's share is the reserved pool's). -/
def ticketN : Nat := authRdN - 1

/-- **What a reader of the ticket pool deposits** (its lent `L`): a share of the currency (the read contract's
first two clauses) or the write token (its third clause). -/
def depT (γ : RNames) : Option Qp → IProp GF
  | some q => auth.authCur γ.γc q
  | none => auth.authWTok γ.γc

/-- **The batch token** (exclusive): the idle and gone branches hold it, a batch's lock token holds it. -/
def batchTok (γ : RNames) : IProp GF := token γ.γk

/-- **The buckets idle**: the lock's share of a history `hs` whose last is every bucket's state, at its last
index; the claimed part at contents `rc` that the readers see; the batch token. -/
def bkIdle (γ : RNames) (d : mvcc.KBReal) (sa su sr : auth.AuthState) (ja ju jr : Nat)
    (cs : GoString → BktData) : IProp GF :=
  iprop(∃ (hs : List auth.AuthState) (rc : GMap GoString BktData), auth.authLockQ γ.γa hs ∗
    rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗ batchTok γ ∗
    ⌜hs.getLast? = some sa ∧ su = sa ∧ sr = sa ∧ ja = hs.length - 1 ∧ ju = ja ∧ jr = ja ∧
      ∀ n, n ∈ authBktL → bktOf rc n = cs n⌝)

/-- **The buckets' common part**: the readers' contents `cs` of the three buckets, their states `sa su sr`
recorded at `ja ju jr`, the realization's quarter of the published index at `p`. -/
def bkCommon (γ : RNames) (d : mvcc.KBReal) (cs : GoString → BktData) (sa su sr : auth.AuthState)
    (ja ju jr p : Nat) : IProp GF :=
  iprop(rbRd d.γB go!"auth" (1 : Qp).half (cs go!"auth") ∗
    rbRd d.γB go!"authUsers" (1 : Qp).half (cs go!"authUsers") ∗
    rbRd d.γB go!"authRoles" (1 : Qp).half (cs go!"authRoles") ∗
    auth.authStateAt γ.γa ja sa ∗ auth.authStateAt γ.γa ju su ∗ auth.authStateAt γ.γa jr sr ∗
    auth.authPubQ γ.γa (1 : Qp).half.half p ∗
    ⌜viewAt ⟨sa, su, sr⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩ ∧
      ju ≤ ja ∧ jr ≤ ja ∧ p ≤ ju ∧ p ≤ jr⌝)

/-- **The two reader pools** (`AuthRealPool`), each slot a reader slot of the backend with the share `s0` of
its open token: the ticket pool (`ticketN` slots, the tickets deposited, the readers' lent `depT`) and the
reserved pool (one slot, for the write token's reads: the write token deposited, nothing lent). -/
def pools (γ : RNames) (d : mvcc.KBReal) (s0 : Qp) : IProp GF :=
  iprop(poolSt γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) (rdTok d.γB d.P d.be) (bOpen d.γB s0) ticketN ∗
    poolSt γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (fun _ => iprop(True)) (rdTok d.γB d.P d.be)
      (bOpen d.γB s0) 1)

/-- **The pools after the release**: the held slots' receipts and tickets, the deposits' maps empty. -/
def poolsRel (γ : RNames) : IProp GF :=
  iprop(poolRel γ.γm γ.γh (ticketsIn γ.γt ticketN) ∗ poolRel γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)))

/-- **The realization's state of one backend** (see the file header): the buckets' common part and the life:
live (the succession right, the retired token, the pools, the rest `q0` of the open share; the buckets idle or
in a batch, the write token then deposited), retired (the publication quarter, the pools, the rest of the open
share; the buckets gone: the write token and the batch token kept) or released (the whole currency, the retired
token, the pools' remains; gone). -/
def realSt (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) : IProp GF :=
  iprop(∃ (cs : GoString → BktData) (sa su sr : auth.AuthState) (ja ju jr p : Nat),
    bkCommon γ d cs sa su sr ja ju jr p ∗
    ((auth.authSucc γ.γa ∗ auth.authRetired γ.γc ∗ pools γ d s0 ∗ bOpen d.γB q0 ∗
        (bkIdle γ d sa su sr ja ju jr cs ∨ auth.authWTok γ.γc)) ∨
      (auth.authPubTok γ.γa ∗ pools γ d s0 ∗ bOpen d.γB q0 ∗ auth.authWTok γ.γc ∗ batchTok γ) ∨
      (auth.authCur γ.γc 1 ∗ auth.authRetired γ.γc ∗ poolsRel γ ∗ auth.authWTok γ.γc ∗ batchTok γ)))

/-- **The realization's invariant of one backend.** -/
def realInv (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) : IProp GF :=
  iprop(inv authRealN (realSt γ d s0 q0))

instance realInv_persistent (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    Persistent (realInv (GF := GF) γ d s0 q0) := by
  unfold realInv; infer_instance

/-! ## The ticket pool's steps (the read contract's `Racq`, `Robs`, `Rrel`) -/

/-- **A ticket pool reader's receipt**: its deposit's entry, and the share lent the slot's. -/
def rcpt (γ : RNames) (s0 : Qp) (o : Option Qp) (qo : Qp) : IProp GF :=
  iprop(∃ k : Nat, ghostMapElem γ.γm k (DFrac.own 1) o ∗ ⌜qo = s0⌝)

theorem one_add_not_le (q : Qp) (h : (1 : Qp) + q ≤ 1) : False := by
  have h1 : (1 : Rat) + q.val ≤ 1 := h
  have := q.2
  grind

/-- A reader's deposit refutes the released backend (the whole currency and the write token). -/
theorem depT_released (γ : RNames) (o : Option Qp) :
    depT (GF := GF) γ o ∗ auth.authCur γ.γc 1 ∗ auth.authWTok γ.γc ⊢ False := by
  cases o with
  | some q =>
    simp only [depT, auth.authCur]
    iintro ⟨H1, H2, -⟩
    ihave %h := ghostVar_valid_2 _ _ _ _ _ $$ H2 H1
    exfalso; exact one_add_not_le q h.1
  | none =>
    simp only [depT, auth.authWTok]
    iintro ⟨H1, -, H2⟩
    iapply token_exclusive $$ H1 H2

/-- **`Racq`**: a ticket and the deposit for a reader slot, a share of the open token and the receipt. -/
theorem real_acq (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (o : Option Qp) :
    realInv (GF := GF) γ d s0 q0 ∗ ownToks γ.γt 1 ∗ depT γ o ∗ £ 1 ⊢
      |={⊤}=> ∃ qo : Qp, rdTok d.γB d.P d.be ∗ bOpen d.γB qo ∗ rcpt γ s0 o qo := by
  iintro ⟨#Hinv, Ht, Hd, Hlc⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d s0 q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hq, Hb⟩ | ⟨Hpt, Hp, Hq, HT, Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, Hbt⟩)
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_acq _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _ (ownToks γ.γt 1) ticketN
      (fun a => ticketsIn_dep γ.γt ticketN a) o $$ [$Hp1 $Ht $Hd] with ⟨Hp1, Htok, Hsh, %k, Hk⟩
    imod Hclose $$ [Hc Hs Hr Hp1 Hp2 Hq Hb]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      ileft
      iframe Hs Hr Hq Hb
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iexists s0
    iframe Htok Hsh
    iunfold rcpt
    iexists k
    iframe Hk
    ipureintro; rfl
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_acq _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _ (ownToks γ.γt 1) ticketN
      (fun a => ticketsIn_dep γ.γt ticketN a) o $$ [$Hp1 $Ht $Hd] with ⟨Hp1, Htok, Hsh, %k, Hk⟩
    imod Hclose $$ [Hc Hpt Hp1 Hp2 Hq HT Hbt]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      iright; ileft
      iframe Hpt Hq HT Hbt
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iexists s0
    iframe Htok Hsh
    iunfold rcpt
    iexists k
    iframe Hk
    ipureintro; rfl
  · iexfalso
    iapply depT_released γ o $$ [$Hd $Hcur $HT]

/-- The readers' contents of the auth buckets are the buckets' common part's (the read lock held). -/
theorem bkCommon_rv (γ : RNames) (d : mvcc.KBReal) (cs : GoString → BktData) (sa su sr : auth.AuthState)
    (ja ju jr p : Nat) (x : Loc) (rv : RView) :
    bkCommon (GF := GF) γ d cs sa su sr ja ju jr p ∗ rtHeld d.γB d.P d.be x rv ⊢
      bkCommon γ d cs sa su sr ja ju jr p ∗ rtHeld d.γB d.P d.be x rv ∗
      ⌜schema.rvAuth d.P rv = ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩⌝ := by
  iintro ⟨Hc, Hh⟩
  iunfold bkCommon at Hc
  icases Hc with ⟨Ha, Hu, Hr, #Hsa, #Hsu, #Hsr, Hp, %Hv⟩
  rw [rtHeld_eq]
  icases rtHeldF_rbRd d.γB d.P d.be x rv _ go!"auth" _ _ $$ [$Hh $Ha] with ⟨Hh, Ha, %h1⟩
  icases rtHeldF_rbRd d.γB d.P d.be x rv _ go!"authUsers" _ _ $$ [$Hh $Hu] with ⟨Hh, Hu, %h2⟩
  icases rtHeldF_rbRd d.γB d.P d.be x rv _ go!"authRoles" _ _ $$ [$Hh $Hr] with ⟨Hh, Hr, %h3⟩
  iframe Hh
  isplitl [Ha Hu Hr Hp]
  · iunfold bkCommon; iframe Ha Hu Hr Hp; iframe #; ipureintro; exact Hv
  ipureintro
  unfold schema.rvAuth
  simp only [mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI,
    go_etcd_io.etcd.server.v3.storage.schema.authName, go_etcd_io.etcd.server.v3.storage.schema.authUsersName,
    go_etcd_io.etcd.server.v3.storage.schema.authRolesName]
  rw [h1, h2, h3]

/-- **`Robs`**: with the read lock held, the receipt and the slot's share back for the deposit and a held
slot's receipt; the buckets read are well formed. -/
theorem real_obs (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (o : Option Qp) (x : Loc) (rv : RView) (qo : Qp) :
    realInv (GF := GF) γ d s0 q0 ∗ rtHeld d.γB d.P d.be x rv ∗ bOpen d.γB qo ∗ rcpt γ s0 o qo ∗ £ 1 ⊢
      |={⊤}=> rtHeld d.γB d.P d.be x rv ∗ depT γ o ∗ ownToks γ.γh 1 ∗ ⌜schema.authWf (schema.rvAuth d.P rv)⌝ := by
  iintro ⟨#Hinv, Hh, Ho, Hrc, Hlc⟩
  iunfold rcpt at Hrc
  icases Hrc with ⟨%k, Hk, %hq⟩
  subst hq
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d qo q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases bkCommon_rv γ d cs sa su sr ja ju jr p x rv $$ [$Hc $Hh] with ⟨Hc, Hh, %Hrv⟩
  ihave %Hwf : ⌜schema.authWf (schema.rvAuth d.P rv)⌝ $$ [Hc]
  · iunfold bkCommon at Hc
    icases Hc with ⟨-, -, -, -, -, -, -, %Hv⟩
    ipureintro; rw [Hrv]; exact viewAt_wf Hv.1
  icases Hl with (⟨Hs, Hr, Hp, Hq, Hb⟩ | ⟨Hpt, Hp, Hq, HT, Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, Hbt⟩)
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_obs _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _ ticketN k o $$ [$Hp1 $Hk $Ho]
      with ⟨Hp1, Hd, Hy⟩
    imod Hclose $$ [Hc Hs Hr Hp1 Hp2 Hq Hb]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      ileft
      iframe Hs Hr Hq Hb
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iframe Hh Hd Hy
    ipureintro; exact Hwf
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_obs _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _ ticketN k o $$ [$Hp1 $Hk $Ho]
      with ⟨Hp1, Hd, Hy⟩
    imod Hclose $$ [Hc Hpt Hp1 Hp2 Hq HT Hbt]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      iright; ileft
      iframe Hpt Hq HT Hbt
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iframe Hh Hd Hy
    ipureintro; exact Hwf
  · iunfold poolsRel at Hpr
    icases Hpr with ⟨Hpr1, -⟩
    iexfalso
    iapply poolRel_noRcpt γ.γm γ.γh (ticketsIn γ.γt ticketN) k o $$ [$Hpr1 $Hk]

/-- **`Rrel`**: the slot and the held slot's receipt back for a ticket (after the release, the slot is dropped). -/
theorem real_rel (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    realInv (GF := GF) γ d s0 q0 ∗ rdTok d.γB d.P d.be ∗ ownToks γ.γh 1 ∗ £ 1 ⊢ |={⊤}=> ownToks γ.γt 1 := by
  iintro ⟨#Hinv, Htok, Hy, Hlc⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d s0 q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hq, Hb⟩ | ⟨Hpt, Hp, Hq, HT, Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, Hbt⟩)
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_rel _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _ (ownToks γ.γt 1) ticketN
      (fun a => ticketsIn_wd γ.γt ticketN a) $$ [$Hp1 $Hy $Htok] with ⟨Hp1, HR⟩
    imod Hclose $$ [Hc Hs Hr Hp1 Hp2 Hq Hb]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      ileft
      iframe Hs Hr Hq Hb
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iexact HR
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_rel _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _ (ownToks γ.γt 1) ticketN
      (fun a => ticketsIn_wd γ.γt ticketN a) $$ [$Hp1 $Hy $Htok] with ⟨Hp1, HR⟩
    imod Hclose $$ [Hc Hpt Hp1 Hp2 Hq HT Hbt]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      iright; ileft
      iframe Hpt Hq HT Hbt
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iexact HR
  · iunfold poolsRel at Hpr
    icases Hpr with ⟨Hpr1, Hpr2⟩
    imod poolRel_rel _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (ownToks γ.γt 1)
      (fun a => ticketsIn_wd γ.γt ticketN a) $$ [$Hpr1 $Hy] with ⟨Hpr1, HR⟩
    imod Hclose $$ [Hc Hcur Hr Hpr1 Hpr2 HT Hbt]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      iright; iright
      iframe Hcur Hr HT Hbt
      iunfold poolsRel
      iframe Hpr1 Hpr2
    imodintro
    iexact HR

/-! ## Real reads' views (after schema's `RLock`) -/

/-- **The view of a held read**: the buckets read hold a view of recorded states, each no older than any
published lower bound `i`, the `auth` bucket's the latest. -/
theorem real_view (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (Y : RView → IProp GF) (x : Loc)
    (D : schema.AuthData) (i : Nat) :
    realInv (GF := GF) γ d s0 q0 ∗ schema.heldR d.γB d.P d.be Y x D ∗ auth.authPubLb γ.γa i ∗ £ 1 ⊢
      |={⊤}=> schema.heldR d.γB d.P d.be Y x D ∗
        ∃ v : auth.BkView, ⌜viewAt v D⌝ ∗ auth.authViewSnapFrom (.on γ.γa) i v := by
  iintro ⟨#Hinv, Hh, #Hlb, Hlc⟩
  iunfold schema.heldR at Hh
  icases Hh with ⟨%rv, %Hrv, Hh, HY⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d s0 q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases bkCommon_rv γ d cs sa su sr ja ju jr p x rv $$ [$Hc $Hh] with ⟨Hc, Hh, %Hcs⟩
  iunfold bkCommon at Hc
  icases Hc with ⟨Ha, Hu, Hr, #Hsa, #Hsu, #Hsr, Hp, %Hv⟩
  iunfold auth.authPubQ at Hp
  iunfold auth.authPubLb at Hlb
  ihave %Hip := monoNatLbOwn_valid γ.γa.pub _ p i $$ Hp Hlb
  imod Hclose $$ [Ha Hu Hr Hp Hl]
  · inext
    iunfold realSt
    iexists cs, sa, su, sr, ja, ju, jr, p
    iframe Hl
    iunfold bkCommon
    iframe Ha Hu Hr; iframe #
    isplitl [Hp]
    · iunfold auth.authPubQ; iexact Hp
    ipureintro; exact Hv
  imodintro
  isplitl [Hh HY]
  · iunfold schema.heldR
    iexists rv
    iframe Hh HY
    ipureintro; exact Hrv
  iexists ⟨sa, su, sr⟩
  isplitr
  · ipureintro
    rw [← Hrv.1, Hcs]
    exact Hv.1
  simp only [auth.authViewSnapFrom]
  iexists ja, ju, jr
  iframe #
  ipureintro
  obtain ⟨-, h1, h2, h3, h4⟩ := Hv
  exact ⟨by omega, by omega, h1, h2⟩

/-- **The view of a held read with the write token and the history's half**: no batch is open, so every
bucket is at the history's last state. -/
theorem real_viewIdle (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (Y : RView → IProp GF) (x : Loc)
    (D : schema.AuthData) (hs : List auth.AuthState) :
    realInv (GF := GF) γ d s0 q0 ∗ schema.heldR d.γB d.P d.be Y x D ∗ auth.authWTok γ.γc ∗
      auth.authHistHalf γ.γa hs ∗ £ 1 ⊢
      |={⊤}=> schema.heldR d.γB d.P d.be Y x D ∗ auth.authWTok γ.γc ∗ auth.authHistHalf γ.γa hs ∗
        ∃ st : auth.AuthState, ⌜viewAt (auth.BkView.uni st) D ∧ hs.getLast? = some st⌝ ∗
          auth.authSnap (.on γ.γa) st := by
  iintro ⟨#Hinv, Hh, HT, Hhh, Hlc⟩
  iunfold schema.heldR at Hh
  icases Hh with ⟨%rv, %Hrv, Hh, HY⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d s0 q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases bkCommon_rv γ d cs sa su sr ja ju jr p x rv $$ [$Hc $Hh] with ⟨Hc, Hh, %Hcs⟩
  icases Hl with (⟨Hs, Hr, Hp, Hq, Hb⟩ | ⟨Hpt, Hp, Hq, HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, HT', Hbt⟩)
  · icases Hb with (Hid | HT')
    · iunfold bkIdle at Hid
      icases Hid with ⟨%hs', %rc, Hlq, Hro, Hbt, %Hid⟩
      ihave %Heq := auth.authHistHalf_lockQ_agree γ.γa hs hs' $$ Hhh Hlq
      subst Heq
      obtain ⟨hl, hu, hr, -, -, -, -⟩ := id Hid
      iunfold bkCommon at Hc
      icases Hc with ⟨Ha, Hu, Hr', #Hsa, #Hsu, #Hsr, Hp', %Hv⟩
      imod Hclose $$ [Ha Hu Hr' Hp' Hs Hr Hp Hq Hlq Hro Hbt]
      · inext
        iunfold realSt
        iexists cs, sa, su, sr, ja, ju, jr, p
        isplitl [Ha Hu Hr' Hp']
        · iunfold bkCommon; iframe Ha Hu Hr' Hp'; iframe #; ipureintro; exact Hv
        ileft
        iframe Hs Hr Hp Hq
        ileft
        iunfold bkIdle
        iexists hs, rc
        iframe Hlq Hro Hbt
        ipureintro; exact Hid
      imodintro
      iframe HT Hhh
      isplitl [Hh HY]
      · iunfold schema.heldR; iexists rv; iframe Hh HY; ipureintro; exact Hrv
      iexists sa
      isplitr
      · ipureintro
        refine ⟨?_, hl⟩
        rw [← Hrv.1, Hcs]
        have h := Hv.1
        rw [hu, hr] at h
        exact h
      simp only [auth.authSnap]
      iexists ja
      iexact Hsa
    · iunfold auth.authWTok at HT HT'
      iexfalso
      iapply token_exclusive $$ HT HT'
  · iunfold auth.authWTok at HT HT'
    iexfalso
    iapply token_exclusive $$ HT HT'
  · iunfold auth.authWTok at HT HT'
    iexfalso
    iapply token_exclusive $$ HT HT'

/-! ## The users' walk at a state -/

/-- The walk's messages, each a user of the state (`userOutD_are` per entry). -/
theorem zip_userOut (st : auth.AuthState) (m : BktData) (dU : GoString → auth.UserRec)
    (h : schema.usersAt st m dU) :
    ∀ (us : List Loc) (es : List Ent), (∀ e ∈ es, m.lookup e.1 = some e.2) →
      ([∗list] x ∈ us.zip es, auth.ownUser (GF := GF) x.1 (dU x.2.1)) ⊢
        [∗list] x ∈ us.zip (es.map Prod.fst), auth.userOut x.1 st x.2
  | [], es, _ => by
    simp only [List.zip_nil_left]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | u :: us, [], _ => by
    simp only [List.map_nil, List.zip_nil_right]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | u :: us, e :: es, he => by
    simp only [List.zip_cons_cons, List.map_cons]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · have hl : m.lookup e.1 = some e.2 := he e (List.mem_cons_self ..)
      iapply schema.userOutD_are st m u e.1 dU h
      unfold schema.userOutD
      rw [hl]
      iexact H1
    · iapply zip_userOut st m dU h us es (fun e' he' => he e' (List.mem_cons_of_mem _ he')) $$ H

/-- **The users' walk at a state** (`unsafeGetAllUsers` of a users bucket holding `st` with the records
`dU`): the state's users (`auth.usersOut`). -/
theorem usersOutD_at (st : auth.AuthState) (m : BktData) (dU : GoString → auth.UserRec) (s : GoSlice)
    (h : schema.usersAt st m dU) :
    schema.usersOutD (GF := GF) s m dU ⊢ auth.usersOut s st := by
  iintro H
  iunfold schema.usersOutD at H
  icases H with ⟨%us, %es, Hs, %Hp, Hl⟩
  have hmem : ∀ e ∈ es, m.lookup e.1 = some e.2 := fun e he =>
    (schema.mem_bktEnts_iff m e.1 e.2).1 (Hp.1.mem_iff.1 he)
  iunfold auth.usersOut
  iexists us, es.map Prod.fst
  iframe Hs
  isplitr
  · ipureintro
    refine ⟨by rw [List.length_map]; exact Hp.2, ?_, ?_⟩
    · exact (Hp.1.map Prod.fst).nodup_iff.2 (schema.sorted_keys_nodup (bktEnts_sorted m))
    · intro n
      rw [← h.1 n, List.mem_map]
      constructor
      · rintro ⟨e, he, rfl⟩; rw [hmem e he]; rfl
      · intro hs
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
        exact ⟨(n, v), Hp.1.mem_iff.2 ((schema.mem_bktEnts_iff m n v).2 hv), rfl⟩
  iapply zip_userOut st m dU h us es hmem $$ Hl

end defs

end authReal
end EtcdGrove
end Perennial
