/-
**The server's auth component** (the auth-component refactor's stage 1, 2026-11-04; the statements
frozen by the user, 2026-11-04): the server's proofs reach auth through one slot, `AuthC` (off, or
on at the store's names), its sealed predicates and their laws, auth off being the slot's trivial
instance rather than a twin shape (`notes/decisions.md`, "The auth component").

* `AuthC`: `auth.AuthMode` without `.any`, which no server spec admits;
* sealed: `acRes` (the apply thread's auth part, today's `kvAuthM`), `acInv`, `acTok`, `acPub`,
  `acRead`, `acLessor`, `acCost`, `acSnapKit`, `acSnapOk`;
* public (pure, read outside the slot): `acBkts`, `acImg`, `acOpenQ`, `acModesOk`,
  `restSetC`;
* the laws: the bridges to today's mode-indexed names (stage 2 rewrites with them, then deletes
  them), the opening laws with auth on (`acRes_on`, ...: `srvEntryStep`'s on case, a departure
  from the slot rule until the one KV model, stage 3), the introductions (`NewServer`), and the
  laws the twin proofs take at their divergence points (token rights, publication, the merged
  snapshot's lend, the install's facts, the backend change, the reader side).

In stage 1 the environment keeps its `authMode`: the laws that read it take
`hC : E.authMode = C.mode`, which stage 2 (`AEnv.auth : AuthC`) makes definitional.
Nothing imports this module until stage 2. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyAuthM
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MergedImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- **The server's auth component**: off (the store's auth never enabled on this server), or on at
the store's ghost names `γa`. -/
inductive AuthC where
  | off
  | on (γa : auth.AuthNames)

/-- The auth package's contract mode of a component. -/
def AuthC.mode : AuthC → auth.AuthMode
  | .off => .off
  | .on γa => .on γa

def AuthC.isOn : AuthC → Bool
  | .off => false
  | .on _ => true

theorem AuthC.mode_isOn (C : AuthC) : C.mode.isOn = C.isOn := by
  cases C <;> rfl

section pure
variable [GooseExts]

/-- **The buckets the component owns**: none off; the auth store's on. -/
def acBkts : AuthC → GoString → Prop
  | .off => fun _ => False
  | .on _ => auth.authBkts

/-- **The component's buckets hold the auth state `st`**: nothing off; `authBucketsAt st` on. -/
def acImg : AuthC → auth.AuthState → GMap GoString backend.BktData → Prop
  | .off => fun _ _ => True
  | .on _ => authBucketsAt

/-- **The apply thread's share of a server backend's open token**: the half off; a quarter on,
the auth realization keeping the other quarter. -/
def acOpenQ : AuthC → Qp
  | .off => (1 : Qp).half
  | .on _ => (1 : Qp).half.half

/-- **The KV modes the component admits**: every one off; on, no compaction and no lease grant.
Stage 2's `srvKVInvsC` carries `⌜acModesOk C E.cmp γr.kv.lg⌝` (today `srvKVInvsOn`'s last
conjunct). -/
def acModesOk : AuthC → Bool → Bool → Prop
  | .off => fun _ _ => True
  | .on _ => fun cmp lg => cmp = false ∧ lg = false

/-- **The rest resource's buckets**: the tracked buckets neither the cluster's nor the
component's. -/
def restSetC (C : AuthC) (n : GoString) : Prop :=
  ¬ membership.clusterBkts n ∧ ¬ acBkts C n

theorem restSet_eq (C : AuthC) : restSet C.mode = restSetC C := by
  funext n
  cases C with
  | off => simp [restSet, restSetC, acBkts, AuthC.mode]
  | on γa => rfl

theorem srvOpenQ_eq (C : AuthC) : srvOpenQ C.mode = acOpenQ C := by
  cases C <;> rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply thread's auth part at the latest auth state `st`**, through the uber-applier `ua`:
off, the store's field (`srvAuthApplyRes`); on, the base applier's auth layer and the auth resource
at `st` on the current backend. -/
@[no_expose] def acRes (C : AuthC) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface)
    (st : auth.AuthState) : IProp GF :=
  match C with
  | .off => srvAuthApplyRes s E
  | .on _ => iprop(srvUberBase s ua E ∗ srvAuthApplyResB s E st)

/-- **The component's invariants** (persistent): nothing off; on, the store's history tied to the
committed log and the uber-applier's latest-state contracts. -/
@[no_expose] def acInv (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  match C with
  | .off => iprop(True)
  | .on _ => iprop(authHistTie E γr srvAuthSt0 ∗ srvUberOn s)

/-- **The rights to issue tokens at the consistent index `k`**: nothing off; on, the rights'
authority below an index at most `k`. -/
@[no_expose] def acTok (C : AuthC) (k : w64) : IProp GF :=
  match C with
  | .off => iprop(True)
  | .on γa => iprop(∃ n : Int, auth.freshBelow γa.fresh n ∗ ⌜n ≤ uint.Z k⌝)

/-- **A published index recording the auth state `st`** (persistent). -/
@[no_expose] def acPub (C : AuthC) (st : auth.AuthState) : IProp GF :=
  authPubAt C.mode st

/-- **The read side** (persistent): the store's lower-bound checks, and with auth on its request
side bound to the request context's token. -/
@[no_expose] def acRead (C : AuthC) (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  match C with
  | .off => srvAuthLb s E
  | .on _ => iprop(srvAuthLb s E ∗ srvAuthBound s E)

/-- **The lessor premise** (persistent): nothing off; on, the lessor finds no lease. -/
@[no_expose] def acLessor (C : AuthC) (s : Loc) : IProp GF :=
  srvLessorNilM C.isOn s

/-- **The time receipt an entry's application costs the component**: nothing off; one on. -/
@[no_expose] def acCost (C : AuthC) : IProp GF :=
  match C with
  | .off => iprop(True)
  | .on _ => iprop(⧗ 1)

/-- **The store `ast`'s contracts on any backend and the facts its `Recover` takes**
(persistent): off, `authRecoverOk`; on, the store's invariant and snapshot clause
(`authSnapKitM`). -/
@[no_expose] def acSnapKit (C : AuthC) (ast : Loc) (RD : IProp GF) : IProp GF :=
  match C with
  | .off => iprop(authApplyOkM .off ast RD ∗ authRecoverOk ast)
  | .on γa => iprop(authApplyOkM (.on γa) ast RD ∗ authSnapKitM (.on γa) ast RD)

/-- **`Recover`'s facts at the image's committed log `A'`** (persistent; today's `snapAuthResM`). -/
@[no_expose] def acSnapOk (C : AuthC) (s ast : Loc) (RD : IProp GF) (γr : ReadNames)
    (A' : List EntryModel) : IProp GF :=
  snapAuthResM C.mode s ast RD γr A'

instance acInv_persistent (C : AuthC) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (acInv (GF := GF) C s E γr) := by
  cases C <;> unfold acInv <;> infer_instance

instance acPub_persistent (C : AuthC) (st : auth.AuthState) :
    Persistent (acPub (GF := GF) C st) := by
  unfold acPub; infer_instance

instance acPub_timeless (C : AuthC) (st : auth.AuthState) :
    Timeless (acPub (GF := GF) C st) := by
  unfold acPub; infer_instance

instance acRead_persistent (C : AuthC) (s : Loc) (E : apply.AEnv GF) :
    Persistent (acRead (GF := GF) C s E) := by
  cases C <;> unfold acRead <;> infer_instance

instance acLessor_persistent (C : AuthC) (s : Loc) : Persistent (acLessor (GF := GF) C s) := by
  unfold acLessor; infer_instance

instance acSnapKit_persistent (C : AuthC) (ast : Loc) (RD : IProp GF) :
    Persistent (acSnapKit (GF := GF) C ast RD) := by
  cases C <;> unfold acSnapKit <;> infer_instance

instance acSnapOk_persistent (C : AuthC) (s ast : Loc) (RD : IProp GF) (γr : ReadNames)
    (A' : List EntryModel) : Persistent (acSnapOk (GF := GF) C s ast RD γr A') := by
  unfold acSnapOk; infer_instance

instance acCost_timeless (C : AuthC) : Timeless (acCost (GF := GF) C) := by
  cases C <;> unfold acCost <;> infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The window's side condition: the component's buckets are tracked rest buckets. -/
theorem acBkts_rest (C : AuthC) (n : GoString) (h : acBkts C n) : n ∈ mvcc.restBuckets := by
  cases C with
  | off => exact h.elim
  | on γa => exact authBkts_rest n h

/-! ### Bridges to today's mode-indexed names (stage 2 rewrites with them, then deletes them) -/

theorem kvAuthM_eq (C : AuthC) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface)
    (st : auth.AuthState) : kvAuthM C.isOn s E ua st = acRes C s E ua st := by
  cases C <;> rfl

theorem srvTokRights_eq (C : AuthC) (E : apply.AEnv GF) (k : w64) (hC : E.authMode = C.mode) :
    srvTokRights E k = acTok C k := by
  cases C <;> simp only [srvTokRights, acTok, hC, AuthC.mode]

theorem srvLessorNilM_eq (C : AuthC) (s : Loc) : srvLessorNilM (GF := GF) C.isOn s = acLessor C s := by
  dsimp only [acLessor, AuthC.mode, AuthC.isOn]

theorem snapAuthResM_eq (C : AuthC) (s ast : Loc) (RD : IProp GF) (γr : ReadNames)
    (A' : List EntryModel) : snapAuthResM C.mode s ast RD γr A' = acSnapOk C s ast RD γr A' := by
  dsimp only [acSnapOk, AuthC.mode, AuthC.isOn]

theorem authPubAt_eq (C : AuthC) (st : auth.AuthState) :
    authPubAt (GF := GF) C.mode st = acPub C st := by
  dsimp only [acPub, AuthC.mode, AuthC.isOn]

/-- `srvSnapRO`'s auth conjuncts give the kit (stage 2 makes `srvSnapRO` carry `acSnapKit C`). -/
theorem acSnapKit_of (C : AuthC) (E : apply.AEnv GF) (ast : Loc) (RD : IProp GF)
    (hC : E.authMode = C.mode) :
    authApplyOkM E.authMode ast RD ∗ authSnapKitM E.authMode ast RD ∗
      □ (⌜E.authMode = .off⌝ → authRecoverOk ast) ⊢ acSnapKit (GF := GF) C ast RD := by
  rw [hC]
  cases C with
  | off =>
    dsimp only [acSnapKit, AuthC.mode, AuthC.isOn]
    iintro ⟨#Ha, -, #Hr⟩
    iframe Ha
    iapply Hr
    ipureintro; rfl
  | on γa =>
    dsimp only [acSnapKit, AuthC.mode, AuthC.isOn]
    iintro ⟨#Ha, #Hk, -⟩
    iframe Ha Hk

theorem acSnapKit_apply (C : AuthC) (ast : Loc) (RD : IProp GF) :
    acSnapKit (GF := GF) C ast RD ⊢ authApplyOkM C.mode ast RD := by
  cases C <;> dsimp only [acSnapKit, AuthC.mode, AuthC.isOn] <;> iintro ⟨#Ha, -⟩ <;> iexact Ha

/-! ### Opening, with auth on only (`srvEntryStep`'s on case; a departure until layer A) -/

theorem acRes_on (C : AuthC) (γa : auth.AuthNames) (hM : C = .on γa) (s : Loc)
    (E : apply.AEnv GF) (ua : GoInterface) (st : auth.AuthState) :
    acRes C s E ua st ⊣⊢ srvUberBase s ua E ∗ srvAuthApplyResB s E st := by
  subst hM; exact .rfl

theorem acInv_on (C : AuthC) (γa : auth.AuthNames) (hM : C = .on γa) (s : Loc)
    (E : apply.AEnv GF) (γr : ReadNames) :
    acInv C s E γr ⊣⊢ authHistTie E γr srvAuthSt0 ∗ srvUberOn s := by
  subst hM; exact .rfl

theorem acLessor_on (C : AuthC) (γa : auth.AuthNames) (hM : C = .on γa) (s : Loc) :
    acLessor (GF := GF) C s ⊣⊢ srvLessorNil s := by
  subst hM; exact .rfl

theorem acCost_on (C : AuthC) (γa : auth.AuthNames) (hM : C = .on γa) :
    acCost (GF := GF) C ⊣⊢ ⧗ 1 := by
  subst hM; exact .rfl

/-! ### Introduction (`NewServer` builds each piece from the store's kit in its mode) -/

theorem acTok_init (C : AuthC) (E : apply.AEnv GF) (k : w64) (hC : E.authMode = C.mode) :
    authFreshInit (GF := GF) E.authMode ⊢ acTok C k := by
  rw [← srvTokRights_eq C E k hC]
  exact srvTokRights_init E k

theorem acRes_off (s : Loc) (E : apply.AEnv GF) (ua : GoInterface) (st : auth.AuthState) :
    srvAuthApplyRes s E ⊢ acRes .off s E ua st :=
  .rfl

theorem acInv_off (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    ⊢ acInv (GF := GF) .off s E γr := by
  dsimp only [acInv, AuthC.mode, AuthC.isOn]; itrivial

theorem acLessor_off (s : Loc) : ⊢ acLessor (GF := GF) .off s := by
  dsimp only [acLessor, AuthC.mode, AuthC.isOn]; simp only [srvLessorNilM]; itrivial

/-- Off, the token rights are nothing (whatever the environment). -/
theorem acTok_off (k : w64) : acTok (GF := GF) .off k = iprop(True) := by
  dsimp only [acTok]

theorem acCost_off : ⊢ acCost (GF := GF) .off := by
  dsimp only [acCost, AuthC.mode, AuthC.isOn]; itrivial

/-- One proof takes the entry's receipt in both modes; off discards it. -/
theorem acCost_of (C : AuthC) : ⧗ 1 ⊢ acCost (GF := GF) C := by
  cases C with
  | off => dsimp only [acCost, AuthC.mode, AuthC.isOn]; iintro -; itrivial
  | on γa => dsimp only [acCost, AuthC.mode, AuthC.isOn]; iintro H; iexact H

/-! ### Token rights -/

theorem acTok_mono (C : AuthC) (k k' : w64) (h : uint.Z k ≤ uint.Z k') :
    acTok (GF := GF) C k ⊢ acTok C k' := by
  cases C with
  | off => dsimp only [acTok, AuthC.mode, AuthC.isOn]; iintro -; itrivial
  | on γa =>
    dsimp only [acTok, AuthC.mode, AuthC.isOn]
    iintro ⟨%n, H, %Hn⟩
    iexists n
    iframe H
    ipureintro; omega

/-- **Mint an `Authenticate` token's right** at the consistent index `x` it reads, the rights
moving to `k > x`. -/
theorem acTok_mint (C : AuthC) (γa : auth.AuthNames) (hM : C = .on γa) (x k : w64)
    (h : uint.Z x < uint.Z k) (pre : GoString) :
    acTok (GF := GF) C x ⊢ |==> (acTok C k ∗ auth.tokFresh γa (auth.simpleTok pre x)) := by
  subst hM
  dsimp only [acTok, AuthC.mode, AuthC.isOn]
  iintro ⟨%n, Hf, %hn⟩
  imod auth.freshBelow_mint (GF := GF) γa.fresh n x pre hn $$ Hf with ⟨Hf, Ht⟩
  imodintro
  isplitl [Hf]
  · iexists (uint.Z x + 1)
    iframe Hf
    ipureintro; omega
  iunfold auth.tokFresh
  iexact Ht

/-! ### Publication -/

theorem acRes_publish (C : AuthC) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface)
    (st : auth.AuthState) (hC : E.authMode = C.mode) :
    acRes C s E ua st ={⊤}=∗ acRes C s E ua st ∗ acPub C st := by
  cases C with
  | off =>
    dsimp only [acPub, AuthC.mode, AuthC.isOn]
    iintro H
    imodintro
    iframe H
    simp only [authPubAt]
    itrivial
  | on γa =>
    simp only [AuthC.mode] at hC
    dsimp only [acRes, acPub, AuthC.mode, AuthC.isOn]
    iintro ⟨#Hb, HR⟩
    imod srvAuthApplyResB_publish s ua E γa st hC $$ Hb HR with ⟨HR, #Hp⟩
    imodintro
    iframe HR
    isplitr
    · iexact Hb
    rw [hC]
    iexact Hp

/-! ### The merged snapshot's lend -/

theorem acRes_lend (C : AuthC) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface)
    (st : auth.AuthState) (hC : E.authMode = C.mode) :
    acRes C s E ua st ⊢ bkLendW E (acBkts C) (acImg C st) (acRes C s E ua st) := by
  cases C with
  | off =>
    simp only [acBkts, acImg]
    iintro H
    unfold bkLendW
    iintro %d %_
    imodintro
    iexists iprop(emp)
    isplitr
    · iempintro
    isplitr
    · iintro !> %r Hl Hr
      iframe Hl Hr
      ipureintro; exact ⟨∅, trivial, fun _ h => h.elim⟩
    iintro -
    imodintro
    iexact H
  | on γa =>
    simp only [acBkts, acImg]
    dsimp only [acRes, AuthC.mode, AuthC.isOn]
    iintro ⟨#Hb, HR⟩
    ihave HL := srvAuthApplyResB_lend s E st γa hC $$ HR
    unfold bkLendW
    iintro %d %hd
    imod HL $$ %d %hd with ⟨%RL, HRL, #Hlaw, Hback⟩
    imodintro
    iexists RL
    iframe HRL Hlaw
    iintro HRL
    imod Hback $$ HRL with HR
    imodintro
    iframe HR
    iexact Hb

/-! ### Snapshot install -/

theorem acSnapOk_intro (C : AuthC) (s ast : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (A' : List EntryModel) (hC : E.authMode = C.mode) :
    srvAuthStoreAddr s ↦□ auth.authIface ast ∗ acSnapKit C ast E.RD ∗ srvRLogLb γr.raft A' ⊢
      acSnapOk C s ast E.RD γr A' := by
  cases C with
  | off =>
    dsimp only [acSnapKit, acSnapOk, AuthC.mode, AuthC.isOn]
    iintro ⟨-, ⟨-, #Hr⟩, -⟩
    simp only [snapAuthResM]
    iexact Hr
  | on γa =>
    dsimp only [acSnapKit, acSnapOk, AuthC.mode, AuthC.isOn]
    iintro ⟨#Ha, ⟨-, #Hk⟩, #Hl⟩
    simp only [AuthC.mode] at hC
    have h := snapAuthResM_on s ast E γr A' γa hC
    rw [hC] at h
    iapply h
    iframe Ha Hk

/-! ### Backend change -/

theorem acRead_backend (C : AuthC) (s : Loc) {γ γ' : ApplyNames} {E E' : apply.AEnv GF}
    (h : beSucc γ E γ' E') : acRead C s E ⊢ acRead C s E' := by
  obtain ⟨-, p, P, f, c, RO, RW, rfl⟩ := h
  exact .rfl

theorem acInv_backend (C : AuthC) (s : Loc) (γr : ReadNames) {γ γ' : ApplyNames}
    {E E' : apply.AEnv GF} (h : beSucc γ E γ' E') : acInv C s E γr ⊢ acInv C s E' γr := by
  obtain ⟨-, p, P, f, c, RO, RW, rfl⟩ := h
  exact .rfl

/-! ### The reader side -/

theorem acRead_of_res (C : AuthC) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface)
    (st : auth.AuthState) (hC : E.authMode = C.mode) :
    acRes C s E ua st ⊢ acRead C s E := by
  cases C with
  | off =>
    unfold acRes acRead srvAuthApplyRes srvAuthLb
    iintro ⟨%stl, #Hf, -⟩
    iexists (auth.authIface stl)
    iframe Hf
    rw [hC]
    simp only [AuthC.mode, authStoreLbM]
    itrivial
  | on γa =>
    dsimp only [acRes, acRead, AuthC.mode, AuthC.isOn]
    iintro ⟨#Hb, -⟩
    isplitl
    · iapply srvAuthLb_of_uberBase s ua E $$ Hb
    · iapply srvAuthBound_of_uberBase s ua E (by rw [hC]; rfl) $$ Hb

/-- `acRead_of_res`, keeping the row (the auth component's 2c: `start` builds its views from the
row it hands the apply thread). -/
theorem acRes_read (C : AuthC) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface)
    (st : auth.AuthState) (hC : E.authMode = C.mode) :
    acRes C s E ua st ⊢ acRes C s E ua st ∗ acRead C s E := by
  cases C with
  | off =>
    unfold acRes acRead srvAuthApplyRes srvAuthLb
    iintro ⟨%stl, #Hf, H⟩
    isplitl
    · iexists stl; iframe Hf; iexact H
    iexists (auth.authIface stl)
    iframe Hf
    rw [hC]
    simp only [AuthC.mode, authStoreLbM]
    itrivial
  | on γa =>
    dsimp only [acRes, acRead, AuthC.mode, AuthC.isOn]
    iintro ⟨#Hb, HR⟩
    iframe Hb HR
    isplitl
    · iapply srvAuthLb_of_uberBase s ua E $$ Hb
    · iapply srvAuthBound_of_uberBase s ua E (by rw [hC]; rfl) $$ Hb

theorem acRead_lb (C : AuthC) (s : Loc) (E : apply.AEnv GF) :
    acRead C s E ⊢ srvAuthLb s E := by
  cases C with
  | off => dsimp only [acRead, AuthC.mode, AuthC.isOn]; iintro H; iexact H
  | on γa => dsimp only [acRead, AuthC.mode, AuthC.isOn]; iintro ⟨H, -⟩; iexact H

theorem acRead_bound (C : AuthC) (γa : auth.AuthNames) (hM : C = .on γa) (s : Loc)
    (E : apply.AEnv GF) : acRead C s E ⊢ srvAuthBound s E := by
  subst hM
  dsimp only [acRead, AuthC.mode, AuthC.isOn]
  iintro ⟨-, H⟩
  iexact H

end laws

end EtcdGrove
end Perennial
