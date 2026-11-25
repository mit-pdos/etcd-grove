-- The copy for the part `KvNet/` of `Net/Proof/net/Errors.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The Go model's helpers and `netFD` methods (`models/net/model.go`, translated; over the primitive
stubs of `Net/TrustedCode/net.lean`), as WP lemmas the proofs of `net`'s specs use: the stubs
(`extAny*`), the errors (`closedErr`, `kindErr`, `codeErr`: `kindErr`'s and `resKind`'s predicates
of `Base.lean`), the addresses (`anyTCPAddr`: `netAddr`), `netOk`, the `netFD`s the model makes
(`modelFD`, `newConn`: `fdAt`, `isConn`), Go's `conn.ok`/`TCPListener.ok`, and `netFD`'s methods
(one lemma per model: the extension's operation, then the result's error).
-/
module

public import KvNet.Proof.net.Base
public import KvNet.Spec.net.Conn__Read

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

/-! ### The primitive stubs that answer arbitrarily -/

theorem wp_extAnyString (Φ : val → IProp GF) :
    (∀ s : GoString, Φ #s) -∗ WP (App (Val (@! net.extAnyString)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyString
  iexact HΦ

theorem wp_extAnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ #n) -∗ WP (App (Val (@! net.extAnyW64)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyW64
  iexact HΦ

theorem wp_extAnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ #b) -∗ WP (App (Val (@! net.extAnyBool)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyBool
  iexact HΦ

theorem wp_extAnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ #n) -∗ WP (App (Val (@! net.extAnyErrno)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyErrno
  iexact HΦ

/-- `fdAt`'s content, for a proof that keeps `fdAt` itself too. -/
theorem fdAt_elim (fd : Loc) (id : w64) (nw : GoString) (la ra : GoInterface) :
    fdAt (GF := GF) fd id nw la ra ⊢
      ∃ v : netFD, ⌜v.pfd'.Sysfd' = id ∧ v.net' = nw ∧ v.laddr' = la ∧ v.raddr' = ra⌝ ∗ fd ↦□ v := by
  unfold fdAt; iintro ⟨%v, %h, #Hv, -⟩; iexists v; iframe Hv; ipureintro; exact h

/-- `lisAt`'s content, for a proof that keeps `lisAt` itself too. -/
theorem lisAt_elim (t : Loc) (l : w64) (x : GoInterface) :
    lisAt (GF := GF) t l x ⊢
      ∃ (nw : GoString) (fd : Loc) (lc : ListenConfig) (ra : GoInterface), ⌜tcpNet nw ∧ l ≠ 0⌝ ∗
        t ↦□ (TCPListener.mk fd lc) ∗ fdAt fd l nw x ra ∗ netAddr x := by
  unfold lisAt lisFd
  iintro ⟨%nw, %hnw, ⟨%fd, %lc, %ra, #Ht, #Hfd⟩, #Hx, %hl⟩
  iexists nw, fd, lc, ra
  iframe Ht Hfd Hx
  ipureintro; exact ⟨hnw, hl⟩

/-! ### The primitive stubs of the extension's operations

Each takes the caller's atomic update in the form the specs give it (a result `Q res`) and returns
the result's code, with what the outcome says of it: never a timeout, but for `Read`, `Write`. -/

local notation "NG" => extGlobalGS netExt (G := hG.goose_globalGS)
local notation "NL" => extLocalGS netExt (L := hG.goose_localGS)

theorem wp_extClose (cn : Nat) (s : Bool) (a : GoString) (Q : Option NetErr → IProp GF)
    (Φ : val → IProp GF) :
    netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
      ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗ netEnd NG cn s st' -∗
        netDir NG cn s d' ={∅,⊤}=∗ Q res) -∗
    (∀ res, Q res -∗ ⌜res ≠ some .timeout⌝ -∗ Φ #(errCode res)) -∗
    WP (App (Val (@! net.extClose)) (Val #(endId cn s))) {{ Φ }} := by
  iintro #Hat HAU HΦ
  wp_func_call; wp_call
  iapply wp_net_Close cn s a $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %st' %d' %Hc Hend Hdir
  imod Hk $$ %res %st' %d' %Hc Hend Hdir with HQ
  imodintro
  iapply HΦ $$ HQ
  ipureintro
  unfold CloseOutcome at Hc; split at Hc <;> (rw [Hc.1]; simp)

theorem wp_extCloseWrite (cn : Nat) (s : Bool) (a : GoString) (Q : Option NetErr → IProp GF)
    (Φ : val → IProp GF) :
    netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
      ∀ res d', ⌜CloseWriteOutcome st d res d'⌝ -∗ netEnd NG cn s st -∗
        netDir NG cn s d' ={∅,⊤}=∗ Q res) -∗
    (∀ res, Q res -∗ ⌜res ≠ some .timeout⌝ -∗ Φ #(errCode res)) -∗
    WP (App (Val (@! net.extCloseWrite)) (Val #(endId cn s))) {{ Φ }} := by
  iintro #Hat HAU HΦ
  wp_func_call; wp_call
  iapply wp_net_CloseWrite cn s a $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %res %d' %Hc Hend Hdir
  imod Hk $$ %res %d' %Hc Hend Hdir with HQ
  imodintro
  iapply HΦ $$ HQ
  ipureintro
  unfold CloseWriteOutcome at Hc; split at Hc
  · rw [Hc.1]; simp
  · rcases Hc with h | h <;> (rw [h.1]; simp)

theorem wp_extSetDeadline (cn : Nat) (s : Bool) (a : GoString) (kind : w64) (tm : time.Time)
    (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res st', ⌜DeadlineOutcome st kind (!timeIsZero tm.wall' tm.ext') res st'⌝ -∗
        netEnd NG cn s st' ={∅,⊤}=∗ Q res) -∗
    (∀ res, Q res -∗ ⌜res ≠ some .timeout⌝ -∗ Φ #(errCode res)) -∗
    WP (App (App (App (Val (@! net.extSetDeadline)) (Val #(endId cn s))) (Val #kind)) (Val #tm))
      {{ Φ }} := by
  iintro #Hat HAU HΦ
  wp_func_call; wp_call
  wp_auto
  iapply wp_net_SetDeadline cn s a kind tm.wall' tm.ext' $$ Hat
  imod HAU with ⟨%st, Hend, Hk⟩
  imodintro
  iexists st
  iframe Hend
  iintro %res %st' %Hc Hend
  imod Hk $$ %res %st' %Hc Hend with HQ
  imodintro
  iapply HΦ $$ HQ
  ipureintro
  unfold DeadlineOutcome at Hc; split at Hc <;> (rw [Hc.1]; simp)

theorem wp_extSetSockopt (cn : Nat) (s : Bool) (a : GoString) (kind x : w64)
    (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (sockOptValid kind x) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res, Q res -∗ ⌜res ≠ some .timeout⌝ -∗ Φ #(errCode res)) -∗
    WP (App (App (App (Val (@! net.extSetSockopt)) (Val #(endId cn s))) (Val #kind)) (Val #x))
      {{ Φ }} := by
  iintro #Hat HAU HΦ
  wp_func_call; wp_call
  iapply wp_net_SetSockopt cn s a kind x $$ Hat
  imod HAU with ⟨%st, Hend, Hk⟩
  imodintro
  iexists st
  iframe Hend
  iintro %res %Hc Hend
  imod Hk $$ %res %Hc Hend with HQ
  imodintro
  iapply HΦ $$ HQ
  ipureintro
  unfold SockOptOutcome at Hc
  split at Hc
  · rw [Hc]; simp
  · split at Hc
    · rw [Hc]; simp
    · split at Hc <;> (rw [Hc]; simp)

theorem wp_extLisClose (l : w64) (a : GoString) (Q : Option NetErr → IProp GF)
    (Φ : val → IProp GF) :
    netLisOn NL l a -∗
    (|={⊤,∅}=> ∃ o, netLis NL l a o ∗
      ∀ res, ⌜LisCloseOutcome o res false⌝ -∗ netLis NL l a false ={∅,⊤}=∗ Q res) -∗
    (∀ res, Q res -∗ ⌜res ≠ some .timeout⌝ -∗ Φ #(errCode res)) -∗
    WP (App (Val (@! net.extLisClose)) (Val #l)) {{ Φ }} := by
  iintro Hon HAU HΦ
  wp_func_call; wp_call
  iapply wp_net_LisClose l a $$ Hon
  imod HAU with ⟨%o, Hl, Hk⟩
  imodintro
  iexists o
  iframe Hl
  iintro %res %Hc Hl
  imod Hk $$ %res %Hc Hl with HQ
  imodintro
  iapply HΦ $$ HQ
  ipureintro
  unfold LisCloseOutcome at Hc; split at Hc <;> (rw [Hc.1]; simp)

theorem wp_extRead (cn : Nat) (s : Bool) (a : GoString) (n : w64) (Q : ReadRes → IProp GF)
    (Φ : val → IProp GF) :
    netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn (!s) d ∗
      ∀ r d', ⌜ReadOutcome st d n.toNat r d'⌝ -∗ netEnd NG cn s st -∗
        netDir NG cn (!s) d' ={∅,⊤}=∗ Q r) -∗
    (∀ r, Q r -∗ ⌜∃ st d d', ReadOutcome st d n.toNat r d'⌝ -∗ Φ r.toVal) -∗
    WP (App (App (Val (@! net.extRead)) (Val #(endId cn s))) (Val #n)) {{ Φ }} := by
  iintro #Hat HAU HΦ
  wp_func_call; wp_call
  iapply wp_net_Read cn s a n $$ Hat
  imod HAU with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Hc Hend Hdir
  imod Hk $$ %r %d' %Hc Hend Hdir with HQ
  imodintro
  iapply HΦ $$ HQ
  ipureintro
  exact ⟨st, d, d', Hc⟩

theorem wp_extWrite (cn : Nat) (s : Bool) (a : GoString) (bs : List w8) (first : Bool)
    (Φ : val → IProp GF) :
    netConnAt NG cn a -∗ (if first then iprop(True) else netWLock NG cn s) -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
      ∀ k res d', ⌜WriteOutcome st d bs k res d'⌝ -∗ netEnd NG cn s st -∗
        netDir NG cn s d' ={∅,⊤}=∗
        ((if writeLast bs k res then iprop(True) else netWLock NG cn s) -∗
          Φ (PairV (#(BitVec.ofNat 64 k)) (#(errCode res))))) -∗
    WP (App (App (App (Val (@! net.extWrite)) (Val #(endId cn s))) (Val #bs)) (Val #first))
      {{ Φ }} := by
  iintro #Hat Hlk HAU
  wp_func_call; wp_call
  iapply wp_net_Write cn s a bs first $$ Hat Hlk HAU

theorem wp_extListen (a : GoString) (Φ : val → IProp GF) :
    ⌜listenOk a = true⌝ -∗
    (|={⊤,∅}=> lisToks NG a ∗ (lisToks NG a ={∅,⊤}=∗ True)) -∗
    (Φ (failV .sys) ∧ ∀ l : w64, ⌜l ≠ 0⌝ -∗ netLis NL l a true -∗
      netLisOn NL l a -∗ Φ (PairV (#l) (#(W64 0)))) -∗
    WP (App (Val (@! net.extListen)) (Val #a)) {{ Φ }} := by
  iintro %ha Htok HΦ
  wp_func_call; wp_call
  iapply wp_net_Listen a $$ %ha Htok HΦ

theorem wp_extDial (a : GoString) (Φ : val → IProp GF) :
    ⌜addrOk a = true⌝ -∗
    (Φ (failV .sys) ∧
      |={⊤,∅}=> ∃ S, netPend NG a S ∗
        ∀ c, ⌜c ∉ S⌝ -∗ netPend NG a (S ∪ {[c]}) -∗ netConnAt NG c a -∗
          netFresh NG c true -∗
          ((netFresh NG c false ={∅,⊤}=∗ Φ (PairV (#(endId c false)) (#(W64 0)))) ∧
           (netEnd NG c false { NetEnd.fresh with closed := true } -∗
            netDir NG c false ⟨[], .fin⟩ ={∅,⊤}=∗ Φ (failV .sys)))) -∗
    WP (App (Val (@! net.extDial)) (Val #a)) {{ Φ }} := by
  iintro %ha HΦ
  wp_func_call; wp_call
  iapply wp_net_Dial a $$ %ha HΦ

theorem wp_extAccept (l : w64) (la : GoString) (Φ : val → IProp GF) :
    netLisOn NL l la -∗
    ((|={⊤,∅}=> ∃ o, netLis NL l la o ∗
        (netLis NL l la o ={∅,⊤}=∗ Φ (failV (if o then .sys else .closed)))) ∧
      ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
        |={⊤,∅}=> ∃ o S, netLis NL l la o ∗ netPend NG a S ∗
          (⌜o = true⌝ -∗ ∀ c, ⌜c ∈ S⌝ -∗ netLis NL l la o -∗
            netPend NG a (S \ {[c]}) -∗ netConnAt NG c a ={∅,⊤}=∗
            Φ (PairV (#(endId c true)) (#(W64 0))))) -∗
    WP (App (Val (@! net.extAccept)) (Val #l)) {{ Φ }} := by
  iintro Hon HΦ
  wp_func_call; wp_call
  iapply wp_net_Accept l la $$ Hon HΦ

/-! ### Errors (D14) -/

theorem wp_closedErr (Φ : val → IProp GF) :
    Φ #closedErr -∗ WP (App (Val (@! net.netClosingErr)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  (try wp_auto)
  unfold closedErr
  iexact HΦ

/-- The `Err` of a failure of kind `k` (its code `c`), `name` the system call's. -/
theorem wp_kindErr (k : NetErr) (ed : Option GoInterface) (name : GoString)
    (nm : GoString → Prop) (hnm : nm name) {c : w64} (hc : c = errCode (some k))
    (Φ : val → IProp GF) :
    edAt (GF := GF) k ed -∗ (∀ e, kindErr (GF := GF) k ed nm e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.codeKindErr)) (Val #c)) (Val #name)) {{ Φ }} := by
  subst hc
  iintro Hed HΦ
  wp_func_call; wp_call
  cases k
  · wp_auto
    wp_apply wp_closedErr
    (try wp_auto)
    iapply HΦ
    unfold kindErr
    ipureintro; rfl
  · cases ed with
    | none => unfold edAt; iexfalso; iexact Hed
    | some e =>
      unfold edAt
      wp_auto
      iapply HΦ
      unfold kindErr
      ipureintro; rfl
  · wp_auto
    wp_apply wp_extAnyErrno as %n %hn
    wp_alloc p as Hp
    ipersist Hp
    wp_auto
    iapply HΦ
    unfold kindErr sysErr
    iexists p, name, n
    isplitr
    · ipureintro; exact ⟨rfl, hnm, hn⟩
    iexact Hp

/-- `codeErr(c, name)`: `nil` for success, else the kind's error. -/
theorem wp_codeErr (res : Option NetErr) (ed : Option GoInterface) (name : GoString)
    (nm : GoString → Prop) (hnm : nm name) {c : w64} (hc : c = errCode res)
    (Φ : val → IProp GF) :
    (match res with | some k => edAt (GF := GF) k ed | none => iprop(True)) -∗
    (∀ e, resKind (GF := GF) res ed nm e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.codeErr)) (Val #c)) (Val #name)) {{ Φ }} := by
  subst hc
  iintro Hed HΦ
  wp_func_call; wp_call
  cases res with
  | none =>
    wp_auto
    iapply HΦ
    unfold resKind
    ipureintro; rfl
  | some k =>
    have hk : errCode (some k) ≠ W64 0 := by cases k <;> decide
    (try wp_auto)
    rw [decide_eq_false hk]
    (try wp_auto)
    wp_apply wp_kindErr k ed name nm hnm rfl $$ Hed as %e #He
    (try wp_auto)
    iapply HΦ
    unfold resKind
    iexact He

/-! ### Addresses (D18) and networks (D23) -/

theorem wp_anyTCPAddr (Φ : val → IProp GF) :
    (∀ x, netAddr (GF := GF) x -∗ Φ #x) -∗
    WP (App (Val (@! net.anyTCPAddr)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_extAnyString as %z
  wp_apply wp_string_to_bytes z as %sl ⟨-, -⟩
  wp_apply wp_extAnyW64 as %port
  wp_apply wp_extAnyString as %zone
  wp_alloc p as Hp
  ipersist Hp
  wp_auto
  iapply HΦ
  unfold netAddr
  iexists p, _
  isplitr
  · ipureintro; rfl
  iexact Hp

/-- `anyListenAddr()`: `anyTCPAddr()`, or a new `*TCPAddr` with a nil IP (Go's for `":p"`). -/
theorem wp_anyListenAddr (Φ : val → IProp GF) :
    (∀ x, netAddr (GF := GF) x -∗ Φ #x) -∗
    WP (App (Val (@! net.anyListenAddr)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_extAnyBool as %b
  cases b
  · wp_auto
    wp_apply wp_anyTCPAddr as %x #Hx
    (try wp_auto)
    iapply HΦ
    iexact Hx
  · wp_auto
    wp_apply wp_extAnyW64 as %port
    wp_alloc p as Hp
    ipersist Hp
    wp_auto
    iapply HΦ
    unfold netAddr
    iexists p, _
    isplitr
    · ipureintro; rfl
    iexact Hp

/-- D23. The networks the model accepts (`netOk`): `true` for `"tcp"` and `"tcp4"`. -/
theorem wp_netOk (nw : GoString) (hnw : tcpNet nw) (Φ : val → IProp GF) :
    Φ #true -∗ WP (App (Val (@! net.netOk)) (Val #nw)) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  rcases hnw with rfl | rfl
  · wp_auto; iexact HΦ
  · wp_auto; iexact HΦ

/-! ### The `netFD`s the model makes -/

/-- `modelFD(id, nw, la, ra)`: a new `netFD`, read-only for good. -/
theorem wp_modelFD (id : w64) (nw : GoString) (la ra : GoInterface) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.net -∗
    (∀ fd : Loc, fdAt (GF := GF) fd id nw la ra -∗ Φ #fd) -∗
    WP (App (App (App (App (Val (@! net.modelFD)) (Val #id)) (Val #nw)) (Val #la)) (Val #ra))
      {{ Φ }} := by
  iintro #Hnet HΦ
  iapply wp_fupd
  wp_func_call; wp_call
  wp_auto
  ipersist «$r0»
  imodintro
  iapply HΦ
  unfold fdAt
  iexists _
  iframe «$r0» Hnet
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A new `*TCPConn` for the end `s` of `cn` on the network `nw`, with new addresses. -/
theorem wp_newConn (cn : Nat) (s : Bool) (a nw : GoString) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.net -∗
    ⌜tcpNet nw⌝ -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
    (∀ (t : Loc) (la ra : GoInterface), connAt (GF := GF) t cn s a la ra -∗ Φ #t) -∗
    WP (App (App (Val (@! net.newConn)) (Val #(endId cn s))) (Val #nw)) {{ Φ }} := by
  iintro #Hnet %hnw #Hat HΦ
  iapply wp_fupd
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_anyTCPAddr as %la #Hla
  (try wp_auto)
  wp_apply wp_anyTCPAddr as %ra #Hra
  (try wp_auto)
  wp_apply wp_modelFD $$ Hnet as %fd #Hfd
  (try wp_auto)
  ipersist «$r0»
  imodintro
  iapply HΦ $$ %«$r0_ptr» %la %ra
  unfold connAt connFd
  iexists nw
  iframe Hat Hla Hra
  isplitr
  · ipureintro; exact hnw
  iexists fd
  iframe «$r0» Hfd

/-! ### `ok()`: Go's `c != nil && c.fd != nil` -/

/-- `(*conn).ok()` on a `conn` holding a non-nil `fd`: `true`. -/
theorem wp_conn_ok (c fd : Loc) (hfd : fd ≠ null) (Φ : val → IProp GF) :
    (c ↦□ (conn.mk fd) : IProp GF) -∗ Φ #true -∗
    WP (App (Val #(methods (go.GoType.PointerType conn.ty) go!"ok" #c)) (Val #())) {{ Φ }} := by
  iintro #Hc HΦ
  ihave %hc := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  wp_method_call; wp_call
  wp_auto
  rw [show (!decide (c = null)) = true by simp [hc]]
  wp_auto
  (try rw [show (!decide (fd = null)) = true by simp [hfd]])
  (try simp only [hfd, decide_false, Bool.not_false])
  (try wp_auto)
  iexact HΦ

/-- `(*TCPConn).ok()` (`conn`'s, promoted) on a `TCPConn` holding a non-nil `fd`: `true`. -/
theorem wp_TCPConn_ok (t fd : Loc) (hfd : fd ≠ null) (Φ : val → IProp GF) :
    (t ↦□ (TCPConn.mk (conn.mk fd)) : IProp GF) -∗ Φ #true -∗
    WP (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"ok" #t)) (Val #())) {{ Φ }} := by
  iintro #Ht HΦ
  iStructNamed Ht
  wp_method_call
  (try wp_auto)
  wp_apply wp_conn_ok _ fd hfd $$ conn
  (try wp_auto)
  iexact HΦ

/-- `(*TCPListener).ok()` on a listener holding a non-nil `fd`: `true`. -/
theorem wp_TCPListener_ok (t fd : Loc) (lc : ListenConfig) (hfd : fd ≠ null) (Φ : val → IProp GF) :
    (t ↦□ (TCPListener.mk fd lc) : IProp GF) -∗ Φ #true -∗
    WP (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"ok" #t)) (Val #())) {{ Φ }} := by
  iintro #Ht HΦ
  ihave %ht := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  wp_method_call; wp_call
  wp_auto
  (try rw [show (!decide (t = null)) = true by simp [ht]])
  (try wp_auto)
  (try rw [show (!decide (fd = null)) = true by simp [hfd]])
  (try wp_auto)
  iexact HΦ

/-! ### `netFD`'s methods (the model) -/

/-- `codeErr` of a result that is not a timeout (no deadline error needed). -/
theorem wp_codeErr_nt (res : Option NetErr) (hres : res ≠ some .timeout) (name : GoString)
    (nm : GoString → Prop) (hnm : nm name) {c : w64} (hc : c = errCode res)
    (Φ : val → IProp GF) :
    (∀ e, resKind (GF := GF) res none nm e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.codeErr)) (Val #c)) (Val #name)) {{ Φ }} := by
  iintro HΦ
  iapply wp_codeErr res none name nm hnm hc Φ $$ [] HΦ
  rcases res with _ | k
  · dsimp only; itrivial
  · cases k
    · dsimp only; unfold edAt; itrivial
    · exact absurd rfl hres
    · dsimp only; unfold edAt; itrivial

/-- D3. `fd.Close()`: the extension's `Close` of the end, then the result's error. -/
theorem wp_fd_Close (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
      ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗ netEnd NG cn s st' -∗
        netDir NG cn s d' ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"close") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"Close" #fd)) (Val #())) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extClose cn s a Q $$ Hat HAU as %res HQ %hres
  wp_apply wp_codeErr_nt res hres go!"close" (· = go!"close") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D4. `fd.closeWrite()`: the extension's `CloseWrite`. -/
theorem wp_fd_closeWrite (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
      ∀ res d', ⌜CloseWriteOutcome st d res d'⌝ -∗ netEnd NG cn s st -∗
        netDir NG cn s d' ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"shutdown") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"closeWrite" #fd)) (Val #())) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extCloseWrite cn s a Q $$ Hat HAU as %res HQ %hres
  wp_apply wp_codeErr_nt res hres go!"shutdown" (· = go!"shutdown") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D5. `fd.SetDeadline(tm)`: the extension's `SetDeadline` of both deadlines. -/
theorem wp_fd_SetDeadline (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (tm : time.Time) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res st', ⌜DeadlineOutcome st (W64 0) (!timeIsZero tm.wall' tm.ext') res st'⌝ -∗
        netEnd NG cn s st' ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"set") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"SetDeadline" #fd)) (Val #tm)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetDeadline cn s a (W64 0) tm Q $$ Hat HAU as %res HQ %hres
  wp_apply wp_codeErr_nt res hres go!"set" (· = go!"set") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D5. `fd.SetReadDeadline(tm)`: the extension's `SetDeadline` of the read deadline. -/
theorem wp_fd_SetReadDeadline (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (tm : time.Time) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res st', ⌜DeadlineOutcome st (W64 1) (!timeIsZero tm.wall' tm.ext') res st'⌝ -∗
        netEnd NG cn s st' ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"set") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"SetReadDeadline" #fd)) (Val #tm)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetDeadline cn s a (W64 1) tm Q $$ Hat HAU as %res HQ %hres
  wp_apply wp_codeErr_nt res hres go!"set" (· = go!"set") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D5. `fd.SetWriteDeadline(tm)`: the extension's `SetDeadline` of the write deadline. -/
theorem wp_fd_SetWriteDeadline (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (tm : time.Time) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res st', ⌜DeadlineOutcome st (W64 2) (!timeIsZero tm.wall' tm.ext') res st'⌝ -∗
        netEnd NG cn s st' ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"set") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"SetWriteDeadline" #fd)) (Val #tm)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetDeadline cn s a (W64 2) tm Q $$ Hat HAU as %res HQ %hres
  wp_apply wp_codeErr_nt res hres go!"set" (· = go!"set") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D24. `setReadBuffer(fd, …)`: the extension's `SetSockopt` (SO_RCVBUF, always valid). -/
theorem wp_setReadBuffer (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (bytes : w64) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (some true) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"setsockopt") e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.setReadBuffer)) (Val #fd)) (Val #bytes)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_func_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetSockopt cn s a (W64 0) (W64 0) Q $$ Hat [HAU] as %res HQ %hres
  · rw [show sockOptValid (W64 0) (W64 0) = (some true) by simp [sockOptValid]]; iexact HAU
  wp_apply wp_codeErr_nt res hres go!"setsockopt" (· = go!"setsockopt") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D24. `setWriteBuffer(fd, …)`: the extension's `SetSockopt` (SO_SNDBUF, always valid). -/
theorem wp_setWriteBuffer (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (bytes : w64) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (some true) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"setsockopt") e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.setWriteBuffer)) (Val #fd)) (Val #bytes)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_func_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetSockopt cn s a (W64 0) (W64 0) Q $$ Hat [HAU] as %res HQ %hres
  · rw [show sockOptValid (W64 0) (W64 0) = (some true) by simp [sockOptValid]]; iexact HAU
  wp_apply wp_codeErr_nt res hres go!"setsockopt" (· = go!"setsockopt") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D24. `setKeepAlive(fd, …)`: the extension's `SetSockopt` (SO_KEEPALIVE, always valid). -/
theorem wp_setKeepAlive (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (ka : Bool) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (some true) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"setsockopt") e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.setKeepAlive)) (Val #fd)) (Val #ka)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_func_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetSockopt cn s a (W64 0) (W64 0) Q $$ Hat [HAU] as %res HQ %hres
  · rw [show sockOptValid (W64 0) (W64 0) = (some true) by simp [sockOptValid]]; iexact HAU
  wp_apply wp_codeErr_nt res hres go!"setsockopt" (· = go!"setsockopt") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D24. `setLinger(fd, …)`: the extension's `SetSockopt` (SO_LINGER, always valid). -/
theorem wp_setLinger (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (sec : w64) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (some true) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"setsockopt") e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.setLinger)) (Val #fd)) (Val #sec)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_func_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetSockopt cn s a (W64 0) (W64 0) Q $$ Hat [HAU] as %res HQ %hres
  · rw [show sockOptValid (W64 0) (W64 0) = (some true) by simp [sockOptValid]]; iexact HAU
  wp_apply wp_codeErr_nt res hres go!"setsockopt" (· = go!"setsockopt") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D24. `setNoDelay(fd, …)`: the extension's `SetSockopt` (TCP_NODELAY, always valid). -/
theorem wp_setNoDelay (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (nd : Bool) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (some true) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"setsockopt") e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.setNoDelay)) (Val #fd)) (Val #nd)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_func_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetSockopt cn s a (W64 0) (W64 0) Q $$ Hat [HAU] as %res HQ %hres
  · rw [show sockOptValid (W64 0) (W64 0) = (some true) by simp [sockOptValid]]; iexact HAU
  wp_apply wp_codeErr_nt res hres go!"setsockopt" (· = go!"setsockopt") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D24. `setKeepAliveIdle(fd, …)`: the extension's `SetSockopt` of `TCP_KEEPIDLE` (`keepIdleValid`). -/
theorem wp_setKeepAliveIdle (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (d : w64) (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗
    (|={⊤,∅}=> ∃ st, netEnd NG cn s st ∗
      ∀ res, ⌜SockOptOutcome st (keepIdleValid d) res⌝ -∗ netEnd NG cn s st ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"setsockopt") e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.setKeepAliveIdle)) (Val #fd)) (Val #d)) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_func_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extSetSockopt cn s a (W64 1) d Q $$ Hat [HAU] as %res HQ %hres
  · rw [show sockOptValid (W64 1) d = (keepIdleValid d) by simp [sockOptValid]]; iexact HAU
  wp_apply wp_codeErr_nt res hres go!"setsockopt" (· = go!"setsockopt") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- D9. `ln.close()` (`TCPListener`'s model): the extension's `LisClose`. -/
theorem wp_TCPListener_close (t : Loc) (l : w64) (x : GoInterface) (a : GoString)
    (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    lisAt (GF := GF) t l x -∗ netLisOn NL l a -∗
    (|={⊤,∅}=> ∃ o, netLis NL l a o ∗
      ∀ res, ⌜LisCloseOutcome o res false⌝ -∗ netLis NL l a false ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"close") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"close" #t)) (Val #()))
      {{ Φ }} := by
  iintro #Hl Hon HAU HΦ
  unfold lisAt lisFd fdAt
  icases Hl with ⟨%nw, %hnw, ⟨%fd, %lc, %ra, #Ht, %v, %hv, #Hv, -⟩, #Hx, %hl⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Ht
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extLisClose l a Q $$ Hon HAU as %res HQ %hres
  wp_apply wp_codeErr_nt res hres go!"close" (· = go!"close") rfl rfl as %e #He
  (try wp_auto)
  iapply HΦ $$ HQ He

/-- The `Err` of `fd.Read`'s result `r` (before `conn.Read`'s wrapping): `nil` for bytes, `eof`
(`io.EOF`'s value) for EOF, the kind's error for a failure. -/
def fdReadErr (r : ReadRes) (eof ed e : GoInterface) : IProp GF :=
  match r with
  | .bytes _ => iprop(⌜e = interface.nil⌝)
  | .eof => iprop(⌜e = eof⌝)
  | .err k => kindErr k (some ed) (· = go!"read") e

instance fdReadErr_persistent (r : ReadRes) (eof ed e : GoInterface) :
    Persistent (fdReadErr (GF := GF) r eof ed e) := by
  cases r <;> unfold fdReadErr <;> infer_instance

/-- D1. `fd.Read(b)`: the extension's `Read` of `len(b)` bytes, copied into `b`; EOF is `io.EOF`;
two later credits from the steps after the extension's `Read`. -/
theorem wp_fd_Read (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (b : GoSlice) (bs0 : List w8) (eof ed : GoInterface) (Q : ReadRes → IProp GF)
    (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗ b ↦* bs0 -∗
    globalAddr io.EOF ↦□ eof -∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed -∗
    (|={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn (!s) d ∗
      ∀ r d', ⌜ReadOutcome st d b.len.toNat r d'⌝ -∗ netEnd NG cn s st -∗
        netDir NG cn (!s) d' ={∅,⊤}=∗ Q r) -∗
    (∀ (r : ReadRes) (bs' : List w8) (k : w64) (e : GoInterface), Q r -∗ b ↦* bs' -∗
      ⌜ReadOutZ bs0 r k bs'⌝ -∗ fdReadErr (GF := GF) r eof ed e -∗ £ 1 -∗ £ 1 -∗
      Φ (PairV #k #e)) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"Read" #fd)) (Val #b)) {{ Φ }} := by
  iintro #Hfd #Hat Hsl #Heof #Hed HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extRead cn s a b.len Q $$ Hat HAU as %r HQ %hr
  cases r with
  | bytes bs =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto_lc 2
    wp_apply wp_string_to_bytes bs as %sl ⟨Hsl2, -⟩
    wp_apply wp_slice_copy_int b bs0 sl bs (DFrac.own 1) $$ [Hsl Hsl2] as %n ⟨%Hn, Hsl, -⟩
    · iframe
    (try wp_auto)
    iapply HΦ $$ HQ Hsl [] [] Hlc1 Hlc2
    · ipureintro; exact ⟨Hn, rfl⟩
    · unfold fdReadErr; ipureintro; rfl
  | eof =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto_lc 2
    iapply HΦ $$ HQ Hsl [] [] Hlc1 Hlc2
    · ipureintro; exact ⟨rfl, rfl⟩
    · unfold fdReadErr; ipureintro; rfl
  | err k =>
    simp only [ReadRes.toVal]
    unfold readRes
    wp_auto_lc 2
    have h0 : k.code ≠ W64 0 := by cases k <;> decide
    have h4 : k.code ≠ W64 4 := by cases k <;> decide
    (try rw [decide_eq_false h0])
    (try wp_auto)
    (try rw [decide_eq_false h4])
    (try wp_auto)
    wp_apply wp_kindErr (c := k.code) k (some ed) go!"read" (· = go!"read") rfl rfl $$ [] as %e #He
    · cases k <;> (unfold edAt; first | itrivial | iexact Hed)
    (try wp_auto)
    iapply HΦ $$ HQ Hsl [] [] Hlc1 Hlc2
    · ipureintro; exact ⟨rfl, rfl⟩
    · unfold fdReadErr; iexact He

/-- D7. `fd.accept()` on the listener `l`: the extension's `Accept`; a new `netFD` of the end
`(c, true)` on the listener's network, with new addresses, or the failure's error. -/
theorem wp_fd_accept (fd : Loc) (l : w64) (nw : GoString) (x ra : GoInterface) (la : GoString)
    (Φ : val → IProp GF) :
    fdAt (GF := GF) fd l nw x ra -∗ netLisOn NL l la -∗
    ((|={⊤,∅}=> ∃ o, netLis NL l la o ∗
        (netLis NL l la o ={∅,⊤}=∗ ∀ e, kindErr (GF := GF) (if o then .sys else .closed) none
          (· = go!"accept4") e -∗ Φ (PairV #null #e))) ∧
      ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
        |={⊤,∅}=> ∃ o S, netLis NL l la o ∗ netPend NG a S ∗
          (⌜o = true⌝ -∗ ∀ c, ⌜c ∈ S⌝ -∗ netLis NL l la o -∗
            netPend NG a (S \ {[c]}) -∗ netConnAt NG c a ={∅,⊤}=∗
            ∀ nfd la' ra', fdAt (GF := GF) nfd (endId c true) nw la' ra' -∗ netAddr la' -∗
              netAddr ra' -∗ Φ (PairV #nfd #interface.nil))) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"accept" #fd)) (Val #()))
      {{ Φ }} := by
  iintro #Hfd Hon HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, #Hnet⟩
  obtain ⟨hid, hnw, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extAccept l la $$ Hon
  isplit
  · icases HΦ with ⟨HΦ, -⟩
    imod HΦ with ⟨%o, Hl, Hk⟩
    imodintro
    iexists o
    iframe Hl
    iintro Hl
    imod Hk $$ Hl with HΦ
    imodintro
    unfold failV
    have hk : (if o then NetErr.sys else NetErr.closed).code ≠ W64 0 := by cases o <;> decide
    wp_auto
    (try rw [decide_eq_false hk])
    (try wp_auto)
    wp_apply wp_kindErr (c := (if o then NetErr.sys else NetErr.closed).code)
      (if o then NetErr.sys else NetErr.closed) none go!"accept4"
      (· = go!"accept4") rfl rfl $$ [] as %e #He
    · cases o <;> (simp only [Bool.false_eq_true, ↓reduceIte]; unfold edAt; itrivial)
    (try wp_auto)
    iapply HΦ $$ He
  · icases HΦ with ⟨-, HΦ⟩
    iintro %a %ha
    imod HΦ $$ %a %ha with ⟨%o, %S, Hl, Hp, Hk⟩
    imodintro
    iexists o, S
    iframe Hl Hp
    iintro %ho %c %hc Hl Hp Hat
    imod Hk $$ %ho %c %hc Hl Hp Hat with HΦ
    imodintro
    wp_auto
    wp_apply wp_anyTCPAddr as %la' #Hla'
    wp_apply wp_anyTCPAddr as %ra' #Hra'
    rw [hnw]
    wp_apply wp_modelFD $$ Hnet as %nfd #Hnfd
    (try wp_auto)
    iapply HΦ $$ [Hnfd] Hla' Hra'
    unfold fdAt; iexact Hnfd

/-- D2, D25. `fd.Write(b)`: steps of the extension's `Write` (the caller's update `P` at each), until
one fails or every byte is written; the count, and the failure's error. -/
theorem wp_fd_Write (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (b : GoSlice) (bs : List w8) (dq : DFrac) (ed : GoInterface)
    (P : List w8 → Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗ netConnAt NG cn a -∗ b ↦*{dq} bs -∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed -∗ P [] none -∗
    □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ P w none -∗
        |={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn s d ∗
          ∀ k res d', ⌜WriteOutcome st d rs k res d'⌝ -∗ netEnd NG cn s st -∗
            netDir NG cn s d' ={∅,⊤}=∗ P (w ++ rs.take k) res) -∗
    (∀ (n : w64) (e : GoInterface) w res, P w res -∗ b ↦*{dq} bs -∗
      ⌜w <+: bs ∧ n = BitVec.ofNat 64 w.length ∧ (res = none → w = bs) ∧
        (w = bs → res = none ∨ bs = [])⌝ -∗
      resKind (GF := GF) res (some ed) (· = go!"write") e -∗ Φ (PairV #n #e)) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"Write" #fd)) (Val #b)) {{ Φ }} := by
  iintro #Hfd #Hat Hsl #Hed HP #Hacc HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv, -⟩
  obtain ⟨hid, -, -, -⟩ := hv
  iStructNamed Hv
  iStructNamed pfd
  icases ownSlice_len b dq bs $$ Hsl with %Hlen
  icases ownSlice_wf b dq bs $$ Hsl with %Hwf
  wp_method_call; wp_call
  wp_auto
  have hslz : sint.Z b.len = bs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hblen : b.len.toNat = bs.length ∧ bs.length < 2 ^ 63 := by
    have h := BitVec.toInt_eq_toNat_cond b.len
    simp only [sint.Z] at hslz
    split at h <;> omega
  have hbig := hblen.2
  -- the loop's invariant: `nn` bytes written, `nn = 0` or fewer than all
  ihave HI : (∃ nn : w64,
      "nn" ∷ nn_ptr ↦ nn ∗
      "HP" ∷ P (bs.take nn.toNat) none ∗
      "Hsl" ∷ b ↦*{dq} bs ∗
      "Hlk" ∷ (if decide (nn = W64 0) then iprop(True) else netWLock NG cn s) ∗
      "%Hnn" ∷ ⌜nn.toNat ≤ bs.length ∧ (nn.toNat = 0 ∨ nn.toNat < bs.length)⌝ : IProp GF)
    $$ [nn HP Hsl]
  · iexists W64 0
    iframe
    simp only [decide_true, ↓reduceIte]
    isplitl []
    · itrivial
    ipureintro; exact ⟨Nat.zero_le _, .inl rfl⟩
  wp_for HI
  have hle := Hnn.1
  have hnnz : sint.Z nn = nn.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nn = nn.toNat := by simp [sint.nat, hnnz]
  have hsb : 0 ≤ sint.Z nn ∧ sint.Z nn ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap := by
    exact ⟨by rw [hnnz]; omega, by rw [hnnz, hslz]; omega, Hwf.2⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsb)]
  ihave ⟨Hsl1, Hsl2⟩ := (ownSlice_split_all nn b dq bs ⟨by omega, by omega⟩).1 $$ Hsl
  rw [hnnn]
  wp_apply wp_bytes_to_string _ (bs.drop nn.toNat) dq $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_split_all nn b dq bs ⟨by omega, by omega⟩).2 $$ [Hsl1 Hsl2]
  · rw [hnnn]; iframe
  rw [hid]
  wp_apply wp_extWrite cn s a (bs.drop nn.toNat) (decide (nn = W64 0)) $$ Hat Hlk
  imod Hacc $$ %(bs.take nn.toNat) %(bs.drop nn.toNat) %(List.take_append_drop _ _) HP
    with ⟨%st, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st, d
  iframe Hend Hdir
  iintro %k %res %d' %Hw Hend Hdir
  imod Hk $$ %k %res %d' %Hw Hend Hdir with HP
  imodintro
  iintro Hlk
  have hkle := writeOutcome_le Hw
  simp only [List.length_drop] at hkle
  have hWk : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hnk : (nn + BitVec.ofNat 64 k).toNat = nn.toNat + k := by
    rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
  have htk : bs.take nn.toNat ++ (bs.drop nn.toNat).take k = bs.take (nn.toNat + k) :=
    (List.take_add ..).symm
  rcases res with _ | e
  · -- no failure
    wp_auto
    by_cases hfull : nn + BitVec.ofNat 64 k = b.len
    · rw [decide_eq_true hfull]
      wp_auto
      wp_for_post
      have hfk : nn.toNat + k = bs.length := by
        have := congrArg BitVec.toNat hfull; rw [hnk] at this
        have h2 : b.len.toNat = bs.length := hblen.1
        omega
      rw [htk, hfk, List.take_length]
      iapply HΦ $$ %_ %_ %bs %none HP Hsl [] []
      · ipureintro
        refine ⟨List.prefix_refl _, ?_, fun _ => rfl, fun _ => .inl rfl⟩
        rw [← hfk, ← hnk, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · unfold resKind; ipureintro; rfl
    · rw [decide_eq_false hfull]
      wp_auto
      wp_for_post
      have hlt : nn.toNat + k < bs.length := by
        have h2 : b.len.toNat = bs.length := hblen.1
        have : nn.toNat + k ≠ bs.length := by
          intro hc; apply hfull; apply BitVec.eq_of_toNat_eq; rw [hnk, h2]; exact hc
        omega
      have hk1 : 1 ≤ k := writeOutcome_none_pos Hw (by
        intro h; have := congrArg List.length h; simp at this; omega)
      have hwl : writeLast (bs.drop nn.toNat) k none = false := by
        simp only [writeLast, Option.isSome_none, Bool.false_or, decide_eq_false_iff_not,
          List.length_drop]; omega
      have hnz : decide (nn + BitVec.ofNat 64 k = W64 0) = false := by
        rw [decide_eq_false_iff_not]; intro h0
        have := congrArg BitVec.toNat h0; rw [hnk] at this; simp at this; omega
      rw [hwl] at *
      rw [htk] at *
      iframe
      iexists nn + BitVec.ofNat 64 k
      rw [hnk, hnz]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro; exact ⟨by omega, .inr hlt⟩
  · -- a failure: nothing counted
    obtain rfl := writeOutcome_fail Hw
    wp_auto
    have hne : errCode (some e) ≠ W64 0 := by cases e <;> decide
    rw [decide_eq_false hne]
    wp_auto
    rw [show nn + 0#64 = nn from BitVec.add_zero nn, List.take_zero, List.append_nil]
    have hpure : bs.take nn.toNat <+: bs ∧ nn = BitVec.ofNat 64 (bs.take nn.toNat).length ∧
        (some e = none → bs.take nn.toNat = bs) ∧
        (bs.take nn.toNat = bs → some e = none ∨ bs = []) := by
      refine ⟨List.take_prefix _ _, ?_, fun h => (by cases h), fun h => .inr ?_⟩
      · rw [List.length_take, Nat.min_eq_left hle, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · have := congrArg List.length h
        rw [List.length_take] at this
        apply List.eq_nil_of_length_eq_zero
        omega
    wp_apply wp_kindErr e (some ed) go!"write" (· = go!"write") rfl rfl $$ [] as %er #He
    · cases e <;> (unfold edAt; first | itrivial | iexact Hed)
    (try wp_auto)
    wp_for_post

    iapply HΦ $$ HP Hsl %hpure
    unfold resKind; iexact He

/-- D7. `ln.accept()` (`TCPListener`'s model): `fd.accept()`, then a new `*TCPConn` for the end
`(c, true)` on the listener's network, or the failure's error. -/
theorem wp_TCPListener_accept (t : Loc) (l : w64) (x : GoInterface) (la : GoString)
    (Φ : val → IProp GF) :
    lisAt (GF := GF) t l x -∗ netLisOn NL l la -∗
    ((|={⊤,∅}=> ∃ o, netLis NL l la o ∗
        (netLis NL l la o ={∅,⊤}=∗ ∀ e, kindErr (GF := GF) (if o then .sys else .closed) none
          (· = go!"accept4") e -∗ Φ (PairV #null #e))) ∧
      ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ -∗
        |={⊤,∅}=> ∃ o S, netLis NL l la o ∗ netPend NG a S ∗
          (⌜o = true⌝ -∗ ∀ c, ⌜c ∈ S⌝ -∗ netLis NL l la o -∗
            netPend NG a (S \ {[c]}) -∗ netConnAt NG c a ={∅,⊤}=∗
            ∀ (tc : Loc) (la' ra' : GoInterface), connAt (GF := GF) tc c true a la' ra' -∗
              Φ (PairV #tc #interface.nil))) -∗
    WP (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"accept" #t)) (Val #()))
      {{ Φ }} := by
  iintro #Hl Hon HΦ
  ihave ⟨%nw, %fd, %lc, %ra, %hnl, #Ht, #Hfd, #Hx⟩ := lisAt_elim _ _ _ $$ Hl
  iStructNamed Ht
  iapply wp_fupd
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_fd_accept fd l nw x ra la $$ Hfd Hon
  isplit
  · icases HΦ with ⟨HΦ, -⟩
    imod HΦ with ⟨%o, Hlo, Hk⟩
    imodintro
    iexists o
    iframe Hlo
    iintro Hlo
    imod Hk $$ Hlo with HΦ
    imodintro
    iintro %e #He
    ihave %hne := kindErr_ne_nil _ none _ e (fun _ h => by cases h) $$ He
    obtain ⟨ie, rfl⟩ : ∃ ie, e = GoInterface.ok ie := by
      cases e with | ok ie => exact ⟨ie, rfl⟩ | nil => exact absurd rfl hne
    wp_auto
    imodintro
    iapply HΦ $$ He
  · icases HΦ with ⟨-, HΦ⟩
    iintro %a %ha
    imod HΦ $$ %a %ha with ⟨%o, %S, Hlo, Hp, Hk⟩
    imodintro
    iexists o, S
    iframe Hlo Hp
    iintro %ho %c %hc Hlo Hp #Hat
    imod Hk $$ %ho %c %hc Hlo Hp Hat with HΦ
    imodintro
    iintro %nfd %la' %ra' #Hnfd #Hla' #Hra'
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ $$ %«$r0_ptr» %la' %ra'
    unfold connAt connFd
    iexists nw
    iframe Hat Hla' Hra'
    isplitr
    · ipureintro; exact hnl.1
    iexists nfd
    iframe «$r0» Hnfd

end proof

end net
end Perennial
