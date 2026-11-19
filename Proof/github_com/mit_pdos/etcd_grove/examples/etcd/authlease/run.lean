/-
`run(srvs, ms, lg)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): **proved**, over
its callees' specs. Lean-first (no Rocq counterpart). authN's `run.wp_proof` (`authN/run.lean`) for the
serve loop (authN's `serve_member` in the revocable lease mode), the set-up and the clients, with:

- the driver's cell (`Cell.lean`) allocated over member `0`'s KV state before the set-up, the set-up's
  puts through it (`cell_setupAu`);
- the two barrier rounds through `barriers` (`bArg`: each member's barrier arguments; the second
  round's read update `cell_readAu`, its floor seeing the three attachments);
- the leases (`grantPut` with the ghost step `cell_fix`, u's transaction `cell_txnTAu`), the checks
  (`noAuth`, u's refused put and transaction `refused_update`, `absent`, `foreign`, root's read of
  `z/lease`, u's revocation `cell_revokeUAu` and the absences after it), the lessor facts from the
  second barrier's floor (`cell_holds`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barriers
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.grantPut
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.noAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.foreign
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.absent
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Refusals
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.context.WithTimeoutBackgroundMd

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth etcdstart
open etcd_authN (Wit akV mod_len_sint srvdW srvdAt serve_member)
open etcd_auth3 (admStates_same srvAuthAtLog_same srvRLogLb_same srvReqLogLb_same authHistFrozen_same)

section barriers
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A served member's barrier arguments** (`barriers`' `bs`): its address, watch environment, server,
witnesses and names, the set-up's frozen history `hs` (`γz`), requested and committed logs, the auth
state's revision `r`, the read update `Q`. -/
abbrev bArg (γz : GName) (hs : List auth.AuthState) (Lset Lc : List EntryModel) (r : Nat)
    (Q : KVState → IProp GF) (q : (Loc × (GMember × MemberG GF)) × Wit GF) : BArgs GF :=
  { addr := q.1.2.1.Client', V := akV q.1.2.1.Client' q.1.2.2.ρ q.2.R, s := q.1.1, E := q.2.E,
    ρ := { q.1.2.2.ρ with wait := q.2.γw }, cid := q.2.cid, mid := q.2.mid, γa := q.2.γa, γz := γz,
    hs := hs, Lset := Lset, Lc := Lc, r := r, Q := Q }

/-- **Every served member's barrier precondition**: its served facts, the set-up's facts at member
`x0`'s names carried to its own (`*_same`), and the read update at its KV names. -/
theorem barrierPre_all (x0 : GMember × MemberG GF) (w0 : Wit GF) (γz : GName) (hs : List auth.AuthState)
    (Lset Lc : List EntryModel) (r : Nat) (Q : KVState → IProp GF)
    (l : List ((Loc × (GMember × MemberG GF)) × Wit GF))
    (hl : ∀ q ∈ l, etcdstart.sameCluster x0.2.ρ q.1.2.2.ρ ∧ plainEndpoint q.1.2.1.Client')
    (hadm : admStates { x0.2.ρ with wait := w0.γw }.kv srvAuthSt0 Lset = hs ∧
      srvAuthAtLog { x0.2.ρ with wait := w0.γw }.kv srvAuthSt0 Lset = setupSt r)
    (hlc : srvAuthAtLog { x0.2.ρ with wait := w0.γw }.kv srvAuthSt0 Lc = setupSt r) :
    ([∗list] q ∈ l, srvdW q.1.1 q.1.2 q.2 .revocable) ∗
      authHistFrozen { x0.2.ρ with wait := w0.γw }.kv γz hs ∗
      srvReqLogLb { x0.2.ρ with wait := w0.γw }.raft Lset ∗
      srvRLogLb { x0.2.ρ with wait := w0.γw }.raft Lc ∗
      □ (∀ ρ' : ReqNames, ⌜etcdstart.sameCluster x0.2.ρ ρ'⌝ -∗
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu ρ'.rd.kv Q)) ⊢
      [∗list] q ∈ l, barrierPre (bArg γz hs Lset Lc r Q q) := by
  induction l with
  | nil => iintro _; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons q l ih =>
    iintro ⟨Hs, #Hfz, #Hllb, #HLc, #HQ⟩
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨#Hq, Hs⟩
    iapply BigSepL.bigSepL_cons.2
    obtain ⟨hsc, hpe⟩ := hl q List.mem_cons_self
    isplitr [Hs]
    · iunfold srvdW at Hq
      iunfold srvdAt at Hq
      icases Hq with ⟨%HR, #Hrd, -, #HKV, -, #HAu, -, -, -⟩
      have hon : q.2.E.authOn = true := by unfold apply.AEnv.authOn; rw [HR.1]; rfl
      iunfold barrierPre
      isplitl []
      · ipureintro; exact ⟨hpe, HR.1⟩
      iframe HAu HKV
      ihave #Hrd' : isServerReadM q.2.E.authOn q.1.1 q.2.E q.1.2.2.ρ.rd $$ []
      · rw [hon]; iexact Hrd
      iframe Hrd'
      ihave #Hfzq := authHistFrozen_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw }
        hsc γz hs $$ Hfz
      ihave #Hllbq := srvReqLogLb_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw }
        hsc Lset $$ Hllb
      ihave #HLcq := srvRLogLb_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw }
        hsc Lc $$ HLc
      iframe Hfzq Hllbq HLcq
      isplitl []
      · ipureintro
        rw [admStates_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw } hsc,
          srvAuthAtLog_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw } hsc]
        exact hadm
      isplitl []
      · ipureintro
        rw [srvAuthAtLog_same { x0.2.ρ with wait := w0.γw } { q.1.2.2.ρ with wait := q.2.γw } hsc]
        exact hlc
      imodintro
      iapply HQ
      ipureintro; exact hsc
    · iapply (ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')))
      iframe Hs
      iframe #

end barriers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 10000 in
theorem run.wp_proof
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_SetUp : etcd_auth.SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_barriers : barriers.spec (GF := GF) (hG := hG))
    (wp_grantPut : grantPut.spec (GF := GF) (hG := hG))
    (wp_noAuth : noAuth.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_absent : absent.spec (GF := GF) (hG := hG))
    (wp_foreign : foreign.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_WithLease : WithLease.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF))
    (hlaw : lessor_keys_of_read_stmt (GF := GF)) :
    run.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC srvsl msl lg ss xs x0 γn σ0 hx0 hxl Hpe Htb HLv Hrb48 Hbuq Hrf Hms hAs hc0
    hlog hlm hLp hns hsc hx
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  have hk1 : 1 ≤ xs.length := by
    cases xs with
    | nil => simp at hx0
    | cons _ _ => simp
  have hlogx : ∀ x ∈ xs, x.2.ρ.rd.kv.log0 = [[], []] := fun x hx => by rw [(hsc x hx).2.2.2.1, hlog]
  wp_start as ⟨#Hlgz, Hss, #Hmsl, Htok, Hcfree, Hups, HkV, Hview⟩
  -- the driver's cell, over member 0's KV state (before the set-up)
  imod (cell_alloc x0.2.ρ.rd.kv σ0 hx) $$ HkV with ⟨%γc, #Hinv, #Hi0, #Hp0, #Hg0, #Hd0, Ha, Hids⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hmsll := ownSlice_len $$ Hmsl
  have hkl : uint.nat msl.len = xs.length := by have := Hmsll.1; simp at this; word
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z msl.len := by
    have := Hmsll.1; simp at this; constructor <;> word
  have hm0 : (xs.map (·.1))[(sint.Z (W64 0)).toNat]? = some x0.1 := by
    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.getElem?_map, hx0]; rfl
  have hk0 : ¬ (uint.Z msl.len = 0) := by word
  -- (for `run`'s indexing) u's member `1 % k`, v's member `2 % k`
  have hmodZ := fun c hc => mod_len_sint msl.len xs.length c hkl (by omega) hxl hc
  obtain ⟨xu, hxu⟩ : ∃ x, xs[1 % xs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))⟩
  obtain ⟨xv, hxv⟩ : ∃ x, xs[2 % xs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))⟩
  have hmsZ : sint.Z msl.len = (xs.length : Int) := by have := Hmsll.1; simp at this; word
  have hu : sint.Z (W64 1 % msl.len) = ((1 % xs.length : Nat) : Int) := hmodZ 1 (by omega)
  have hv : sint.Z (W64 2 % msl.len) = ((2 % xs.length : Nat) : Int) := hmodZ 2 (by omega)
  have Hbu : 0 ≤ sint.Z (W64 1 % msl.len) ∧ sint.Z (W64 1 % msl.len) < sint.Z msl.len := by
    rw [hu, hmsZ]; have := Nat.mod_lt 1 (by omega : xs.length > 0); omega
  have Hbv : 0 ≤ sint.Z (W64 2 % msl.len) ∧ sint.Z (W64 2 % msl.len) < sint.Z msl.len := by
    rw [hv, hmsZ]; have := Nat.mod_lt 2 (by omega : xs.length > 0); omega
  have hmu : (xs.map (·.1))[(sint.Z (W64 1 % msl.len)).toNat]? = some xu.1 := by
    rw [hu, Int.toNat_natCast, List.getElem?_map, hxu]; rfl
  have hmv : (xs.map (·.1))[(sint.Z (W64 2 % msl.len)).toNat]? = some xv.1 := by
    rw [hv, Int.toNat_natCast, List.getElem?_map, hxv]; rfl
  imod ownSlice_persist _ _ _ $$ Hss with #Hss
  (try wp_auto)
  -- the serve loop: `for j, m := range ms { if err := Serve(srvs[j], m.Client); err != nil { return
  -- Failed } }`, the thread token from member to member
  ihave IH : (∃ (n jv : w64) (mv : GMember) (ws : List (Wit GF)),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "m" ∷ m_ptr ↦ mv ∗ "Htok" ∷ threadTok ∗
      "Hups" ∷ ([∗list] s; x ∈ ss.drop (sint.nat n); xs.drop (sint.nat n),
        (threadTok -∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s x.2.ρ x.2.E lg γn x.2.id γa .revocable)) ∗
      "Hcfree" ∷ ([∗list] x ∈ xs.drop (sint.nat n), netAddrFree (GF := GF) x.1.Client') ∗
      "#Hsv" ∷ ([∗list] q ∈ ((ss.zip xs).take (sint.nat n)).zip ws, srvdW q.1.1 q.1.2 q.2 .revocable) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ ws.length = sint.nat n⌝ : IProp GF)
      $$ [i j m Htok Hups Hcfree]
  · iexists W64 0, _, _, []
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.drop_zero, List.take_zero, List.zip_nil_left]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega, rfl⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem ss (sint.nat n) as sj
    list_elem xs (sint.nat n) as xj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    have Hbs : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len := ⟨Hn.1, by have := Hssl.1; word⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    simp only [Hbs, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index srvsl (sint.Z n) _ _ sj Hbs.1 $$ [Hss] as -
    · iframe #; ipureintro; rw [hnz]; exact Hsj_lookup
    (try wp_auto)
    -- the member's `memberUpOn`, the token given to it
    isimp only [drop_cons_of_getElem? ss _ sj Hsj_lookup, drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hups
    ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
    icases Hups with ⟨Hupj, Hups⟩
    ihave ⟨%γa, Hupj⟩ := Hupj $$ Htok
    isimp only [drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hcfree
    ihave Hcfree := BigSepL.bigSepL_cons.1 $$ Hcfree
    icases Hcfree with ⟨Hcj, Hcfree⟩
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    wp_apply (serve_member wp_Serve wp_BcryptCost hP hR sj lg xj.1.Client' xj.2.ρ xj.2.E γn xj.2.id γa
        .revocable Htb HLv Hrb48 Hbuq Hrf Hms (hlogx xj hxj) (fun _ => ⟨hlm xj hxj, hLp⟩)) $$ [Hcj Hupj] as %serr Hs
    · iframe; iframe #
    icases Hs with (%Hserr | ⟨%Hserr, Htok, %E, %γw, %cid, %mid, %R, %HR, #Hrd, #Htls,
      #HKV, #HSA, #HAu, #HWF, #Htag, #HLS⟩)
    · cases serr with
      | nil => exact absurd rfl Hserr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hserr
    (try wp_auto)
    have hzj : (ss.zip xs)[sint.nat n]? = some (sj, xj) :=
      List.getElem?_zip_eq_some.2 ⟨Hsj_lookup, Hxj_lookup⟩
    have htl : ((ss.zip xs).take (sint.nat n)).length = ws.length := by
      rw [List.length_take, List.length_zip, Hupl, Hn.2.2]; omega
    have hzz : ((ss.zip xs).take (sint.nat n + 1)).zip (ws ++ [⟨γa, E, γw, cid, mid, R⟩]) =
        ((ss.zip xs).take (sint.nat n)).zip ws ++ [((sj, xj), ⟨γa, E, γw, cid, mid, R⟩)] := by
      rw [List.take_add_one, hzj, Option.toList_some, List.zip_append htl]; rfl
    ihave #Hsv' : [∗list] q ∈ ((ss.zip xs).take (sint.nat n + 1)).zip (ws ++ [⟨γa, E, γw, cid, mid, R⟩]),
        srvdW q.1.1 q.1.2 q.2 .revocable $$ []
    · rw [hzz]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold srvdW
      iunfold srvdAt
      iframe #
      ipureintro; exact HR
    iclear Hsv
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, n, xj.1, ws ++ [⟨γa, E, γw, cid, mid, R⟩]
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega, by simp [Hn.2.2]⟩
  -- every member served
  have hnk : sint.nat n = xs.length := by have := Hmsll.1; simp at this; word
  have hwl : ws.length = xs.length := by rw [Hn.2.2, hnk]
  ihave #Hsv : [∗list] q ∈ (ss.zip xs).zip ws, srvdW q.1.1 q.1.2 q.2 .revocable $$ []
  · iExactEq Hsv; rw [hnk, List.take_of_length_le (by simp [Hupl])]
  iclear Hups Hcfree
  -- `a0 := ms[0].Client`, `au := ms[1%k].Client`, `av := ms[2%k].Client`
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hb0.1 hm0 $$ Hmsl with ⟨#Hm0, -⟩
  iStructNamedSuffix Hm0 "_m0"
  (try wp_auto)
  simp only [hk0, ↓reduceIte]
  (try wp_auto)
  simp only [Hbu, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hbu.1 hmu $$ Hmsl with ⟨#Hmu, -⟩
  iStructNamedSuffix Hmu "_mu"
  (try wp_auto)
  simp only [hk0, ↓reduceIte]
  (try wp_auto)
  simp only [Hbv, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hbv.1 hmv $$ Hmsl with ⟨#Hmv, -⟩
  iStructNamedSuffix Hmv "_mv"
  (try wp_auto)
  -- member 0's served facts (its witnesses `w0`), u's member's and v's member's witnesses
  have hx0m : x0 ∈ xs := List.mem_of_getElem? hx0
  have hxum : xu ∈ xs := List.mem_of_getElem? hxu
  have hxvm : xv ∈ xs := List.mem_of_getElem? hxv
  have hzl : ((ss.zip xs).zip ws).length = xs.length := by simp [Hupl, hwl]
  have hgz : ∀ (i : Nat) (x : GMember × MemberG GF), xs[i]? = some x →
      ∃ s w, ((ss.zip xs).zip ws)[i]? = some ((s, x), w) := by
    intro i x hx
    have hi : i < xs.length := (List.getElem?_eq_some_iff.1 hx).1
    obtain ⟨s, hs⟩ : ∃ s, ss[i]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw⟩ : ∃ w, ws[i]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨s, w, List.getElem?_zip_eq_some.2 ⟨List.getElem?_zip_eq_some.2 ⟨hs, hx⟩, hw⟩⟩
  obtain ⟨s0, w0, hy0⟩ := hgz 0 x0 hx0
  obtain ⟨su, wu, hyu⟩ := hgz _ xu hxu
  obtain ⟨sv, wv, hyv⟩ := hgz _ xv hxv
  ihave #H0' := BigSepL.bigSepL_lookup hy0 $$ Hsv
  ihave #H0 : srvdW s0 x0 w0 .revocable $$ []
  · iexact H0'
  iclear H0'
  iunfold srvdW at H0
  iunfold srvdAt at H0
  icases H0 with ⟨%HR₁, #Hrd₁, #Htls₁, #HKV₁, #HSA₁, #HAu₁, #HWF₁, #Htag₁, #HLS₁⟩
  -- `NewClient(a1, lg)`: the client with no user name, at member 0
  wp_apply (wp_NewClient x0.1.Client' lg (akV x0.1.Client' x0.2.ρ w0.R) (Hpe x0 hx0m) Htb31) as %cl %cerr Hcl
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hctk⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- `SetUp(cli)` through member 0
  ihave #Hsau : iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      kvOpAu1 x0.2.ρ.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) $$ []
  · iintro !> %k %hk
    ihave #H := cell_setupAu x0.2.ρ.rd.kv γc k hk $$ Hinv
    iexact H
  ihave #Hput : isGrpcRpcMd x0.1.Client' go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid) $$ []
  · iunfold akKVOn at HKV₁
    icases HKV₁ with ⟨#H, -, -, -⟩
    iexact H
  wp_apply (wp_SetUp cl x0.1.Client' (akV x0.1.Client' x0.2.ρ w0.R) s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid w0.γa HR₁.1
      (by show uint.Z x0.2.ρ.rd.kv.c0 ≤ uint.Z x0.2.ρ.rd.raft.ai0; rw [hc0]; word) hAs)
    $$ [Hview] as %ok Hok
  · iframe; iframe #
  cases ok
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %kpub, %rset, #Hfz, #Hllb, %Hadm, -, -, %Lc, #HLc,
    %HLcst⟩
  (try wp_auto)
  -- `barriers(ms, lg)`: each member's auth state fixed after the set-up
  have hlq : ∀ q ∈ (ss.zip xs).zip ws, etcdstart.sameCluster x0.2.ρ q.1.2.2.ρ ∧
      plainEndpoint q.1.2.1.Client' := by
    intro q hq
    have hx := List.of_mem_zip (List.of_mem_zip hq).1 |>.2
    exact ⟨hsc _ hx, Hpe _ hx⟩
  have hmsb : ∀ (Q : KVState → IProp GF), (xs.map (·.1)).map (·.Client') =
      (((ss.zip xs).zip ws).map (bArg γz hs Lset Lc rset Q)).map (·.addr) := by
    intro Q
    have h1 : ((ss.zip xs).zip ws).map Prod.fst = ss.zip xs :=
      List.map_fst_zip (by simp [Hupl, hwl])
    have h2 : (ss.zip xs).map Prod.snd = xs := List.map_snd_zip (by simp [Hupl])
    calc (xs.map (·.1)).map (·.Client') = (((((ss.zip xs).zip ws).map Prod.fst).map Prod.snd).map
          (·.1)).map (·.Client') := by rw [h1, h2]
      _ = _ := by simp only [List.map_map]; rfl
  ihave #Hbp1 : [∗list] b ∈ ((ss.zip xs).zip ws).map (bArg γz hs Lset Lc rset (fun _ => iprop(True))),
      barrierPre b $$ []
  · rw [BigSepL.bigSepL_map]
    iapply (barrierPre_all x0 w0 γz hs Lset Lc rset _ _ hlq Hadm HLcst)
    iframe #
    iintro !> %ρ' %_
    ileft; ipureintro; rfl
  wp_apply (wp_barriers msl lg (xs.map (·.1)) _ (hmsb _) (by omega) hAs) as %okb Hb1
  · iframe #
  icases Hb1 with (%Hb | ⟨%Hb, #Hbq1⟩) <;> subst Hb
  · wp_auto
    iapply HΦ; ipureintro; right; rfl
  wp_auto
  ihave #Hbq1' : [∗list] q ∈ (ss.zip xs).zip ws,
      barrierPost (bArg γz hs Lset Lc rset (fun _ => iprop(True)) q) $$ []
  · rw [← BigSepL.bigSepL_map (fun q => bArg γz hs Lset Lc rset (fun _ => iprop(True)) q)]
    iexact Hbq1
  iclear Hbq1
  ihave #F0 := BigSepL.bigSepL_lookup hy0 $$ Hbq1'
  iunfold barrierPost at F0
  icases F0 with ⟨⟨%i₁, #Hfix₁⟩, -⟩
  ihave #Hu' := BigSepL.bigSepL_lookup hyu $$ Hsv
  ihave #Hu : srvdW su xu wu .revocable $$ []
  · iexact Hu'
  iclear Hu'
  iunfold srvdW at Hu
  iunfold srvdAt at Hu
  icases Hu with ⟨%HR₂, #Hrd₂, #Htls₂, #HKV₂, -, #HAu₂, #HWF₂, #Htag₂, #HLS₂⟩
  ihave #Fu := BigSepL.bigSepL_lookup hyu $$ Hbq1'
  iunfold barrierPost at Fu
  icases Fu with ⟨⟨%i₂, #Hfix₂⟩, -⟩
  ihave #Hv' := BigSepL.bigSepL_lookup hyv $$ Hsv
  ihave #Hv : srvdW sv xv wv .revocable $$ []
  · iexact Hv'
  iclear Hv'
  iunfold srvdW at Hv
  iunfold srvdAt at Hv
  icases Hv with ⟨%HR₃, #Hrd₃, #Htls₃, #HKV₃, -, #HAu₃, #HWF₃, #Htag₃, #HLS₃⟩
  ihave #Fv := BigSepL.bigSepL_lookup hyv $$ Hbq1'
  iunfold barrierPost at Fv
  icases Fv with ⟨⟨%i₃, #Hfix₃⟩, -⟩
  -- the clients: root at member 0, u at member `1 % k`, v at member `2 % k`, the one with no token at
  -- member `1 % k`
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hall : client.ctxErrClientAll (GF := GF) $$ []
  · ihave #Hw := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hw
    iunfold client.ctxErrClientAll
    iexact Hw
  wp_apply (wp_newUserClient x0.1.Client' go!"root" go!"root-pw" lg (akV x0.1.Client' x0.2.ρ w0.R)
      (fun t => auth.tokIssued w0.γa t go!"root") (Hpe x0 hx0m) (by omega) (by unfold strsSizeOk; decide))
    as %rcl %rerr Hrc
  · iframe #
    iapply (client.authTokReg_of _ _ _ w0.γa)
    iexact HAu₁
  icases Hrc with (⟨%Hrerr, #Hrnc, #Hrtk⟩ | %Hrfail)
  rotate_left
  · obtain ⟨Hrerr, -⟩ := Hrfail
    cases rerr with
    | nil => exact absurd rfl Hrerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hrerr
  wp_auto
  wp_apply (wp_newUserClient xu.1.Client' go!"u" go!"u-pw" lg (akV xu.1.Client' xu.2.ρ wu.R)
      (fun t => auth.tokIssued wu.γa t go!"u") (Hpe xu hxum) (by omega) (by unfold strsSizeOk; decide))
    as %ucl %uerr Huc
  · iframe #
    iapply (client.authTokReg_of _ _ _ wu.γa)
    iexact HAu₂
  icases Huc with (⟨%Huerr, #Hunc, #Hutk⟩ | %Hufail)
  rotate_left
  · obtain ⟨Huerr, -⟩ := Hufail
    cases uerr with
    | nil => exact absurd rfl Huerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Huerr
  wp_auto
  wp_apply (wp_newUserClient xv.1.Client' go!"v" go!"v-pw" lg (akV xv.1.Client' xv.2.ρ wv.R)
      (fun t => auth.tokIssued wv.γa t go!"v") (Hpe xv hxvm) (by omega) (by unfold strsSizeOk; decide))
    as %vcl %verr Hvc
  · iframe #
    iapply (client.authTokReg_of _ _ _ wv.γa)
    iexact HAu₃
  icases Hvc with (⟨%Hverr, #Hvnc, #Hvtk⟩ | %Hvfail)
  rotate_left
  · obtain ⟨Hverr, -⟩ := Hvfail
    cases verr with
    | nil => exact absurd rfl Hverr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hverr
  wp_auto
  wp_apply (wp_NewClient xu.1.Client' lg (akV xu.1.Client' xu.2.ρ wu.R) (Hpe xu hxum) Htb31) as %bcl %berr Hbc
  · iframe #
  icases Hbc with (⟨%Hberr, #Hbnc, #Hbtk⟩ | %Hbfail)
  rotate_left
  · obtain ⟨Hberr, -⟩ := Hbfail
    cases berr with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hberr
  wp_auto
  sorry

end proof

end etcd_authlease
end EtcdGrove
end Perennial
