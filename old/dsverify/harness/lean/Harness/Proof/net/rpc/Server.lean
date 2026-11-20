/-
The server side of the lab's `net/rpc` model (`server.go`): `Server.call`, `serve`, `ServeConn`
and `ServeHTTP`, and the protocol proof: a server whose registrations serve address `a`
(`srvServes`) keeps `a`'s protocol on every connection it serves (`ServerGhost.lean`).

* `Server.call.spec`: `s.call(sm, body)` for a request whose service is registered at `s`: the
  reply, the message and the continuation `Ψ reply msg`, for every message (the service is
  registered and `lastDot` finds the dot, as the deposit says, and `rcvrOk` rules out a missing
  method, so `call` returns the dispatch's reply and message).
* `wp_serve`: the goroutine answering request `k` of a connection: it calls the registered
  receiver, records the answer and its continuation in the connection's invariant (`answer`)
  and, under the connection's `connWriter` lock (`cwInv`), writes its response frame
  (`resp_next`), or, once a write failed, nothing.
* `wp_ServeConn`: on the acceptor's end of a connection to `a` with `rpcHead` read and
  `connectedBytes` written, reads frames until one fails or does not decode, forking `serve`
  for each request (`req_parse`, `claim_role`, `take_req`), then closes the connection.
* `srv_handlerOk`: `s`'s `ServeHTTP` is a `handlerOk` handler of `rpcPath` for `a`'s protocols:
  it hijacks the connection, writes `connectedBytes` (closing on failure) and runs `ServeConn`.

The proofs take the specs of `wire.go` (`WireSpec.lean`) and of `(*response).Hijack`
(`http/Proto.lean`) as hypotheses.
-/
module

public import Harness.Proof.net.rpc.ServerDefs
public import Harness.Proof.net.rpc.ServerGhost
public import Harness.Proof.net.TCPConn__Close
public import Harness.Proof.net.TCPConn__Write
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]

/-- `s.call(sm, body)` for a request whose service is registered at `s`: with the dispatch's
predicate transformer for a continuation that needs the method found, the reply, the message
and `Ψ` of them (for every message). -/
abbrev Server.call.spec : Prop :=
  ∀ (s : Loc) (sm : GoString) (body : GoSlice) (dq : DFrac) (bs : List w8) (svc m : GoString)
    (rcvr : GoInterface) (Ψ : List w8 → GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗ kitCodecOk (GF := GF) ∗
      ⌜splitSM sm = some (svc, m)⌝ ∗ svcReg s svc rcvr ∗ body ↦*{dq} bs ∗
      RpcCodec.call rcvr m bs (fun reply msg found =>
        iprop(⌜found = true⌝ ∗ Ψ reply msg)) }}
    (App (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"call")) (Val #sm)) (Val #body))
  {{ (rep : GoSlice) (msg : GoString), RET (PairV #rep #msg);
      ∃ rbs : List w8, rep ↦* rbs ∗ Ψ rbs msg }}

set_option goose.wp.extras true

theorem Server.call.wp_proof (wp_lastDot : lastDot.spec (GF := GF) (hG := hG)) :
    Server.call.spec (GF := GF) (hG := hG) := by
  intro s sm body dq bs svc m rcvr Ψ
  wp_start as ⟨#Hset, #Hok, %Hsplit, #Hreg, Hbody, Hcall⟩
  ihave ⟨-, #Hsync, -, -⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_apply wp_lastDot as %dot %Hdot
  unfold splitSM at Hsplit
  rcases hj : lastDotIdx sm with _ | j
  · rw [hj] at Hsplit; cases Hsplit
  rw [hj] at Hsplit Hdot
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at Hsplit
  obtain ⟨hsvc, hm⟩ := Hsplit
  obtain ⟨hd1, hd2⟩ := Hdot
  have hjlt : j < sm.length := by
    unfold lastDotIdx at hj
    have := List.mem_of_find?_eq_some hj
    simpa using this
  wp_if_destruct
  · exfalso; simp at *; omega
  have hdn : sint.nat dot = j := by show (sint.Z dot).toNat = j; rw [hd2]; simp
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z dot ∧
    sint.Z dot ≤ (sm.length : Int) by simp; omega)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hsmlen
  have hd1' : sint.Z (dot + W64 1) = j + 1 := by
    have : (j : Int) + 1 < 2 ^ 63 := by omega
    word
  have hlen' : sint.Z (W64 (sm.length : Nat)) = sm.length := by word
  have hdn' : sint.nat (dot + W64 1) = j + 1 := by
    show (sint.Z (dot + W64 1)).toNat = j + 1; rw [hd1']; omega
  have hln : sint.nat (W64 (sm.length : Nat)) = sm.length := by
    show (sint.Z (W64 (sm.length : Nat))).toNat = sm.length; rw [hlen']; simp
  rw [if_pos (by rw [hd1', hlen']; omega)]
  simp only [hdn, hdn', hln, Nat.sub_zero, List.drop_zero, hsvc, hm]
  have hmt : List.take (sm.length - (j + 1)) m = m := by
    rw [← hm]; exact List.take_of_length_le (by simp)
  rw [hmt]
  unfold svcReg
  icases Hreg with ⟨%γ, #Hsg, #Hel⟩
  unfold isServerG
  iNamed Hsg
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (∃ mm : GMap GoString GoInterface, ownMap mp (DFrac.own 1) mm ∗
    ghostMapAuth γ 1 mm : IProp GF) $$ [Hinv]
  · unfold servicesInv; iexact Hinv
  icases Hinv with ⟨%mm, Hmap, Hauth⟩
  icombine Hel Hauth gives %Hlk
  wp_apply (wp_map_lookup2 go.string (go.InterfaceType []) mp mm svc (DFrac.own 1)) $$ Hmap
    as Hmap
  rw [show mm !! svc = some rcvr from Hlk]
  simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
  wp_apply sync.Mutex.Unlock.wp_proof _ (servicesInv mp γ) $$ [$Hsync $Hmu $Hlocked Hmap Hauth]
  · unfold servicesInv; iexists _; iframe Hmap Hauth
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns
  icases Hfns with ⟨-, -, -, #HfC, -⟩
  unfold kitCodecOk
  icases Hok with ⟨-, -, -, #HcOk⟩
  unfold callOk
  wp_auto
  ihave Hc2 := HcOk $$ %rcvr %m %body %dq %bs
    %(fun reply msg found => iprop(⌜found = true⌝ ∗ Ψ reply msg))
  wp_apply Hc2 $$ Hbody Hcall as %rep %rbs %msg %found Hrep HΨ
  icases HΨ with ⟨%Hfound, HΨ⟩
  subst Hfound
  wp_auto
  iapply HΦ
  iexists rbs
  iframe Hrep HΨ
/-- The run of request `k` of connection `cid` (to address `a`): see the file header. -/
theorem wp_serve (wp_lastDot : lastDot.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_encodeMsg : encodeMsg.spec (GF := GF) (hG := hG))
    (s : Loc) (W : RpcWorld GF) (a : GoString) (cid : w64) (γ : RpcConnNames) (σ : GName)
    (cv : GoInterface) (w : Loc) (k : Nat) (L : List RpcReq) (r : RpcReq) (body : GoSlice)
    (hr : L[k]? = some r) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ srvServes s W a ∗ connIface cv cid true ∗
        sync.isMutex (structFieldRef net.rpc.connWriter go!"mu" w) (cwInv W a cid σ w) ∗
        isRpcConn W a cid γ ∗ monoListLbOwn γ.reqs L ∗ reqDeposit W a r ∗
        ghostMapElem γ.ans k (DFrac.own 1) (none : Option (GoString × List w8)) ∗
        ghostMapElem σ k (DFrac.own 1) () ∗ body ↦* r.body }}
      (App (App (App (App (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"serve"))
        (Val #cv)) (Val #w)) (Val #r.seq)) (Val #r.sm)) (Val #body))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hset, #Hok, #Hsrv, #Hcv, #Hmu, #Hc, #Hlb, Hdep, Hans, Hσ, Hbody⟩
  ihave ⟨-, #Hsync, #Hnet, -⟩ := deps_of_pkg $$ Hpkg
  unfold reqDeposit
  icases Hdep with ⟨%svc, %m, %S, %Φr, %HSS, #Hsaved, HS⟩
  unfold srvServes
  icases Hsrv $$ %svc %S %HSS.2 with ⟨%rcvr, #Hreg, #HrOk⟩
  unfold rcvrOk
  ihave Hcall := HrOk $$ %m %r.body %Φr HS
  wp_auto
  wp_apply Server.call.wp_proof wp_lastDot $$ [$Hpkg $Hset $Hok $Hreg $Hbody $Hcall]
    as %rep %msg ⟨%rbs, Hrep, HΦr⟩
  · ipureintro; exact HSS.1
  ihave #Hinv := isRpcConn_inv W a cid γ $$ Hc
  iapply fupd_wp
  imod answer W a cid γ k L r msg rbs hr ⊤ (by simp) $$ Hinv Hans Hlb [HΦr] with #HansP
  · unfold replyEscrow
    iexists Φr
    iframe Hsaved HΦr
  imodintro
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hcw⟩
  ihave Hcw : (∃ broken : Bool, structFieldRef net.rpc.connWriter go!"broken" w ↦ broken ∗
    (if broken then iprop(True) else
      ∃ Wb : List w8, sendTok cid true (respProto W a) Wb ∗ respDone W a cid σ Wb) : IProp GF)
    $$ [Hcw]
  · unfold cwInv; iexact Hcw
  icases Hcw with ⟨%broken, Hbr, Hrest⟩
  wp_auto
  cases broken
  · simp only [Bool.false_eq_true, ite_false]
    icases Hrest with ⟨%Wb, Hsend, Hdone⟩
    wp_auto
    wp_apply wp_encodeMsg $$ [$Hpkg $Hrep] as %pl ⟨Hpl, Hrep⟩
    ihave %Hpllen := ownSlice_len _ _ _ $$ Hpl
    have hlen : (msgOf r.seq msg rbs).length < 2 ^ 63 := by
      rw [Hpllen.1]; show (sint.Z pl.len).toNat < 2 ^ 63
      have := Hpllen.2; word
    iapply fupd_wp
    imod resp_next W a cid γ σ Wb k L r msg rbs hr hlen ⊤ (by simp) $$ Hc Hdone Hσ HansP Hlb
      with ⟨#HP, Hdone⟩
    imodintro
    unfold connIface
    icases Hcv with ⟨%c, %Hcveq, #Hcc⟩
    wp_apply wp_writeFrame $$ [$Hnet $Hsend $HP $Hpl] as %err ⟨%n, %Hn, -, Hsend, Hpl⟩
    · unfold connIface; iexists c; iframe Hcc; ipureintro; exact Hcveq
    subst Hcveq
    rcases err with ei | _
    · wp_auto
      wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hcc] as %err2 -
      wp_apply sync.Mutex.Unlock.wp_proof _ (cwInv W a cid σ w) $$ [$Hsync $Hmu $Hlocked Hbr]
      · unfold cwInv; iexists true; iframe Hbr; simp only [ite_true]; itrivial
      iapply HΦ; itrivial
    · rw [Hn.2.1 rfl, List.take_length] at *
      wp_auto
      wp_apply sync.Mutex.Unlock.wp_proof _ (cwInv W a cid σ w)
        $$ [$Hsync $Hmu $Hlocked Hbr Hsend Hdone]
      · unfold cwInv; iexists false; iframe Hbr; simp only [Bool.false_eq_true, ite_false]
        iexists _; iframe Hsend Hdone
      iapply HΦ; itrivial
  · wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (cwInv W a cid σ w) $$ [$Hsync $Hmu $Hlocked Hbr]
    · unfold cwInv; iexists true; iframe Hbr; simp only [ite_true]; itrivial
    iapply HΦ; itrivial

/-- `s.ServeConn(cv)` on the acceptor's end `cid` of a connection to an rpc address `a` whose
services `s` serves: see the file header. -/
theorem wp_ServeConn (wp_lastDot : lastDot.spec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_encodeMsg : encodeMsg.spec (GF := GF) (hG := hG))
    (wp_decodeMsg : decodeMsg.spec (GF := GF) (hG := hG))
    (s : Loc) (W : RpcWorld GF) (a : GoString) (cv : GoInterface) (cid : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ srvServes s W a ∗ connIface cv cid true ∗
        recvTok cid true (reqProto W a) rpcHead ∗
        sendTok cid true (respProto W a) connectedBytes ∗ connFresh cid true }}
      (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"ServeConn")) (Val #cv))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hset, #Hok, #Hsrv, #Hcv, Hrecv, Hsend, Hfr⟩
  ihave ⟨-, #Hsync, #Hnet, -⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  irename «$r0» => Hw
  generalize «$r0_ptr» = w at *
  icases typedPointsto_split _ _ _ $$ Hw with Hw
  simp only [TypedPointsto.typedPointstoDef]
  icases Hw with ⟨mu, broken, -⟩
  imod ghost_map_alloc_strong_empty (K := Nat) (V := Unit) (GF := GF)
    (fun _ => True) PredInfinite.true with ⟨%σ, -, Hσ⟩
  imod sync.init_Mutex (cwInv W a cid σ w) ⊤
      (structFieldRef net.rpc.connWriter go!"mu" w) $$ [mu] [broken Hsend] with #Hmu
  · iexact mu
  · inext; unfold cwInv; iexists false; iframe broken
    simp only [Bool.false_eq_true, ite_false]
    iexists connectedBytes; iframe Hsend
    unfold respDone; ileft; ipureintro; rfl
  ihave HI : (∃ (qs : List (List w8)) (Mσ : GMap Nat Unit),
      "Hrecv" ∷ recvTok cid true (reqProto W a) (rpcHead ++ framesOf qs) ∗
      "%Hqs" ∷ ⌜(∀ q ∈ qs, q.length < 2 ^ 63) ∧ ∀ i, (Mσ !! i).isSome → i < qs.length⌝ ∗
      "Hσ" ∷ ghostMapAuth σ 1 Mσ ∗
      "Hrole" ∷ ((⌜qs = []⌝ ∗ connFresh cid true) ∨
        ∃ γ : RpcConnNames, isRpcConn W a cid γ ∗ ghostVar γ.ctr (1 : Qp).half qs.length)
      : IProp GF) $$ [Hrecv Hσ Hfr]
  · iexists [], ∅
    simp only [framesOf_nil, List.append_nil]
    iframe Hrecv Hσ
    isplitr
    · ipureintro; simp
    ileft; iframe Hfr
  wp_for HI
  wp_apply wp_readFrame $$ [$Hnet $Hpkg $Hcv $Hrecv] as %p %err ⟨%data, Hrecv, Hres⟩
  icases Hres with (⟨%Herr, %pl, %Hpl, Hp⟩ | ⟨%Herr, -⟩)
  · subst Herr
    wp_auto
    wp_apply wp_decodeMsg $$ [$Hpkg $Hp] as %seq %sm %body %ok Hdec
    cases ok
    · wp_auto
      wp_for_post
      unfold connIface
      icases Hcv with ⟨%c, %Hcveq, #Hcc⟩
      subst Hcveq
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hcc] as %err2 -
      iapply HΦ; itrivial
    · simp only [ite_true]
      icases Hdec with ⟨%b, %Hb, Hbody⟩
      obtain ⟨hdata, hpl⟩ := Hpl
      obtain ⟨hplm, hsm⟩ := Hb
      subst hdata
      ihave Hrecv := req_parse W a cid qs pl Hqs.1 hpl $$ Hrecv
      icases Hrecv with ⟨Hrecv, %γ, %L, %r, #Hc, #Hlb, %HLr⟩
      obtain ⟨hr, hrm⟩ := HLr
      unfold reqMsg at hrm
      have hrsm : r.sm.length < 2 ^ 63 := by
        have := msgOf_length r.seq r.sm r.body
        rw [hrm] at this; omega
      rw [hplm] at hrm
      obtain ⟨hseq, hsmeq, hbeq⟩ := msgOf_inj hrsm hsm hrm
      subst hseq hsmeq hbeq
      ihave #Hinv := isRpcConn_inv W a cid γ $$ Hc
      iapply fupd_wp
      ihave Hctr : (|={⊤}=> ghostVar γ.ctr (1 : Qp).half qs.length : IProp GF) $$ [Hrole]
      · icases Hrole with (⟨%Hq, Hfr⟩ | ⟨%γ', #Hc', Hctr⟩)
        · subst Hq
          iapply claim_role W a cid γ ⊤ (by simp) $$ Hinv Hfr
        · ihave %Hg := isRpcConn_agree W a cid γ γ' $$ Hc Hc'
          subst Hg
          imodintro; iexact Hctr
      imod Hctr
      imod take_req W a cid γ qs.length L r hr ⊤ (by simp) $$ Hinv Hctr Hlb
        with ⟨Hctr, Hdep, Hans⟩
      have hσk : Mσ.lookup qs.length = none := by
        cases h : Mσ.lookup qs.length with
        | none => rfl
        | some v =>
          have := Hqs.2 qs.length (by show (Mσ.lookup qs.length).isSome = true; simp [h])
          omega
      imod ghost_map_insert qs.length () hσk $$ Hσ with ⟨Hσ, Htok⟩
      imodintro
      wp_auto
      wp_apply wp_fork $$ [Hdep Hans Htok Hbody]
      · wp_apply wp_serve wp_lastDot wp_writeFrame wp_encodeMsg s W a cid γ σ cv w qs.length L r
          body hr $$ [$Hpkg $Hset $Hok $Hsrv $Hcv $Hmu $Hc $Hlb $Hdep $Hans $Htok $Hbody]
        itrivial
      wp_for_post
      iframe
      iexists qs ++ [pl], Mσ.insert qs.length ()
      rw [framesOf_concat, ← List.append_assoc]
      iframe Hrecv Hσ
      isplitr
      · ipureintro
        refine ⟨fun q hq => ?_, fun i hi => ?_⟩
        · simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | hq
          · exact Hqs.1 q hq
          · subst hq; exact hpl
        · simp only [List.length_append, List.length_singleton]
          by_cases hik : i = qs.length
          · omega
          · have : (Mσ !! i).isSome := by
              rwa [GMap.lookup_insert_ne _ _ (Ne.symm hik)] at hi
            have := Hqs.2 i this
            omega
      iright
      iexists γ
      iframe Hc
      simp only [List.length_append, List.length_singleton]
      iexact Hctr
  · rcases err with ei | _
    · wp_auto
      wp_for_post
      unfold connIface
      icases Hcv with ⟨%c, %Hcveq, #Hcc⟩
      subst Hcveq
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hcc] as %err2 -
      iapply HΦ; itrivial
    · exfalso; exact Herr.1 rfl

/-- `s`'s `ServeHTTP` handles `rpcPath` of an rpc address `a` whose services `s` serves. -/
theorem srv_handlerOk (wp_lastDot : lastDot.spec (GF := GF) (hG := hG))
    (wp_readFrame : readFrame.spec (GF := GF) (hG := hG))
    (wp_writeFrame : writeFrame.spec (GF := GF) (hG := hG))
    (wp_encodeMsg : encodeMsg.spec (GF := GF) (hG := hG))
    (wp_decodeMsg : decodeMsg.spec (GF := GF) (hG := hG))
    (wp_Hijack : net.http.response.Hijack.spec (GF := GF) (hG := hG))
    (s : Loc) (W : RpcWorld GF) (a : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗ kitCodecOk (GF := GF) ∗
        srvServes s W a ⊢
      net.http.handlerOk ⟨go.GoType.PointerType Server.ty, #s⟩ rpcPath (reqBodyProto W a)
        (respProto W a) := by
  iintro ⟨#Hpkg, #Hset, #Hok, #Hsrv⟩
  unfold net.http.handlerOk
  imodintro
  iintro %w %req %c %cid %Φ #Hhttp Hw Hreq #Hc Hrecv Hsend Hfr HΦ
  ihave ⟨-, #Hsync, #Hnet, -⟩ := deps_of_pkg $$ Hpkg
  unfold net.http.respWriter
  icases Hw with ⟨%l, %Hweq, Hl⟩
  subst Hweq
  have hH : go.typeSetContains (go.GoType.PointerType net.http.response.ty)
      net.http.Hijacker.ty = true := by go_type_set
  rw [method_unfold]
  wp_auto
  simp only [hH, ↓reduceIte]
  wp_auto
  wp_apply wp_Hijack $$ [$Hhttp $Hl] as Hl
  rw [show (connected : val) = #connectedBytes from rfl]
  wp_apply wp_string_to_bytes connectedBytes as %sb ⟨Hsb, -⟩
  ihave #HP : (respProto W a cid ([] ++ connectedBytes) : IProp GF) $$ []
  · unfold respProto; ileft; ipureintro; simp
  wp_apply net.TCPConn.Write.wp_proof c cid true sb connectedBytes (DFrac.own 1) (respProto W a) []
    $$ [$Hnet $Hc $Hsend $HP $Hsb] as %n %err ⟨%k, %code, %Hk, Hsb, Hsend, -⟩
  rcases err with ei | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
    iapply HΦ
    unfold net.http.respWriterBack
    iexists l, _
    iframe Hl
    ipureintro; rfl
  obtain ⟨-, -, -, hk⟩ := Hk
  rw [hk rfl, List.take_length, List.nil_append] at *
  wp_auto
  ihave Hrecv : (recvTok cid true (reqProto W a) rpcHead : IProp GF) $$ [Hrecv]
  · unfold reqProto rpcHead; iexact Hrecv
  wp_apply wp_ServeConn wp_lastDot wp_readFrame wp_writeFrame wp_encodeMsg wp_decodeMsg s W a
    (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) cid
    $$ [$Hpkg $Hset $Hok $Hsrv $Hrecv $Hsend $Hfr]
  · unfold connIface; iexists c; iframe Hc; ipureintro; rfl
  iapply HΦ
  unfold net.http.respWriterBack
  iexists l, _
  iframe Hl
  ipureintro; rfl

end spec

end net.rpc

end Perennial
