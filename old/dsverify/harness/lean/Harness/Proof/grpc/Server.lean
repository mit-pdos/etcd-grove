/-
The server side of the lab's grpc model (`server.go`): `encode`, `Server.call` (the dispatch:
the registered handler runs on the decoded request, with a decoding function meeting `decOk`),
`Server.handle` (the goroutine of one call: run it, cancel its context, write its answer under
the connection's lock unless a write failed), `Server.serveConn` (the reader of a connection:
calls fork `handle` with a fresh cancelable context, cancellations cancel it) and `Server.Serve`
(the accept loop, which returns only with an error).

The connection protocol proof is `ServerGhost.lean`'s. The proofs take the wire specs
(`Wire.lean`), the `status` specs (`StatusSpec.lean`) and the protobuf model's specs
(`Pb.lean`) as hypotheses where the rpc model's proofs do, and Perennial's `context` results.
-/
module

public import Harness.Proof.grpc.ServerDefs
public import Harness.Proof.grpc.ServerGhost
public import Harness.Proof.grpc.Status
public import Harness.Proof.net.TCPConn__Close
public import Harness.Proof.net.TCPListener__Accept
public import Harness.Proof.net.TCPListener__Close
public import Perennial.Proof.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn
open google_golang_org.protobuf.proto (PbCodec PbKit codecSet kitCodecOk)
open google_golang_org.grpc.status (handlerErr statusErrOf isStatus)
open net.rpc (frameOf framesOf connIface errAny)

namespace google_golang_org.grpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [google_golang_org.grpc.Assumptions]
variable [google_golang_org.protobuf.reflect.protoreflect.Assumptions]
variable [google_golang_org.protobuf.proto.Assumptions]
variable [google_golang_org.grpc.codes.Assumptions] [google_golang_org.grpc.status.Assumptions]
variable [context.Assumptions] [fmt.Assumptions]
variable [PbKit] [PbCodec GF]

/-- `encode(msg)`: a nil message is the empty encoding; another is the codec's, or a status
error (`Internal`). -/
abbrev encode.spec : Prop :=
  ∀ (msg : GoInterface) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗
      ((⌜msg = interface.nil⌝ ∗ Ψ (some [])) ∨ (⌜msg ≠ interface.nil⌝ ∗ PbCodec.marshal msg Ψ)) }}
    (App (Val (@! google_golang_org.grpc.encode)) (Val #msg))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err);
      (⌜err = interface.nil⌝ ∗ ∃ bs, b ↦* bs ∗ Ψ (some bs)) ∨
      (⌜err ≠ interface.nil⌝ ∗ (∃ c m, statusErrOf err c m) ∗ Ψ none) }}

set_option goose.wp.extras true

theorem encode.wp_proof : encode.spec (GF := GF) (hG := hG) := by
  intro msg Ψ
  wp_start as ⟨#Hset, #Hok, Hm⟩
  ihave ⟨-, -, -, -, -, #Hst, #Hpb⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  icases Hm with (⟨%Hnil, HΨ⟩ | ⟨%Hnn, Hm⟩)
  · subst Hnil
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists []
    iframe HΨ
    iapply ownSlice_nil
  · rcases msg with i | _
    · wp_auto
      wp_apply google_golang_org.protobuf.proto.MarshalValue.wp_proof $$ [$Hpb $Hset $Hok $Hm]
        as %s %err Hr
      unfold google_golang_org.protobuf.proto.marshalPost
      icases Hr with (⟨%He, %bs, Hs, HΨ⟩ | ⟨%He, -, HΨ⟩)
      · subst He
        wp_auto
        iapply HΦ
        ileft
        isplitr
        · ipureintro; rfl
        iexists bs
        iframe
      · rcases err with ei | _
        · wp_auto
          wp_apply status.Error.wp_proof $$ [$Hst] as %e He
          iapply HΦ
          iright
          unfold status.errPost
          icases He with (%Hc | #He)
          · exfalso; exact absurd Hc.1 (by decide)
          ihave %Hne : ⌜e ≠ interface.nil⌝ $$ [He]
          · unfold statusErrOf
            icases He with ⟨%e0, %s0, %Hh, -⟩
            ipureintro; rw [Hh.1]; simp [interface.mkOk]
          iframe HΨ
          isplitr
          · ipureintro; exact Hne
          iexists _, _
          iexact He
        · exact absurd rfl He
    · exact absurd rfl Hnn

/-- What a call's run returns: the code, the message and the reply bytes, with the
continuation of the reply when the code is OK. -/
def callPost (Φ : List w8 → IProp GF) (code : w64) (rep : GoSlice) : IProp GF :=
  iprop(⌜code = W64 0 ∨ uint.Z code < 2 ^ 32⌝ ∗
    ∃ rbs : List w8, rep ↦* rbs ∗ (if code = W64 0 then Φ rbs else iprop(True)))

/-- `s.call(ctx, fm, body)` for a call to a method of `a` with spec `S` and the caller's deposit
`S bs Φ`, on a server for `a`. -/
abbrev Server.call.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (W : GrpcWorld GF) (a : GoString) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (fm : GoString) (body : GoSlice) (bs : List w8)
    (S : UnarySpec GF) (Φ : List w8 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ isServer s γ W a ∗ context.isContext ctx cd ∗
      ⌜W.MS a fm = some S⌝ ∗ body ↦*□ bs ∗ S bs Φ }}
    (App (App (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"call"))
      (Val #(interface.ok ctx))) (Val #fm)) (Val #body))
  {{ (code : w64) (msg : GoString) (rep : GoSlice), RET (PairV (PairV #code #msg) #rep);
      callPost Φ code rep }}

theorem callPost_err (Φ : List w8 → IProp GF) (code : w64) (h : code ≠ W64 0)
    (hb : uint.Z code < 2 ^ 32) :
    ⊢ callPost (GF := GF) Φ code slice.nil := by
  unfold callPost
  isplitr
  · ipureintro; exact Or.inr hb
  iexists []
  rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]
  isplitl
  · iapply ownSlice_nil
  · itrivial

/-- A status error of a code that is not `OK` is not `nil`, and a handler error. -/
theorem errPost_handlerErr (c : w32) (m : GoString) (err : GoInterface) (hc : c ≠ W32 0) :
    status.errPost (GF := GF) c m err ⊢ ⌜err ≠ interface.nil⌝ ∗ handlerErr err := by
  unfold status.errPost
  iintro (%H | #He)
  · exact absurd H.1 hc
  isplitr
  · unfold statusErrOf
    icases He with ⟨%e0, %s0, %Hh, -⟩
    ipureintro; rw [Hh.1]; simp [interface.mkOk]
  · unfold handlerErr; ileft; iexists c, m; iexact He

theorem lastSlashIdx_get {s : GoString} {j : Nat} (h : lastSlashIdx s = some j) :
    s[j]? = some (W8 47) := by
  unfold lastSlashIdx at h
  have := List.find?_some h
  simpa using this

theorem fullMethod_split (s : GoString) (j : Nat) (h : s[j]? = some (W8 47)) :
    fullMethod (s.take j) (s.drop (j + 1)) = W8 47 :: s := by
  have hj : j < s.length := (List.getElem?_eq_some_iff.1 h).1
  have hs : s = s.take j ++ W8 47 :: s.drop (j + 1) := by
    conv => lhs; rw [← List.take_append_drop j s]
    rw [List.drop_eq_getElem_cons hj]
    congr 2
    exact (List.getElem?_eq_some_iff.1 h).2
  unfold fullMethod
  conv => rhs; rw [hs]
  simp only [List.append_assoc, List.cons_append]
  rfl

theorem w64_of_w32_lt (c : w32) : uint.Z (W64 (uint.Z c) : w64) < 2 ^ 32 := by
  have := uint_Z_lt c
  have h1 : uint.Z (W64 (uint.Z c) : w64) = uint.Z c := by word
  rw [h1]; simpa using this

theorem w64_of_w32_ne (c : w32) (h : c ≠ W32 0) : (W64 (uint.Z c) : w64) ≠ W64 0 := by
  intro h'
  apply h
  have h1 : uint.Z (W64 (uint.Z c) : w64) = uint.Z c := by word
  have h0 : uint.Z c = 0 := by
    rw [h'] at h1; rw [← h1]; rfl
  word

/-- What the server needs of a handler's error, for `FromError` and `FromContextError`. -/
theorem handlerErr_pre (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ handlerErr err ⊢
      ((⌜err = interface.nil⌝ ∨ (∃ c msg, statusErrOf err c msg) ∨
        (errAny err ∗ ⌜status.notStatusErr err⌝)) ∗ errAny err ∗ ⌜status.cmpSafe err⌝) := by
  iintro ⟨#Hst, #Hh⟩
  unfold handlerErr
  icases Hh with (⟨%c, %m, #He⟩ | ⟨#Ha, %Hn⟩)
  · isplitr
    · iright; ileft; iexists c, m; iexact He
    isplitr
    · iapply status.statusErrOf_errAny $$ [$Hst $He]
    · unfold statusErrOf
      icases He with ⟨%e0, %s0, %Hh, -⟩
      ipureintro; left; exact ⟨_, e0, Hh.1⟩
  · isplitr
    · iright; iright; iframe Ha; ipureintro; exact Hn.1
    iframe Ha; ipureintro; exact Hn.2

theorem Server.call.wp_proof : Server.call.spec (GF := GF) (hG := hG) := by
  intro s γ W a ctx cd fm body bs S Φr
  wp_start as ⟨#Hset, #Hok, #Hsrv, #Hctx, %HS, #Hbody, HSd⟩
  ihave ⟨#Hcontext, -, -, #Hsync, -, #Hst, #Hpb⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  rcases fm with _ | ⟨c0, sm⟩
  · simp only [List.length_nil]
    wp_auto
    iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
  · have hne : W64 ((c0 :: sm).length : Int) ≠ W64 0 := by
      intro h
      have h1 : sint.Z (W64 ((c0 :: sm).length : Int)) = (c0 :: sm).length :=
        sint_Z_W64_length (by omega)
      rw [h] at h1; simp at h1; omega
    rw [decide_eq_false hne]
    wp_auto
    by_cases hc : c0 = W8 47
    rotate_left
    · rw [decide_eq_false hc]
      wp_auto
      iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
    subst hc
    simp only [_root_.decide_true, Bool.not_true]
    wp_auto
    have hsm : sint.Z (W64 ((W8 47 :: sm).length : Int)) = sm.length + 1 := by
      rw [sint_Z_W64_length (by omega)]; simp
    have hsmn : sint.nat (W64 ((W8 47 :: sm).length : Int)) = sm.length + 1 := by
      show (sint.Z _).toNat = _; rw [hsm]; omega
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen2
    rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z (W64 ((W8 47 :: sm).length : Int)) ∧
      sint.Z (W64 ((W8 47 :: sm).length : Int)) ≤ ((W8 47 :: sm).length : Int) by
        rw [hsm]; simp; omega)]
    rw [hsmn]
    simp only [Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero, List.take_length]
    wp_auto
    wp_apply lastSlash.wp_proof as %pos %Hpos
    wp_if_destruct
    · iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
    rcases hj : lastSlashIdx sm with _ | j
    · rw [hj] at Hpos; exfalso; simp at *; omega
    rw [hj] at Hpos
    obtain ⟨hd1, hd2⟩ := Hpos
    have hjlt : j < sm.length := by
      unfold lastSlashIdx at hj
      have := List.mem_of_find?_eq_some hj
      simpa using this
    have hdn : sint.nat pos = j := by show (sint.Z pos).toNat = j; rw [hd2]; simp
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z pos ∧
      sint.Z pos ≤ (sm.length : Int) by simp; omega)]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hsmlen
    have hd1' : sint.Z (pos + W64 1) = j + 1 := by
      have : (j : Int) + 1 < 2 ^ 63 := by omega
      word
    have hlen' : sint.Z (W64 (sm.length : Nat)) = sm.length := by word
    have hdn' : sint.nat (pos + W64 1) = j + 1 := by
      show (sint.Z (pos + W64 1)).toNat = j + 1; rw [hd1']; omega
    have hln : sint.nat (W64 (sm.length : Nat)) = sm.length := by
      show (sint.Z (W64 (sm.length : Nat))).toNat = sm.length; rw [hlen']; simp
    rw [if_pos (by rw [hd1', hlen']; omega)]
    simp only [hdn, hdn', hln, Nat.sub_zero, List.drop_zero]
    have hmt : List.take (sm.length - (j + 1)) (List.drop (j + 1) sm) = List.drop (j + 1) sm :=
      List.take_of_length_le (by simp)
    rw [hmt]
    wp_auto
    unfold isServer
    icases Hsrv with ⟨%mp, #Hmp, #Hmu⟩
    wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv⟩
    iunfold srvInv at Hinv
    icases Hinv with ⟨%m, %sv, %R', Hmap, Hserve, Hsvcs, %HR, Hg⟩
    wp_apply (wp_map_lookup2 go.string (go.GoType.PointerType serviceInfo.ty) mp m
      (List.take j sm) (DFrac.own 1)) $$ Hmap as Hmap
    rcases hm : m !! (List.take j sm) with _ | info
    · simp only [Option.isSome_none, Option.getD_none]
      wp_apply sync.Mutex.Unlock.wp_proof _ (srvInv W a s mp γ)
        $$ [$Hsync $Hmu $Hlocked Hmap Hserve Hsvcs Hg]
      · unfold srvInv; iexists m, sv, R'; iframe; ipureintro; exact HR
      iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
    ihave #Hinfo : svcOk W a (List.take j sm) info $$ [Hsvcs]
    · iapply (BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hm)) $$ Hsvcs
    simp only [Option.isSome_some, Option.getD_some]
    wp_apply sync.Mutex.Unlock.wp_proof _ (srvInv W a s mp γ)
      $$ [$Hsync $Hmu $Hlocked Hmap Hserve Hsvcs Hg]
    · unfold srvInv; iexists m, sv, R'; iframe; ipureintro; exact HR
    unfold svcOk
    icases Hinfo with ⟨%impl, %mm, %M, #Himpl, #Hmm, #HM, #Hhs⟩
    wp_auto
    wp_apply (wp_map_lookup2 go.string MethodHandler.ty mm M (List.drop (j + 1) sm)
      DFrac.discard) $$ HM as -
    rcases hh : M !! (List.drop (j + 1) sm) with _ | h
    · simp only [Option.isSome_none, Option.getD_none]
      wp_auto
      iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
    simp only [Option.isSome_some, Option.getD_some]
    have hfm : fullMethod (List.take j sm) (List.drop (j + 1) sm) = W8 47 :: sm := by
      exact fullMethod_split sm j (lastSlashIdx_get hj)
    ihave #HhOk : handlerOk impl h S $$ []
    · iapply Hhs; ipureintro; exact ⟨hh, by rw [hfm]; exact HS⟩
    ipersist body
    wp_auto
    unfold handlerOk
    wp_apply HhOk $$ [$Hctx] [] [$HSd] as %reply %err Hres
    · unfold decOk
      imodintro
      iintro %v %Ψu %Θ Hu HΘ
      wp_auto
      wp_if_destruct
      · wp_apply status.Error.wp_proof $$ [$Hst] as %e He
        ihave ⟨%Hne, #Hh⟩ := errPost_handlerErr _ _ _ (by decide) $$ He
        iapply HΘ; iright; iframe Hh
        isplitr
        · ipureintro; exact Hne
        iright; iexact Hu
      · wp_apply google_golang_org.protobuf.proto.UnmarshalValue.wp_proof
          $$ [$Hpb $Hset $Hok $Hbody $Hu] as %err ⟨%okb, -, %Hiff, HΨ, -⟩
        cases okb
        · have hne : err ≠ interface.nil := fun h => by simp_all
          rcases err with ei | _
          · wp_auto
            wp_apply status.Error.wp_proof $$ [$Hst] as %e He
            ihave ⟨%Hne, #Hh⟩ := errPost_handlerErr _ _ _ (by decide) $$ He
            iapply HΘ; iright; iframe Hh
            isplitr
            · ipureintro; exact Hne
            ileft; iexact HΨ
          · exact absurd rfl hne
        · have he : err = interface.nil := Hiff.2 rfl
          subst he
          wp_auto
          iapply HΘ; ileft; iframe HΨ; ipureintro; rfl
    icases Hres with (⟨%He, Hrep⟩ | ⟨%He, #Hh⟩)
    · subst He
      wp_auto
      unfold replyOk
      wp_apply encode.wp_proof reply (fun o => iprop(∀ rbs, ⌜o = some rbs⌝ -∗ Φr rbs))
        $$ [$Hpkg $Hset $Hok Hrep] as %rb %merr Hr
      · icases Hrep with (⟨%Hn, HΦ0⟩ | ⟨%Hn, Hm⟩)
        · ileft; isplitr; ipureintro; exact Hn
          iintro %rbs %Hr; cases Hr; iexact HΦ0
        · iright; iframe Hm; ipureintro; exact Hn
      icases Hr with (⟨%He, %rbs, Hrb, HΨ⟩ | ⟨%He, -, -⟩)
      · subst He
        ihave %Hrbl := ownSlice_len $$ Hrb
        wp_auto
        wp_if_destruct
        · iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
        · iapply HΦ
          unfold callPost
          isplitr
          · ipureintro; left; decide
          iexists rbs
          iframe Hrb
          rw [show (W64 (uint.Z (W32 0)) : w64) = W64 0 by decide, if_pos rfl]
          iapply HΨ; ipureintro; rfl
      · rcases merr with ei | _
        · wp_auto
          iapply HΦ; iapply callPost_err _ _ (by decide) (by decide)
        · exact absurd rfl He
    · rcases err with ei | _
      rotate_left
      · exact absurd rfl He
      ihave ⟨Hpre, #Hea, %Hcmp⟩ := handlerErr_pre _ $$ [$Hst $Hh]
      wp_auto
      wp_apply (status.FromError.wp_proof (GF := GF) (hG := hG) (GoInterface.ok ei))
        $$ [$Hst $Hpre] as %st %okf Hfe
      icases Hfe with (⟨%Hc⟩ | ⟨%c, %msg, %Hokf, #Hse, #Hst1⟩ | ⟨%Hokf, %msg, #Hst1⟩)
      · exact Hc.elim
      · subst Hokf
        ihave %hc : ⌜c ≠ W32 0⌝ $$ [Hse]
        · unfold statusErrOf
          icases Hse with ⟨%e0, %s0, %Hh0, -⟩
          ipureintro; exact Hh0.2
        wp_auto
        wp_apply status.Status.Code.wp_proof $$ [$Hst $Hst1]
        wp_apply status.Status.Message.wp_proof $$ [$Hst $Hst1]
        iapply HΦ; iapply callPost_err _ _ (w64_of_w32_ne c hc) (w64_of_w32_lt c)
      · subst Hokf
        wp_auto
        wp_apply status.FromContextError.wp_proof $$ [$Hst $Hea] as %st2 ⟨%c, %msg2, %hc, #Hst2⟩
        · ipureintro; exact Hcmp
        wp_apply status.Status.Code.wp_proof $$ [$Hst $Hst2]
        wp_apply status.Status.Message.wp_proof $$ [$Hst $Hst2]
        iapply HΦ; iapply callPost_err _ _ (w64_of_w32_ne c hc) (w64_of_w32_lt c)

/-- A cancel function that can be called (any number of times; persistent). -/
def cancelOk (f : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #f) (Val #())) {{ Φ }})

instance cancelOk_persistent (f : GoFunc) : Persistent (cancelOk (GF := GF) f) := by
  unfold cancelOk; infer_instance

/-- The invariant of a served connection's `mu`: the `broken` flag, the running calls' cancel
functions, and while not broken the acceptor's writer token with the answers written. -/
def scInv (W : GrpcWorld GF) (a : GoString) (cid : w64) (σ : GName) (sc : Loc) : IProp GF :=
  iprop(∃ (brk : Bool) (amp : Loc) (am : GMap w64 GoFunc),
    structFieldRef serverConn go!"broken" sc ↦ brk ∗
    structFieldRef serverConn go!"active" sc ↦ amp ∗ amp ↦$ am ∗
    ([∗map] _k ↦ f ∈ am, cancelOk f) ∗
    (if brk then iprop(True) else
      ∃ Wb : List w8, sendTok cid true (respProto W a) Wb ∗ respDone W a cid σ Wb))

/-- `sc` serves the acceptor's end `cid` of a connection to `a` (persistent). -/
def isSC (sc : Loc) (cid : w64) (W : GrpcWorld GF) (a : GoString) (σ : GName) : IProp GF :=
  iprop(∃ cv : GoInterface, structFieldRef serverConn go!"conn" sc ↦□ cv ∗ connIface cv cid true ∗
    sync.isMutex (structFieldRef serverConn go!"mu" sc) (scInv W a cid σ sc))

instance isSC_persistent (sc : Loc) (cid : w64) (W : GrpcWorld GF) (a : GoString) (σ : GName) :
    Persistent (isSC sc cid W a σ) := by
  unfold isSC; infer_instance

theorem cancels_delete (am : GMap w64 GoFunc) (k : w64) :
    ([∗map] _k ↦ f ∈ am, cancelOk (GF := GF) f) ⊢ [∗map] _k ↦ f ∈ GMap.delete k am, cancelOk f :=
  BigSepM.bigSepM_subseteq Std.LawfulPartialMap.delete_subset_self

/-- The run of call `k` of connection `cid` (to address `a`), with its context and cancel
function: see the file header. -/
theorem wp_handle (s : Loc) (γs : GName) (W : GrpcWorld GF) (a : GoString) (sc : Loc) (cid : w64)
    (σ : GName) (γ : GConnNames) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (cancel : GoFunc) (k : Nat) (L : List CFrame) (fm : GoString) (b : List w8) (post col : GName)
    (body : GoSlice) (hr : L[k]? = some (.call fm b post col)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ isServer s γs W a ∗ isSC sc cid W a σ ∗
        context.isContext ctx cd ∗ cancelOk cancel ∗ isGConn W a cid γ ∗
        monoListLbOwn γ.reqs L ∗ frameDeposit W a (.call fm b post col) ∗
        ghostMapElem γ.ans k (DFrac.own 1) (none : Option (w64 × GoString × List w8)) ∗
        ghostMapElem σ k (DFrac.own 1) () ∗ body ↦* b }}
      (App (App (App (App (App (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"handle"))
        (Val #sc)) (Val #(interface.ok ctx))) (Val #cancel)) (Val #(W64 k))) (Val #fm))
        (Val #body))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hset, #Hok, #Hsrv, #Hsc, #Hctx, #Hcan, #Hc, #Hlb, Hdep, Hans, Hσ, Hbody⟩
  ihave ⟨-, -, #Hnet, #Hsync, -, -, -⟩ := deps_of_pkg $$ Hpkg
  unfold frameDeposit
  icases Hdep with ⟨%S, %Φr, %HS, #Hsaved, HSd⟩
  imod ownSlice_persist $$ Hbody with #Hbody
  wp_auto
  wp_apply Server.call.wp_proof $$ [$Hpkg $Hset $Hok $Hsrv $Hctx $Hbody $HSd]
    as %code %msg %rep Hpost
  · ipureintro; exact HS
  unfold callPost
  icases Hpost with ⟨%hcode, %rbs, Hrep, HΦr⟩
  ihave #Hinv := isGConn_inv W a cid γ $$ Hc
  iapply fupd_wp
  imod answer W a cid γ k L fm b post col code msg rbs hr hcode ⊤ (by simp) $$ Hinv Hans Hlb [HΦr]
    with #HansP
  · unfold answerEscrow
    by_cases hc : code = W64 0
    · simp only [hc, ↓reduceIte]
      unfold replyEscrow
      iexists Φr
      iframe Hsaved HΦr
    · simp only [hc, ↓reduceIte]; itrivial
  imodintro
  unfold cancelOk
  wp_apply Hcan
  unfold isSC
  icases Hsc with ⟨%cv, #Hcv, #Hcvi, #Hmu⟩
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv2⟩
  iunfold scInv at Hinv2
  icases Hinv2 with ⟨%brk, %amp, %am, Hbrk, Hact, Ham, Hcans, Hrest⟩
  wp_auto
  wp_apply (wp_mapDelete amp am (W64 k) go.uint64 context.CancelFunc.ty) $$ Ham as Ham
  ihave Hcans := cancels_delete am (W64 k) $$ Hcans
  cases brk
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrest with ⟨%Wb, Hsend, Hdone⟩
    wp_auto
    wp_apply encodeMsg.wp_proof $$ [$Hpkg $Hrep] as %pl ⟨Hpl, Hrep⟩
    ihave %Hpllen := ownSlice_len _ _ _ $$ Hpl
    have hlen : (respMsg (k, code, msg, rbs)).length < 2 ^ 63 := by
      unfold respMsg; rw [Hpllen.1]; show (sint.Z pl.len).toNat < 2 ^ 63
      have := Hpllen.2; word
    ihave ⟨#HP, Hdone⟩ := resp_next W a cid γ σ Wb k code msg rbs hlen $$ Hc Hdone Hσ HansP
    simp only [respMsg]
    unfold connIface
    icases Hcvi with ⟨%c, %Hcveq, #Hcc⟩
    wp_apply writeFrame.wp_proof $$ [$Hnet $Hsend $HP $Hpl] as %err ⟨%n, %Hn, -, Hsend, Hpl⟩
    · unfold connIface; iexists c; iframe Hcc; ipureintro; exact Hcveq
    subst Hcveq
    rcases err with ei | _
    · wp_auto
      wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hcc] as %err2 -
      wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc) $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham Hcans]
      · unfold scInv; iexists true, amp, _; iframe; simp only [↓reduceIte]; itrivial
      iapply HΦ; itrivial
    · rw [Hn.2.1 rfl, List.take_length] at *
      wp_auto
      wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc)
        $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham Hcans Hsend Hdone]
      · unfold scInv; iexists false, amp, _; iframe
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexists _; iframe
      iapply HΦ; itrivial
  · simp only [↓reduceIte]
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc) $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham Hcans]
    · unfold scInv; iexists true, amp, _; iframe; simp only [↓reduceIte]; itrivial
    iapply HΦ; itrivial

/-- A cancel function of `WithCancel(Background())` can be called. -/
theorem cancelOk_of (f : GoFunc) (γ' : context.ContextNames) :
    (□ (∀ Φ : val → IProp GF, □ (True : IProp GF) -∗ ▷ (context.ContextClosed γ' -∗ Φ #()) -∗
        WP (App (Val #f) (Val #())) {{ Φ }})) ⊢ cancelOk f := by
  iintro #H
  unfold cancelOk
  imodintro
  iintro %Φ HΦ
  iapply H
  · itrivial
  · inext; iintro -; iexact HΦ

/-- `sc.cancelCall(seq)`. -/
theorem wp_cancelCall (sc : Loc) (cid : w64) (W : GrpcWorld GF) (a : GoString) (σ : GName)
    (seq : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isSC sc cid W a σ }}
      (App (Val (sc @!! go.GoType.PointerType serverConn.ty @!! go!"cancelCall")) (Val #seq))
    {{ RET #(); True }} := by
  wp_start as #Hsc
  ihave ⟨-, -, -, #Hsync, -, -, -⟩ := deps_of_pkg $$ Hpkg
  unfold isSC
  icases Hsc with ⟨%cv, #Hcv, #Hcvi, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv2⟩
  iunfold scInv at Hinv2
  icases Hinv2 with ⟨%brk, %amp, %am, Hbrk, Hact, Ham, Hcans, Hrest⟩
  wp_auto
  wp_apply (wp_map_lookup2 go.uint64 context.CancelFunc.ty amp am seq (DFrac.own 1)) $$ Ham as Ham
  rcases hm : am !! seq with _ | f
  · simp only [Option.isSome_none, Option.getD_none]
    wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc)
      $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham Hcans Hrest]
    · unfold scInv; iexists brk, amp, am; iframe
    iapply HΦ; itrivial
  · ihave #Hf : cancelOk f $$ [Hcans]
    · iapply (BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hm)) $$ Hcans
    simp only [Option.isSome_some, Option.getD_some]
    wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc)
      $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham Hcans Hrest]
    · unfold scInv; iexists brk, amp, am; iframe
    unfold cancelOk
    wp_apply Hf
    iapply HΦ; itrivial

/-- `s.serveConn(cv)` on the acceptor's end `cid` of a fresh connection to `a`, with nothing read
or written yet: see the file header. -/
theorem wp_serveConn (s : Loc) (γs : GName) (W : GrpcWorld GF) (a : GoString) (cv : GoInterface)
    (cid : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ isServer s γs W a ∗ connIface cv cid true ∗
        recvTok cid true (reqProto W a) [] ∗ sendTok cid true (respProto W a) [] ∗
        connFresh cid true }}
      (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"serveConn")) (Val #cv))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hset, #Hok, #Hsrv, #Hcvi, Hrecv, Hsend, Hfr⟩
  ihave ⟨#Hcontext, -, #Hnet, #Hsync, -, -, -⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoFunc) go.uint64 context.CancelFunc.ty) as %amp Ham
  irename «$r0» => Hscv
  generalize «$r0_ptr» = sc at *
  icases typedPointsto_split _ _ _ $$ Hscv with Hscv
  simp only [TypedPointsto.typedPointstoDef]
  icases Hscv with ⟨Hconn, Hmu0, Hbrk, Hact, -⟩
  ipersist Hconn
  imod ghost_map_alloc_strong_empty (K := Nat) (V := Unit) (GF := GF)
    (fun _ => True) PredInfinite.true with ⟨%σ, -, Hσ⟩
  imod sync.init_Mutex (scInv W a cid σ sc) ⊤
      (structFieldRef serverConn go!"mu" sc) $$ [Hmu0] [Hbrk Hact Ham Hsend] with #Hmu
  · iexact Hmu0
  · inext; unfold scInv; iexists false, amp, ∅; iframe
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitl []
    · iapply BigSepM.bigSepM_empty.2; iempintro
    iexists []; iframe
    unfold respDone; ileft; ipureintro; rfl
  ihave #Hsc : isSC sc cid W a σ $$ []
  · unfold isSC; iexists cv; iframe Hconn Hcvi Hmu
  ihave HI : (∃ (qs : List (List w8)) (Mσ : GMap Nat Unit),
      "Hrecv" ∷ recvTok cid true (reqProto W a) (framesOf qs) ∗
      "%Hqs" ∷ ⌜(∀ q ∈ qs, q.length < 2 ^ 63) ∧ ∀ i, (Mσ !! i).isSome → i < qs.length⌝ ∗
      "Hσ" ∷ ghostMapAuth σ 1 Mσ ∗
      "Hrole" ∷ ((⌜qs = []⌝ ∗ connFresh cid true) ∨
        ∃ γ : GConnNames, isGConn W a cid γ ∗ ghostVar γ.ctr (1 : Qp).half qs.length)
      : IProp GF) $$ [Hrecv Hσ Hfr]
  · iexists [], ∅
    simp only [net.rpc.framesOf_nil]
    iframe Hrecv Hσ
    isplitr
    · ipureintro; simp
    ileft; iframe Hfr
  wp_for HI
  wp_apply readFrame.wp_proof $$ [$Hnet $Hpkg $Hcvi $Hrecv] as %p %err ⟨%data, Hrecv, Hres⟩
  icases Hres with (⟨%Herr, %pl, %Hpl, Hp⟩ | ⟨%Herr, -⟩)
  · subst Herr
    wp_auto
    wp_apply decodeMsg.wp_proof $$ [$Hpkg $Hp] as %tag %seq %meth %body %ok Hdec
    cases ok
    · wp_auto
      wp_for_post
      wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv2⟩
      iunfold scInv at Hinv2
      icases Hinv2 with ⟨%brk, %amp2, %am, Hbrk, Hact, Ham, #Hcans, Hrest⟩
      wp_auto
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply (wp_map_for_range (K := w64) (V := GoFunc) (fun _ _ => iprop(∃ v : GoFunc, c_ptr ↦ v))) $$ Ham
      iintro %keys %hkeys
      isplitl [c]
      · iexists _; iframe
      isplitl []
      · imodintro
        iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%v0, Hc⟩
        ihave #Hf : cancelOk v $$ [Hcans]
        · iapply (BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hk2)) $$ Hcans
        unfold cancelOk
        wp_auto
        wp_apply Hf
        unfold forMapPostcondition
        iright; ileft
        isplit
        · ipureintro; rfl
        · iexists _; iframe
      iintro ⟨%v0, Hc⟩ Ham
      wp_auto
      wp_apply (wp_map_make1 (K := w64) (V := GoFunc) go.uint64 context.CancelFunc.ty) as %amp3 Ham3
      wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc)
        $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham3 Hrest]
      · unfold scInv; iexists brk, amp3, ∅; iframe
        iapply BigSepM.bigSepM_empty.2; iempintro
      unfold connIface
      icases Hcvi with ⟨%cc, %Hcveq, #Hcc⟩
      subst Hcveq
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof cc cid true $$ [$Hnet $Hcc] as %err2 -
      iapply HΦ; itrivial
    · simp only [ite_true]
      icases Hdec with ⟨%b, %Hb, Hbody⟩
      obtain ⟨hdata, hpl⟩ := Hpl
      obtain ⟨hplm, hsm⟩ := Hb
      subst hdata
      ihave Hrecv := req_parse W a cid qs pl Hqs.1 hpl $$ Hrecv
      icases Hrecv with ⟨Hrecv, %γ, %L, %f, #Hc, #Hlb, %HLf⟩
      obtain ⟨hr, hmsg⟩ := HLf
      ihave #Hinv := isGConn_inv W a cid γ $$ Hc
      iapply fupd_wp
      ihave Hctr : (|={⊤}=> ghostVar γ.ctr (1 : Qp).half qs.length : IProp GF) $$ [Hrole]
      · icases Hrole with (⟨%Hq, Hfr⟩ | ⟨%γ', #Hc', Hctr⟩)
        · subst Hq
          iapply claim_role W a cid γ ⊤ (by simp) $$ Hinv Hfr
        · ihave %Hg := isGConn_agree W a cid γ γ' $$ Hc Hc'
          subst Hg
          imodintro; iexact Hctr
      imod Hctr
      rw [hplm] at hmsg
      cases f with
      | call fm b' post col =>
        unfold CFrame.msg at hmsg
        have hfm : fm.length < 2 ^ 63 := by
          have h1 := congrArg List.length hmsg
          rw [msgOf_length, msgOf_length] at h1
          have h2 : (msgOf tag seq meth b).length < 2 ^ 63 := hplm ▸ hpl
          rw [msgOf_length] at h2
          omega
        obtain ⟨htag, hseq, hm, hb⟩ := msgOf_inj hfm hsm hmsg
        subst htag hseq hm hb
        imod take_call W a cid γ qs.length L fm b' post col hr ⊤ (by simp) $$ Hinv Hctr Hlb
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
        wp_apply context.wp_Background
        ihave #Hcci := context.isClosedchanInit_of_init $$ Hcontext
        wp_apply (context.wp_WithCancel_Background (GF := GF) (hG := hG) iprop(True))
          $$ [$Hcontext $Hcci] as %ctx' %γ' %cancel ⟨#Hcan, #Hctx', -⟩
        ihave #HcanOk := cancelOk_of cancel γ' $$ Hcan
        unfold isSC
        icases Hsc with ⟨%cv', #Hcv', #Hcvi', #Hmu'⟩
        wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu'] as ⟨Hlocked, Hinv2⟩
        iunfold scInv at Hinv2
        icases Hinv2 with ⟨%brk, %amp2, %am, Hbrk, Hact, Ham, #Hcans, Hrest⟩
        wp_auto
        wp_apply (wp_mapInsert go.uint64 amp2 am (W64 qs.length) cancel) $$ Ham as Ham
        wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc)
          $$ [$Hsync $Hmu' $Hlocked Hbrk Hact Ham Hrest]
        · unfold scInv; iexists brk, amp2, _; iframe
          iapply BigSepM.bigSepM_insert_elim $$ [HcanOk] [Hcans]
          · iexact HcanOk
          · iexact Hcans
        wp_apply wp_fork $$ [Hdep Hans Htok Hbody]
        · wp_apply wp_handle s γs W a sc cid σ γ ctx' _ cancel qs.length L fm b' post col body hr
            $$ [$Hpkg $Hset $Hok $Hsrv $Hctx' $HcanOk $Hc $Hlb $Hdep $Hans $Htok $Hbody]
          · unfold isSC; iexists cv'; iframe Hcv' Hcvi' Hmu'
          itrivial
        wp_for_post
        iframe
        iexists qs ++ [pl], Mσ.insert qs.length ()
        rw [net.rpc.framesOf_concat]
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
      | cancel t =>
        unfold CFrame.msg at hmsg
        obtain ⟨htag, hseq, hm, hb⟩ := msgOf_inj (by simp) hsm hmsg
        subst htag hseq hm hb
        imod skip_cancel W a cid γ qs.length L t hr ⊤ (by simp) $$ Hinv Hctr Hlb with Hctr
        imodintro
        wp_auto
        wp_apply wp_cancelCall sc cid W a σ t $$ [$Hpkg $Hsc]
        wp_for_post
        iframe
        iexists qs ++ [pl], Mσ
        rw [net.rpc.framesOf_concat]
        iframe Hrecv Hσ
        isplitr
        · ipureintro
          refine ⟨fun q hq => ?_, fun i hi => ?_⟩
          · simp only [List.mem_append, List.mem_singleton] at hq
            rcases hq with hq | hq
            · exact Hqs.1 q hq
            · subst hq; exact hpl
          · simp only [List.length_append, List.length_singleton]
            have := Hqs.2 i hi
            omega
        iright
        iexists γ
        iframe Hc
        simp only [List.length_append, List.length_singleton]
        iexact Hctr
  · rcases err with ei | _
    · wp_auto
      wp_for_post
      wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv2⟩
      iunfold scInv at Hinv2
      icases Hinv2 with ⟨%brk, %amp2, %am, Hbrk, Hact, Ham, #Hcans, Hrest⟩
      wp_auto
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply (wp_map_for_range (K := w64) (V := GoFunc) (fun _ _ => iprop(∃ v : GoFunc, c_ptr ↦ v))) $$ Ham
      iintro %keys %hkeys
      isplitl [c]
      · iexists _; iframe
      isplitl []
      · imodintro
        iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%v0, Hc⟩
        ihave #Hf : cancelOk v $$ [Hcans]
        · iapply (BigSepM.bigSepM_lookup (by rw [gmap_get?_eq]; exact hk2)) $$ Hcans
        unfold cancelOk
        wp_auto
        wp_apply Hf
        unfold forMapPostcondition
        iright; ileft
        isplit
        · ipureintro; rfl
        · iexists _; iframe
      iintro ⟨%v0, Hc⟩ Ham
      wp_auto
      wp_apply (wp_map_make1 (K := w64) (V := GoFunc) go.uint64 context.CancelFunc.ty) as %amp3 Ham3
      wp_apply sync.Mutex.Unlock.wp_proof _ (scInv W a cid σ sc)
        $$ [$Hsync $Hmu $Hlocked Hbrk Hact Ham3 Hrest]
      · unfold scInv; iexists brk, amp3, ∅; iframe
        iapply BigSepM.bigSepM_empty.2; iempintro
      unfold connIface
      icases Hcvi with ⟨%cc, %Hcveq, #Hcc⟩
      subst Hcveq
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof cc cid true $$ [$Hnet $Hcc] as %err2 -
      iapply HΦ; itrivial
    · exfalso; exact Herr.1 rfl

/-- `s.Serve(lis)` on a listener of `a` (from `net.Listen`), with the server's owner token (no
registration after it) or its served token (a `Serve` again, as the real server allows): it serves
each accepted connection in its own goroutine, and returns only with an error, and the served
token. -/
abbrev Server.Serve.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (W : GrpcWorld GF) (a : GoString) (R : List GoString) (l : Loc)
    (lid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ isServer s γs W a ∗ (srvOwn γs R ∨ srvServed γs) ∗
      net.ownListener l lid a ∗ grpcAddr W a }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"Serve"))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l)))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ ∗ srvServed γs }}

theorem Server.Serve.wp_proof : Server.Serve.spec (GF := GF) (hG := hG) := by
  intro s γs W a R l lid
  wp_start as ⟨#Hset, #Hok, #Hsrv, Hown, #Hl, #Haddr⟩
  ihave ⟨-, -, #Hnet, #Hsync, -, -, -⟩ := deps_of_pkg $$ Hpkg
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%mp, #Hmp, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv⟩
  iunfold srvInv at Hinv
  icases Hinv with ⟨%m, %sv, %R', Hmap, Hserve, Hsvcs, %HR, Hg⟩
  unfold srvOwn srvServed
  ihave Htok : (|==> (ghostVar γs (1 : Qp).half (none : Option (List GoString)) ∗
      ghostVar γs (1 : Qp).half (none : Option (List GoString))) : IProp GF) $$ [Hg Hown]
  · cases sv
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hown with (Hown | Hown)
      · icombine Hg Hown gives %Heq
        obtain ⟨-, Heq⟩ := Heq
        have Heq' := Option.some.inj Heq
        subst Heq'
        iapply ghostVar_update_halves (none : Option (List GoString)) γs (some R') (some R')
          $$ Hg Hown
      · iexfalso
        icombine Hg Hown gives %Heq
        exfalso
        cases Heq.2
    · simp only [↓reduceIte]
      icases Hown with (Hown | Hown)
      · iexfalso
        icombine Hg Hown gives %Heq
        exfalso
        cases Heq.2
      · imodintro
        iframe
  imod Htok with ⟨Hg, Hown⟩
  wp_auto
  wp_apply sync.Mutex.Unlock.wp_proof _ (srvInv W a s mp γs)
    $$ [$Hsync $Hmu $Hlocked Hmap Hserve Hsvcs Hg]
  · unfold srvInv; iexists m, true, R'; simp only [↓reduceIte]; iframe; ipureintro; exact HR
  unfold grpcAddr
  icases Haddr with ⟨#Hpr, -⟩
  wp_for
  wp_apply net.TCPListener.Accept.wp_proof l lid a (reqProto W a) (respProto W a)
    $$ [$Hnet $Hl $Hpr] as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%c, %cid, %Hcv, #Hc, ⟨Hsend, Hrecv⟩, Hf⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  · wp_auto
    wp_apply wp_fork $$ [Hsend Hrecv Hf]
    · wp_apply wp_serveConn s γs W a (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) cid
        $$ [$Hpkg $Hset $Hok $Hsrv $Hsend $Hrecv $Hf]
      · unfold connIface; iexists c; iframe Hc; ipureintro; rfl
      itrivial
    wp_for_post
    iframe
  · wp_auto
    wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %r -
    wp_if_destruct
    · wp_for_post
      iframe
    · wp_apply net.TCPListener.Close.wp_proof l lid a $$ [$Hnet $Hl] as %err2 -
      wp_for_post
      iapply HΦ
      iframe
      ipureintro; simp

end spec

end google_golang_org.grpc

end Perennial
