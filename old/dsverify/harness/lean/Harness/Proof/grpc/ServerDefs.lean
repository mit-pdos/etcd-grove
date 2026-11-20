/-
The server side of the lab's grpc model (`server.go`): what a registered service must meet, the
server's representation predicate, and the specs of `NewServer` and `RegisterService`.

* `handlerOk impl h S` (persistent): the generated method handler `h` (a `MethodHandler`, e.g.
  `_Consensus_ESP_Handler`) with the service implementation `impl` meets the unary spec `S`:
  called with any context, a decoding function `dec` of the request bytes `bs` (`decOk`), a nil
  interceptor and the caller's deposit `S bs Φ`, it returns `(reply, nil)` with `replyOk reply Φ`
  (the reply's encoding, if any, gives `Φ`), or `(_, err)` with a non-nil `err` the server can
  convert to a status (`status.handlerErr`). The run proves it of its generated handlers and
  service methods.
* `decOk dec bs` (persistent): `dec(v)` decodes `bs` into `v` with the codec (`nil`), or returns
  a status error (the codec's failure, or a request over the size limit, in which case the
  codec's premise comes back).
* `svcOk W a name info` (persistent): the registered `*serviceInfo` `info` of service `name`
  holds an implementation and a methods map (for good) whose every handler meets the spec of
  its full method `"/name/method"` at `a`.
* `isServer s γ W a` (persistent): `s`'s `services` map, owned by `mu`'s invariant
  (`srvInv`) with each entry's `svcOk`, and the `serve` flag; `srvOwn γ R` (exclusive): the
  server's owner token, whose names `R` are those registered, as long as `Serve` has not run;
  `srvServed γ` (exclusive): the token after `Serve` ran, which `Serve` takes and gives back
  (`Serve` turns `srvOwn` into it: no registration after it, as the real server refuses, but
  `Serve` again, as the real server allows).
* `NewServer()`: a server for any world and address the caller names, with its token for `[]`.
* `s.RegisterService(sd, ss)` with the token for `R` and `sd.ServiceName ∉ R`, no streams, and
  every method's handler meeting its spec: the token for `name :: R`.
-/
module

public import Harness.Proof.grpc.Proto
public import Harness.Proof.grpc.Pb
public import Harness.Proof.grpc.StatusSpec
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn
open google_golang_org.protobuf.proto (PbCodec PbKit codecSet kitCodecOk)
open google_golang_org.grpc.status (handlerErr)

namespace google_golang_org.grpc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [PbKit] [PbCodec GF]

/-- A handler's reply gives the continuation of its encoding: a nil reply is the empty message;
another is encoded by the codec (an encoding failure is an error answer, which needs nothing). -/
def replyOk (reply : GoInterface) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop((⌜reply = interface.nil⌝ ∗ Φ []) ∨
    (⌜reply ≠ interface.nil⌝ ∗ PbCodec.marshal reply (fun o => iprop(∀ bs, ⌜o = some bs⌝ -∗ Φ bs))))

/-- `dec` decodes the request bytes `bs` (see the file header; persistent). -/
def decOk (dec : GoFunc) (bs : List w8) : IProp GF :=
  iprop(□ ∀ (v : GoInterface) (Ψ : Bool → IProp GF) (Θ : val → IProp GF),
    PbCodec.unmarshal bs v Ψ -∗
    ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ Ψ true) ∨
        (⌜err ≠ interface.nil⌝ ∗ handlerErr err ∗ (Ψ false ∨ PbCodec.unmarshal bs v Ψ))) -∗
      Θ #err) -∗
    WP (App (Val #dec) (Val #v)) {{ Θ }})

/-- The handler `h` with implementation `impl` meets `S` (see the file header; persistent). -/
def handlerOk (impl : GoInterface) (h : GoFunc) (S : UnarySpec GF) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec : GoFunc)
      (bs : List w8) (Φ : List w8 → IProp GF) (Θ : val → IProp GF),
    context.isContext ctx cd -∗ decOk dec bs -∗ S bs Φ -∗
    ▷ (∀ (reply err : GoInterface), ((⌜err = interface.nil⌝ ∗ replyOk reply Φ) ∨
        (⌜err ≠ interface.nil⌝ ∗ handlerErr err)) -∗ Θ (PairV #reply #err)) -∗
    WP (App (App (App (App (Val #h) (Val #impl)) (Val #(interface.ok ctx))) (Val #dec))
      (Val #func.nil)) {{ Θ }})

/-- The full method name of method `m` of service `svc`. -/
def fullMethod (svc m : GoString) : GoString := go!"/" ++ svc ++ go!"/" ++ m

/-- A registered service (see the file header; persistent). -/
def svcOk (W : GrpcWorld GF) (a name : GoString) (info : Loc) : IProp GF :=
  iprop(∃ (impl : GoInterface) (mm : Loc) (M : GMap GoString GoFunc),
    structFieldRef serviceInfo go!"impl" info ↦□ impl ∗
    structFieldRef serviceInfo go!"methods" info ↦□ mm ∗ ownMap mm DFrac.discard M ∗
    □ ∀ (m : GoString) (h : GoFunc) (S : UnarySpec GF),
      ⌜M !! m = some h ∧ W.MS a (fullMethod name m) = some S⌝ -∗ handlerOk impl h S)

/-- The invariant of a server's `mu`: its services, each `svcOk`, the `serve` flag, and the
owner token's other half (with the registered names) until `Serve` ran, the served token's after. -/
def srvInv (W : GrpcWorld GF) (a : GoString) (s mp : Loc) (γ : GName) : IProp GF :=
  iprop(∃ (m : GMap GoString Loc) (sv : Bool) (R : List GoString),
    ownMap mp (DFrac.own 1) m ∗ structFieldRef Server go!"serve" s ↦ sv ∗
    ([∗map] name ↦ info ∈ m, svcOk W a name info) ∗
    ⌜∀ n, (m !! n).isSome = true → n ∈ R⌝ ∗
    (if sv then ghostVar γ (1 : Qp).half (none : Option (List GoString))
     else ghostVar γ (1 : Qp).half (some R)))

/-- `s` is a server for address `a` of world `W`, with owner names `γ` (persistent). -/
def isServer (s : Loc) (γ : GName) (W : GrpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ mp : Loc, structFieldRef Server go!"services" s ↦□ mp ∗
    sync.isMutex (structFieldRef Server go!"mu" s) (srvInv W a s mp γ))

/-- The server's owner token, with the registered names `R` (exclusive). -/
def srvOwn (γ : GName) (R : List GoString) : IProp GF := ghostVar γ (1 : Qp).half (some R)

/-- The server's token after `Serve` ran (exclusive). -/
def srvServed (γ : GName) : IProp GF :=
  ghostVar γ (1 : Qp).half (none : Option (List GoString))

instance handlerOk_persistent (impl : GoInterface) (h : GoFunc) (S : UnarySpec GF) :
    Persistent (handlerOk (GF := GF) impl h S) := by
  unfold handlerOk; infer_instance
instance decOk_persistent (dec : GoFunc) (bs : List w8) : Persistent (decOk (GF := GF) dec bs) := by
  unfold decOk; infer_instance
instance svcOk_persistent (W : GrpcWorld GF) (a name : GoString) (info : Loc) :
    Persistent (svcOk W a name info) := by
  unfold svcOk; infer_instance
instance isServer_persistent (s : Loc) (γ : GName) (W : GrpcWorld GF) (a : GoString) :
    Persistent (isServer s γ W a) := by
  unfold isServer; infer_instance

end defs

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

/-- The packages the `grpc` model imports are initialized. -/
theorem deps_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ⊢
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
      isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.google_golang_org.grpc).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.context ∗ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
    isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive ∗ True) ⊢ _
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, -, -, -⟩
  iframe

/-- `NewServer()`: a server for the world and address the caller names, with its owner token. -/
abbrev NewServer.spec : Prop :=
  ∀ (W : GrpcWorld GF) (a : GoString) (opt : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.NewServer)) (Val #opt))
  {{ (s : Loc) (γ : GName), RET #s; isServer s γ W a ∗ srvOwn γ [] }}

/-- A service descriptor `sd` (read with fraction `dq`) whose every method's handler meets its
spec at `a` with implementation `ss`, and which has no streams. -/
def descOk (W : GrpcWorld GF) (a : GoString) (sd : Loc) (dq : DFrac) (name : GoString)
    (ss : GoInterface) : IProp GF :=
  iprop(∃ (msl ssl : GoSlice) (Ms : List MethodDesc),
    structFieldRef ServiceDesc go!"ServiceName" sd ↦{dq} name ∗
    structFieldRef ServiceDesc go!"Methods" sd ↦{dq} msl ∗ msl ↦*{dq} Ms ∗
    structFieldRef ServiceDesc go!"Streams" sd ↦{dq} ssl ∗ ⌜ssl.len = W64 0⌝ ∗
    □ ∀ (i : Nat) (d : MethodDesc) (S : UnarySpec GF),
      ⌜Ms[i]? = some d ∧ W.MS a (fullMethod name d.MethodName') = some S⌝ -∗
      handlerOk ss d.Handler' S)

/-- `s.RegisterService(sd, ss)`: see the file header. -/
abbrev Server.RegisterService.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (W : GrpcWorld GF) (a : GoString) (R : List GoString) (sd : Loc)
    (dq : DFrac) (name : GoString) (ss : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ isServer s γ W a ∗
      srvOwn γ R ∗ ⌜name ∉ R⌝ ∗ descOk W a sd dq name ss }}
    (App (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"RegisterService")) (Val #sd))
      (Val #ss))
  {{ RET #(); srvOwn γ (name :: R) ∗ descOk W a sd dq name ss }}

set_option goose.wp.extras true

theorem NewServer.wp_proof : NewServer.spec (GF := GF) (hG := hG) := by
  intro W a opt
  wp_start
  ihave ⟨-, -, -, #Hsync, -, -, -⟩ := deps_of_pkg $$ Hpkg
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
    (go.GoType.PointerType serviceInfo.ty)) as %mp Hmp
  irename «$r0» => Hs
  generalize «$r0_ptr» = s at *
  iStructNamed Hs
  imod (ghostVar_alloc (GF := GF) (some ([] : List GoString))) with ⟨%γ, Hg⟩
  ihave ⟨Hg1, Hg2⟩ := ghostVar_halves γ (some ([] : List GoString)) $$ Hg
  ipersist services
  imod sync.init_Mutex (srvInv W a s mp γ) ⊤ (structFieldRef Server go!"mu" s) $$ [mu]
    [Hmp serve Hg1] with #Hmu
  · iexact mu
  · inext; unfold srvInv; iexists ∅, false, []
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hmp serve Hg1
    isplitl
    · iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro; intro n hn; simp at hn
  imodintro
  iapply HΦ
  unfold isServer srvOwn
  iframe Hg2
  iexists mp
  iframe services Hmu

theorem Server.RegisterService.wp_proof : Server.RegisterService.spec (GF := GF) (hG := hG) := by
  intro s γ W a R sd dq name ss
  wp_start as ⟨#Hsrv, Hown, %Hn, Hd⟩
  ihave ⟨-, -, -, #Hsync, -, -, -⟩ := deps_of_pkg $$ Hpkg
  unfold descOk
  icases Hd with ⟨%msl, %ssl, %Ms, Hname, Hmsl, HMs, Hssl, %Hssl0, #Hh⟩
  wp_auto
  rw [Hssl0]
  simp only [_root_.decide_true, Bool.not_true]
  wp_auto
  unfold isServer
  icases Hsrv with ⟨%mp, #Hmp, #Hmu⟩
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv⟩
  iunfold srvInv at Hinv
  icases Hinv with ⟨%m, %sv, %R', Hmap, Hserve, Hsvcs, %HR, Hg⟩
  unfold srvOwn
  cases sv
  rotate_left
  · simp only [↓reduceIte]
    iexfalso
    icombine Hg Hown gives %Hv
    exfalso
    cases Hv.2
  simp only [Bool.false_eq_true, ↓reduceIte]
  icombine Hg Hown gives %Heq
  obtain ⟨-, Heq⟩ := Heq
  have Heq' := Option.some.inj Heq
  subst Heq'
  wp_auto
  wp_apply (wp_map_lookup2 go.string (go.GoType.PointerType serviceInfo.ty) mp m name
    (DFrac.own 1)) $$ Hmap as Hmap
  have hnone : m !! name = none := by
    cases h : m !! name with
    | none => rfl
    | some _ => exact absurd (HR name (by simp [h])) Hn
  rw [hnone]
  simp only [Option.isSome_none, Bool.false_eq_true]
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoFunc) go.string MethodHandler.ty) as %mm Hmm
  ihave %HMslen := ownSlice_len $$ HMs
  ihave IH : (∃ (n : w64) (M : GMap GoString GoFunc) (dv : MethodDesc),
      "i" ∷ i_ptr ↦ n ∗ "d" ∷ d_ptr ↦ dv ∗ "Hmm" ∷ mm ↦$ M ∗ "HMs" ∷ msl ↦*{dq} Ms ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (Ms.length : Int) ∧
        ∀ (k : GoString) (h : GoFunc), M !! k = some h →
          ∃ (j : Nat) (d : MethodDesc), Ms[j]? = some d ∧ d.MethodName' = k ∧ d.Handler' = h⌝
      : IProp GF) $$ [i d Hmm HMs]
  · iexists _, ∅, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun k h hk => by simp at hk⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < Ms.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, Ms[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index msl (sint.Z n) Ms dq x Hn.1 $$ [HMs] as HMs
    · iframe; ipureintro; exact Hx
    wp_apply (wp_mapInsert go.string mm M x.MethodName' x.Handler') $$ Hmm as Hmm
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun k h hk => ?_⟩
    by_cases hkx : k = x.MethodName'
    · subst hkx
      rw [GMap.lookup_insert_eq] at hk
      cases hk
      exact ⟨_, x, Hx, rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkx)] at hk
      exact Hn.2.2 k h hk
  · irename «$r0» => Hinfo
    generalize «$r0_ptr» = info at *
    iStructNamed Hinfo
    ipersist impl
    ipersist methods
    imod ownMap_persist mm (DFrac.own 1) M $$ Hmm with #Hmm
    wp_apply (wp_mapInsert go.string mp m name info) $$ Hmap as Hmap
    imod ghostVar_update_halves (some (name :: R')) γ (some R') (some R') $$ Hg Hown with ⟨Hg, Hown⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (srvInv W a s mp γ)
      $$ [$Hsync $Hmu $Hlocked Hmap Hserve Hsvcs Hg]
    · unfold srvInv
      iexists _, false, name :: R'
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hmap Hserve Hg
      isplitl
      · iapply (BigSepM.bigSepM_insert (by rw [gmap_get?_eq]; exact hnone)).2
        iframe Hsvcs
        unfold svcOk
        iexists ss, mm, M
        iframe impl methods Hmm
        imodintro
        iintro %k %h %S %Hk
        obtain ⟨hk, hS⟩ := Hk
        obtain ⟨j, d, hd, hdk, hdh⟩ := Hn.2.2 k h hk
        subst hdk hdh
        iapply Hh $$ %j %d %S
        ipureintro; exact ⟨hd, hS⟩
      · ipureintro
        intro k hk
        by_cases hkn : k = name
        · subst hkn; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkn)] at hk
          exact List.mem_cons_of_mem _ (HR k hk)
    iapply HΦ
    iframe Hown
    iexists msl, ssl, Ms
    iframe Hname Hmsl HMs Hssl Hh
    ipureintro; exact Hssl0

end spec

end google_golang_org.grpc

end Perennial
