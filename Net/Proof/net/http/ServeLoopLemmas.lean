/-
Lemmas for `Server.Serve`'s proof (`Net/Proof/net/http/Server__Serve.lean`), on the server
`http.Serve` makes (`ServeLoopDefs.lean`):

* `wp_setupHTTP2_Serve`: no TLS configuration, so HTTP/2 is "configured" by the model's no-op
  (`onceSetNextProtoDefaults`), once (`sync.Once`); it returns `nextProtoErr`, `nil`.
* `wp_trackListener_add`/`_remove`: the listener tracked (`s.listeners`, under `s.mu`) and counted in
  `s.listenerGroup` (Perennial's `sync.join` wait-group protocol: `ownAdder`/`ownDone`), then
  untracked; the server is never shut down.
* `wp_newConn`: `&conn{server: s, rwc: rw}`, every other field zero (`connNew`'s).
* `wp_oclClose`: `onceCloseListener.Close`: the listener closed once (`sync.Once`, the net
  extension's `Listener.Close` through `lisClose_au`), its error kept.
* `wp_logf_argOk`: `s.logf` with no `ErrorLog`, i.e. `log.Printf`, on arguments Go's formatting calls
  only methods `fmt.stringMethodSpec` covers (`fmt.argOk`: Perennial's condition on `fmt`'s own,
  proved, formatting). Perennial's `log.Printf.spec` asks for `fmt.ArgsWf` (no method at all);
  `Accept`'s retry logs an `*OpError` and a `time.Duration` with `%v` (`notes/perennial-changes.md`):
  proved here from Perennial's model of `log.Printf` (`TrustedCode/log.lean`, which returns), as
  dsv-gryff's `log.wp_Printf_logArg`. `opError_argOk`, `duration_argOk`: the two arguments.
-/
module

public import Net.Proof.net.http.ServeLoopDefs
public import Net.Proof.net.http.ServerConnLemmas
public import Net.Proof.net.http.ServeLemmas
public import Net.Proof.net.Errors
public import Net.Spec.net.Listener__Close
public import Perennial.Proof.log.Base
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.fmt.Args

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `s.setupHTTP2_Serve()` with no `TLSConfig`: `nil`. -/
theorem wp_setupHTTP2_Serve (s : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        structFieldRef net.http.Server go!"TLSConfig" s ↦□ (null : Loc) ∗
        structFieldRef net.http.Server go!"nextProtoOnce" s ↦
          (_root_.Perennial.zero_val sync.Once) ∗
        structFieldRef net.http.Server go!"nextProtoErr" s ↦ (interface.nil : GoInterface) }}
      (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"setupHTTP2_Serve"))
        (Val #()))
    {{ RET #(interface.nil : GoInterface);
        structFieldRef net.http.Server go!"nextProtoErr" s ↦ (interface.nil : GoInterface) }} := by
  wp_start as ⟨#Htls, Honce, Herr⟩
  imod sync.init_Once (structFieldRef net.http.Server go!"nextProtoOnce" s) iprop(True)
    iprop(True) ⊤ $$ [Honce] with #Hio
  · iframe Honce
  try wp_auto
  wp_apply sync.Once.wp_Do $$ [$Hio]
  · wp_start as -
    try wp_auto
    wp_method_call
    try wp_auto
    wp_method_call
    try wp_auto
    iapply HΦ; itrivial
  try wp_auto
  iapply HΦ; iframe Herr

/-- `s.trackListener(ln, true)` on a server never shut down: tracked, counted. -/
theorem wp_trackListener_add (s ln : Loc) :
    {{ srvConst (GF := GF) s ∗ srvServe s ∗
        sync.join.ownAdder (structFieldRef net.http.Server go!"listenerGroup" s) (W32 0)
          iprop(True) }}
      (App (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"trackListener"))
        (Val #ln)) (Val #true))
    {{ RET #true;
        sync.join.ownDone (structFieldRef net.http.Server go!"listenerGroup" s) iprop(True) }} := by
  wp_start as ⟨#Hs, #Hss, Hadd⟩
  ihave #Hs' := Hs
  iunfold srvConst at Hs'
  icases Hs' with ⟨#Htime, #Hsync, #Hatomic, #Hmu, #Hcs⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold srvMuInv at Hinv
  icases Hinv with ⟨Hac, Hls⟩
  iunfold mapField at Hls
  icases Hls with ⟨%m, Hm, Hmm⟩
  try wp_auto
  icases Hmm with (%Hnil | ⟨%g, Hg⟩)
  · subst Hnil
    simp only [decide_true]
    wp_apply (wp_map_make1 (K := Loc) (V := Unit) _ _) as %m' Hg
    try wp_auto
    wp_apply wp_shuttingDown $$ [$Hss $Hatomic]
    try wp_auto
    wp_apply (wp_mapInsert (K := Loc) (V := Unit) _ _ _ ln ()) $$ [$Hg] as Hg
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) _ iprop(True) (W32 0))
      $$ [$Hsync $Hadd] as ⟨-, Hdone⟩
    · ipureintro; decide
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hac]
    · inext; iunfold srvMuInv; iframe Hac; iunfold mapField; iexists _; iframe Hm; iright; iexists _
      iexact Hg
    iapply HΦ; iexact Hdone
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hg
    simp only [Hnn, decide_false]
    try wp_auto
    wp_apply wp_shuttingDown $$ [$Hss $Hatomic]
    try wp_auto
    wp_apply (wp_mapInsert (K := Loc) (V := Unit) _ _ _ ln ()) $$ [$Hg] as Hg
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) _ iprop(True) (W32 0))
      $$ [$Hsync $Hadd] as ⟨-, Hdone⟩
    · ipureintro; decide
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hac]
    · inext; iunfold srvMuInv; iframe Hac; iunfold mapField; iexists _; iframe Hm; iright; iexists _
      iexact Hg
    iapply HΦ; iexact Hdone

/-- `s.trackListener(ln, false)`: untracked, the count given back. -/
theorem wp_trackListener_remove (s ln : Loc) :
    {{ srvConst (GF := GF) s ∗
        sync.join.ownDone (structFieldRef net.http.Server go!"listenerGroup" s) iprop(True) }}
      (App (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"trackListener"))
        (Val #ln)) (Val #false))
    {{ RET #true; True }} := by
  wp_start as ⟨#Hs, Hdone⟩
  ihave #Hs' := Hs
  iunfold srvConst at Hs'
  icases Hs' with ⟨#Htime, #Hsync, #Hatomic, #Hmu, #Hcs⟩
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold srvMuInv at Hinv
  icases Hinv with ⟨Hac, Hls⟩
  iunfold mapField at Hls
  icases Hls with ⟨%m, Hm, Hmm⟩
  try wp_auto
  icases Hmm with (%Hnil | ⟨%g, Hg⟩)
  · subst Hnil
    simp only [decide_true]
    wp_apply (wp_map_make1 (K := Loc) (V := Unit) _ _) as %m' Hg
    try wp_auto
    wp_apply (wp_mapDelete (K := Loc) (V := Unit) _ _ ln _ _) $$ [$Hg] as Hg
    wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) _)
      $$ [$Hsync $Hdone]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hac]
    · inext; iunfold srvMuInv; iframe Hac; iunfold mapField; iexists _; iframe Hm; iright; iexists _
      iexact Hg
    iapply HΦ; itrivial
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hg
    simp only [Hnn, decide_false]
    try wp_auto
    wp_apply (wp_mapDelete (K := Loc) (V := Unit) _ _ ln _ _) $$ [$Hg] as Hg
    wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) _)
      $$ [$Hsync $Hdone]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hac]
    · inext; iunfold srvMuInv; iframe Hac; iunfold mapField; iexists _; iframe Hm; iright; iexists _
      iexact Hg
    iapply HΦ; itrivial

/-- The connection `newConn` allocates (`&conn{server: s, rwc: rw}`), every other field zero. -/
abbrev connNewVal (s t : Loc) : net.http.conn :=
  { server' := s, cancelCtx' := func.nil,
    rwc' := interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t, remoteAddr' := [],
    tlsState' := null, werr' := interface.nil, r' := null, bufr' := null, bufw' := null,
    lastMethod' := [], curReq' := _root_.Perennial.zero_val _,
    curState' := _root_.Perennial.zero_val _, mu' := _root_.Perennial.zero_val _,
    hijackedv' := false }

/-- `s.newConn(rw)` of a `*TCPConn` `t`: a new connection (`connNewVal`). -/
theorem wp_newConn (s t : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"newConn"))
        (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t)))
    {{ (c : Loc), RET #c; ⌜c ≠ null⌝ ∗ c ↦ connNewVal s t }} := by
  wp_start as -
  try wp_auto
  ihave %hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iapply HΦ
  iframe «$r0»
  ipureintro; exact hnn

/-- A new connection is `connNew`'s (its server and `*TCPConn` read-only from then on). -/
theorem connNew_alloc (c s t : Loc) :
    (c ↦ connNewVal s t : IProp GF) ⊢ |==> connNew (GF := GF) c s t := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef, named]
  icases H with ⟨Hsrv, Hcc, Hrwc, Hra, Htls, Hwerr, Hr, Hbr, Hbw, Hlm, Hcr, Hcs, Hmu, Hhj, -⟩
  ipersist Hsrv
  ipersist Hrwc
  iunfold connNew
  iframe Hsrv Hrwc Hcc Hra Htls Hwerr Hr Hbr Hbw Hlm Hmu Hhj
  isplitl [Hcr]
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef
    iexact Hcr
  iexists (W64 0)
  rw [sync.atomic.ownUint64_unseal]; unfold sync.atomic.ownUint64Def
  have hz : (_root_.Perennial.zero_val sync.atomic.Uint64) =
      { «_#0'» := _root_.Perennial.zero_val _, «_#1'» := _root_.Perennial.zero_val _,
        v' := W64 0 : sync.atomic.Uint64 } := rfl
  rw [← hz]
  iexact Hcs

/-- An `*OpError` is an argument `fmt` formats through its `Error()` (`wp_OpError_Error`). -/
theorem opError_argOk (pe : Loc) (v : net.OpError) :
    (pe ↦□ v : IProp GF) ⊢
      fmt.argOk (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe) := by
  iintro #Hpe
  simp only [fmt.argOk]
  iright; ileft
  isplitl
  · rw [fmt.stringMethodSpec_unfold]
    imodintro
    iintro %Φ HΦ
    iapply wp_OpError_Error $$ Hpe
    inext
    iintro %msg -
    iapply HΦ
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType net.OpError.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType net.OpError.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [fmt.noArgStringSig] using h2⟩

/-- A `time.Duration` is an argument `fmt` formats through its `String()`
(`time.Duration.wp_String`). -/
theorem duration_argOk (d : time.Duration) :
    ⊢ fmt.argOk (GF := GF) (interface.mkOk time.Duration.ty #d) := by
  simp only [fmt.argOk]
  iright; iright
  isplitl
  · rw [fmt.stringMethodSpec_unfold]
    imodintro
    iintro %Φ HΦ
    iapply (time.Duration.wp_String d) $$ []
    · itrivial
    inext
    iintro %str -
    iapply HΦ
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"Error")
    have h3 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"String")
    have h4 := (go.MethodSetIs.method_set_is (t := time.Duration.ty) go!"CanInterface")
    simp only [go.methodSetLookup] at h1 h2 h3 h4
    exact ⟨by simpa using h1, by simpa using h2, by simpa [fmt.noArgStringSig] using h3,
      by simpa using h4⟩

/-- `s.logf(f, args...)` with no `ErrorLog`: `log.Printf`, on `fmt.argOk` arguments (see the file
header). -/
theorem wp_logf_argOk [log.Assumptions] (s : Loc) (f : GoString) (sl : GoSlice)
    (xs : List GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗
        structFieldRef net.http.Server go!"ErrorLog" s ↦□ (null : Loc) ∗ sl ↦* xs ∗
        □ ([∗list] x ∈ xs, fmt.argOk (GF := GF) x) }}
      (App (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"logf")) (Val #f))
        (Val #sl))
    {{ RET #(); sl ↦* xs }} := by
  wp_start as ⟨#Hel, Hsl, -⟩
  try wp_auto
  wp_func_call
  try wp_auto
  iapply HΦ; iexact Hsl

/-- `onceCloseListener`'s once-cell (`sync.Once`): its `closeErr`, `nil` until `close` ran, then
some error for good. -/
def oclOnce (oc : Loc) : IProp GF :=
  sync.isOnce (structFieldRef net.http.onceCloseListener go!"once" oc)
    iprop(structFieldRef net.http.onceCloseListener go!"closeErr" oc ↦ (interface.nil : GoInterface))
    iprop(∃ e : GoInterface, structFieldRef net.http.onceCloseListener go!"closeErr" oc ↦□ e)

instance oclOnce_persistent (oc : Loc) : Persistent (oclOnce (GF := GF) oc) := by
  unfold oclOnce; infer_instance

/-- `oc.Close()` on `Serve`'s `onceCloseListener` over this node's shared listener `l` at `la`:
closed (once), its error returned. -/
theorem wp_oclClose [net.Assumptions] [net.FieldAssumptions]
    (wp_Close : net.Listener.Close.spec (GF := GF) (hG := hG))
    (oc tl : Loc) (l : w64) (x : GoInterface) (la : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ oclOnce oc ∗
        structFieldRef net.http.onceCloseListener go!"Listener" oc ↦□
          interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #tl ∗
        lisAt (GF := GF) tl l x ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
        lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
      (App (Val #(methods (go.GoType.PointerType net.http.onceCloseListener.ty) go!"Close" #oc))
        (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  wp_start as ⟨#Ho, #Hl, #Hat, #Hon, #Hli⟩
  try wp_auto
  ihave #Ho' := Ho
  iunfold oclOnce at Ho'
  wp_apply sync.Once.wp_Do $$ [$Ho'] as ⟨%e, #He⟩
  · wp_start as Herr
    iapply wp_fupd
    try wp_auto
    wp_apply wp_Close tl l x la (fun _ => iprop(True)) $$ [$Hat $Hon]
      as %err ⟨%res, -, -⟩
    · iapply lisClose_au $$ Hli
    try wp_auto
    ipersist Herr
    iapply HΦ
    iexists _; iexact Herr
  try wp_auto
  iapply HΦ; itrivial

/-- `Serve`'s retry log: `s.logf(f, [err, tempDelay])` of an `*OpError` and a `time.Duration`. -/
theorem wp_logf_accept [log.Assumptions] (s : Loc) (f : GoString) (sl : GoSlice) (pe : Loc)
    (v : net.OpError) (d : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗
        structFieldRef net.http.Server go!"ErrorLog" s ↦□ (null : Loc) ∗ pe ↦□ v ∗
        sl ↦* [interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe,
          interface.mkOk time.Duration.ty #d] }}
      (App (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"logf")) (Val #f))
        (Val #sl))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨#Hel, #Hpe, Hsl⟩
  ihave #A1 := opError_argOk (GF := GF) (hG := hG) pe v $$ Hpe
  ihave #A2 := duration_argOk (GF := GF) d
  ihave #Hl : (□ ([∗list] x ∈ ([interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe,
      interface.mkOk time.Duration.ty #d] : List GoInterface), fmt.argOk (GF := GF) x) : IProp GF) $$ []
  · imodintro
    isplitl
    · iexact A1
    isplitl
    · iexact A2
    iapply (BigSepL.bigSepL_nil_intro (P := iprop(True)))
    itrivial
  wp_apply (wp_logf_argOk s f sl [interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe,
      interface.mkOk time.Duration.ty #d]) $$ [$Hel $Hsl $Hl] as -
  iapply HΦ; itrivial

/-- `serverHandler{s}.ServeHTTP` on net/rpc's `CONNECT` request: the server's handler (`effHandler`:
`DefaultServeMux` for none), as no `OPTIONS *` request is. -/
theorem srvHandler_intro (s : Loc) (h : GoInterface) (cn : Nat) (a : GoString) (P Q : Proto GF)
    (path : List w8) (hpath : reqPath path) :
    serveEnv (GF := GF) ∗ structFieldRef net.http.Server go!"Handler" s ↦□ h ∗
      structFieldRef net.http.Server go!"DisableGeneralOptionsHandler" s ↦□ false ∗
      connHandler (effHandler h) cn a P Q path ⊢
    srvHandler s cn a P Q path := by
  iintro ⟨#Hse, #Hh, #Hd, #Hc⟩
  iunfold srvHandler
  imodintro
  iintro %rp %req %rv %u %m %cl %nb %ctx %ra %D %Φ ⟨%Hrv, #Hhead, Hrest, Hu, Hm, Hhj, Htok⟩ HΦ
  iunfold serveEnv at Hse
  icases Hse with ⟨-, #Hdm⟩
  iunfold reqRest at Hrest
  icases Hrest with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17,
    H18, H19, H20, H21, H22, H23, H24⟩
  have hstar : decide (rv.RequestURI' = go!"*") = false := by
    subst Hrv
    simp only [decide_eq_false_iff_not]
    intro h
    have h1 := hpath.1
    simp only [rrReqVal, connectReqVal] at h
    rw [h] at h1
    simp at h1
  wp_method_call
  try wp_auto
  iunfold connHandler at Hc
  icases Hc with ⟨%ii, %Hii, #Hw⟩
  cases h with
  | nil =>
    try wp_auto
    simp only [hstar]
    try wp_auto
    simp only [effHandler] at Hii
    cases ii
    cases Hii
    wp_bind (App (App (Val #(methods _ _ _)) _) _)
    iapply Hw $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
      H23 H24 Hu Hm Hhj Htok]
    · iframe Hhead Hu Hm Hhj Htok
      isplitr
      · ipureintro; exact Hrv
      iunfold reqRest
      iframe
    inext
    iintro Hr
    try wp_auto
    iapply HΦ $$ Hr
  | ok i0 =>
    try wp_auto
    simp only [hstar]
    try wp_auto
    simp only [effHandler] at Hii
    cases Hii
    wp_bind (App (App (Val #(methods _ _ _)) _) _)
    iapply Hw $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
      H23 H24 Hu Hm Hhj Htok]
    · iframe Hhead Hu Hm Hhj Htok
      isplitr
      · ipureintro; exact Hrv
      iunfold reqRest
      iframe
    inext
    iintro Hr
    try wp_auto
    iapply HΦ $$ Hr

end lemmas

end net.http
end Perennial
