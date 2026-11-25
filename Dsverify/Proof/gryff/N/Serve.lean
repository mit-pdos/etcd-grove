/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Serve.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: `genericsmr.(*Replica).serveClient` (proof of `Replica2/Specs.lean`'s
`Replica.serveClient.wp`)

The connection's writer is registered under `clientIdMapsLock` (the escrow invariant gets the
writer, the lock's invariant the connection's `clientConnAt` / `placedConn`; a second
registration of the client id is refuted by `placedConn_fresh`). Each request read from the
client's stream (`clientReqsOk`: its opcode is a request's, `clientReqs_next`) gets its token
(`clientReqsOk_elim`, `req_mint`) and goes, with it, on its kind's channel (`reqChanP`).
-/
module

public import Dsverify.Proof.gryff.N.Listener
public import Dsverify.Proof.gryff.N.Reply
public import Dsverify.Proof.gryff.N.WireInj
public import Dsverify.Proof.gryff.Server.LogErr
public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.N.ConnErr
public import Dsverify.Proof.gryff.N.NetSpecs
public import Dsverify.Proof.gryff.N.ConnLaws
public import Dsverify.Proof.gryff.Lib.NetAddr
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg Out Ev)
open wire wire.gryffproto Perennial.gryff.netN

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF]

/-! ## The request grammar (pure) -/

theorem reqShape_iff_D {c : w8} {m : List w8} : reqShape c m ↔ reqShapeD c m := Iff.rfl

/-- After whole requests, the next byte of a stream of whole requests is a request's opcode. -/
theorem next_code {P B : List (List w8)} {c : w8} {rest : List w8}
    (hP : ∀ x ∈ P, ∃ d, reqShapeD d x) (hB : ∀ y ∈ B, ∃ d, reqShapeD d y)
    (h : P.flatten ++ c :: rest = B.flatten) : c = W8 24 ∨ c = W8 26 ∨ c = W8 22 := by
  obtain ⟨C, rfl⟩ := reqs_flatten_prefix P B (c :: rest) hP hB h
  rw [List.flatten_append] at h
  have h' := List.append_cancel_left h
  cases C with
  | nil => simp at h'
  | cons x C =>
    obtain ⟨d, hd⟩ := hB x (by simp)
    obtain ⟨-, hhd⟩ := reqShapeD_len hd
    cases x with
    | nil => simp at hhd
    | cons a x =>
      simp only [List.head?_cons, Option.some.injEq] at hhd
      simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at h'
      obtain ⟨rfl, -⟩ := h'
      subst hhd
      rcases hd with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)

theorem read_app_inj {a b : Read.Msg} {l1 l2 : List w8}
    (h : Read.enc a ++ l1 = Read.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Read.enc h
theorem write_app_inj {a b : Write.Msg} {l1 l2 : List w8}
    (h : Write.enc a ++ l1 = Write.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Write.enc h
theorem rmw_app_inj {a b : RMW.Msg} {l1 l2 : List w8}
    (h : RMW.enc a ++ l1 = RMW.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj RMW.enc h

theorem read_enc_inj {a b : Read.Msg} (h : Read.enc a = Read.enc b) : a = b :=
  (read_app_inj (l1 := []) (l2 := []) (by simpa using h)).1
theorem write_enc_inj {a b : Write.Msg} (h : Write.enc a = Write.enc b) : a = b :=
  (write_app_inj (l1 := []) (l2 := []) (by simpa using h)).1
theorem rmw_enc_inj {a b : RMW.Msg} (h : RMW.enc a = RMW.enc b) : a = b :=
  (rmw_app_inj (l1 := []) (l2 := []) (by simpa using h)).1

/-- The request kind of an opcode. -/
def codeKind (c : w8) : String :=
  if c = W8 24 then "read" else if c = W8 26 then "write" else "rmw"

theorem codeKind_mem (c : w8) : codeKind c ∈ reqKinds := by
  unfold codeKind reqKinds
  by_cases h1 : c = W8 24
  · rw [if_pos h1]; simp
  · rw [if_neg h1]
    by_cases h2 : c = W8 26
    · rw [if_pos h2]; simp
    · rw [if_neg h2]; simp

theorem reqCode_codeKind {c : w8} (h : c = W8 24 ∨ c = W8 26 ∨ c = W8 22) :
    reqCode (codeKind c) = c := by
  rcases h with rfl | rfl | rfl <;> decide



/-- The next opcode on a client's stream (after whole requests `P`) is a request's (unfolds
stage 1's `clientReqsOk`). -/
theorem clientReqs_next (γ : GryffNames GF) (hs : w32) (last : Int) (body : List w8)
    (P : List (List w8)) (c : w8) (hP : ∀ x ∈ P, ∃ d, reqShape d x)
    (hY : P.flatten ++ [c] <+: body) :
    clientReqsOk γ hs last body ⊢ ⌜c = W8 24 ∨ c = W8 26 ∨ c = W8 22⌝ := by
  unfold clientReqsOk clientReqsBody
  iintro ⟨%ms, %hms, -⟩
  ipureintro
  obtain ⟨hb, hok, -, -⟩ := hms
  obtain ⟨rest, hrest⟩ := hY
  refine next_code hP (B := ms.map (fun x => x.2.2)) ?_ (rest := rest) ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact reqBytesD_shape (hok x hx)
  · rw [← hb, ← hrest]; simp

/-- A reader over a client's stream (after its handshake `u32Le hs`): what it returned is a prefix
of whole requests of the client (`clientConnIn`'s peek, an update of the reader resource). -/
theorem ownReader_client (γ : GryffNames GF) (hs : w32) (br : Loc) (rd : wire.RSt GF)
    (I : List w8 → IProp GF) (Y : List w8) :
    wire.ownReader br rd I (u32Le hs ++ Y) ∗
        □ (∀ Y', wire.ownReader br rd I (u32Le hs ++ Y') ={⊤}=∗ wire.ownReader br rd I (u32Le hs ++ Y') ∗
          ∃ (last : Int) (body : List w8), clientReqsOk γ hs last body ∗ ⌜Y' <+: body⌝) ⊢
      |={⊤}=> wire.ownReader br rd I (u32Le hs ++ Y) ∗
        ∃ (last : Int) (body : List w8), clientReqsOk γ hs last body ∗ ⌜Y <+: body⌝ := by
  iintro ⟨H, #Hbr⟩
  iapply Hbr $$ H

/-- `reqTy` as the pointer type in `reqChanP`. -/
theorem reqTy_eq (kd : String) :
    reqTy kd = go.GoType.PointerType (if kd = "read" then src.gryffproto.Read.ty
      else if kd = "write" then src.gryffproto.Write.ty else src.gryffproto.RMW.ty) := by
  unfold reqTy
  by_cases h1 : kd = "read"
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : kd = "write"
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]

/-- A fresh request struct of kind `kd` at `l` (`New`'s result). -/
def freshReq (kd : String) (l : Loc) : IProp GF :=
  if kd = "read" then iprop(∃ v : src.gryffproto.Read, l ↦ v)
  else if kd = "write" then iprop(∃ v : src.gryffproto.Write, l ↦ v)
  else iprop(∃ v : src.gryffproto.RMW, l ↦ v)

/-- A decoded request struct of kind `kd` at `l`, whose bytes (with the opcode) are `x`. -/
def decReq (kd : String) (l : Loc) (x : List w8) : IProp GF :=
  if kd = "read" then iprop(∃ g : src.gryffproto.Read, l ↦ g ∗ ⌜x = W8 24 :: Read.enc g⌝)
  else if kd = "write" then iprop(∃ g : src.gryffproto.Write, l ↦ g ∗ ⌜x = W8 26 :: Write.enc g⌝)
  else iprop(∃ g : src.gryffproto.RMW, l ↦ g ∗ ⌜x = W8 22 :: RMW.enc g⌝)

theorem reqKinds_cases {kd : String} (h : kd ∈ reqKinds) :
    kd = "read" ∨ kd = "write" ∨ kd = "rmw" := by
  simpa [reqKinds] using h

set_option goose.wp.extras true

/-- `obj.New()` for a registered request object of kind `kd`. -/
theorem wp_New_req (kd : String) (hkd : kd ∈ reqKinds) (obj : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto }}
      (App (Val (obj @!! reqTy kd @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (reqTy kd) #l); freshReq kd l }} := by
  rcases reqKinds_cases hkd with rfl | rfl | rfl
  all_goals
    simp only [reqTy, freshReq]
    simp only [↓reduceIte, String.reduceEq]
    wp_start
    wp_auto
    try wp_alloc l as Hl
    try wp_auto
    iapply HΦ
    iexists _; iframe

/-- `obj.Unmarshal(reader)` for a fresh request struct of kind `kd`. -/
theorem wp_Unmarshal_req (kd : String) (hkd : kd ∈ reqKinds) (l br : Loc) (rd : wire.RSt GF)
    (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        wire.readerOk rd I ∗ wire.ownReader br rd I R ∗ freshReq kd l }}
      (App (Val (l @!! reqTy kd @!! go!"Unmarshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ e : List w8, decReq kd l (reqCode kd :: e) ∗
          wire.ownReader br rd I (R ++ e)) ∨
        (⌜err ≠ interface.nil⌝ ∗ wire.rdErr rd err ∗ ∃ R' : List w8,
          wire.ownReader br rd I (R ++ R')) }} := by
  rcases reqKinds_cases hkd with rfl | rfl | rfl
  · simp only [reqTy, freshReq, decReq, reqCode, ↓reduceIte, String.reduceEq]
    iintro %Φ ⟨#Hg, #Hb, #Hio, #Hrd, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (Read.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, #He, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Read.enc g
      iframe Hown
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      iframe He
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  · simp only [reqTy, freshReq, decReq, reqCode, ↓reduceIte, String.reduceEq]
    iintro %Φ ⟨#Hg, #Hb, #Hio, #Hrd, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (Write.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, #He, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists Write.enc g
      iframe Hown
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      iframe He
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown
  · simp only [reqTy, freshReq, decReq, reqCode, ↓reduceIte, String.reduceEq]
    iintro %Φ ⟨#Hg, #Hb, #Hio, #Hrd, Hown, ⟨%v0, Hl⟩⟩ HΦ
    wp_apply (RMW.wp_Unmarshal l v0 br rd I R) $$ [$Hrd $Hown $Hl]
      as %err (⟨%Herr, %g, %Hwf, Ho, Hown⟩ | ⟨%Herr, #He, %v, %R', Hl, Hown⟩)
    · iframe #
      iapply wire.readNext_true; intro; trivial
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact Herr
      iexists RMW.enc g
      iframe Hown
      iexists g; iframe Ho; ipureintro; rfl
    · iapply HΦ
      iright
      iframe He
      isplitr
      · ipureintro; exact Herr
      iexists R'; iframe Hown

instance msgsOk_clientReply_persistent (γ : GryffNames GF) (hs : w32) (Y : List w8) :
    Persistent (msgsOk (clientReplyOk γ hs) Y) := by
  unfold msgsOk; infer_instance

theorem evTok_of_clientReq (γp : ProtoNames) (k : Fin 3) (e : Ev) (cid rid : w32)
    (i : dsverify_lab.harness.RegInput w64) (h : e.clientReq = some (cid, rid, i)) :
    (evTok γp k e : IProp GF) = reqTok γp k (sint.Z cid, sint.Z rid) i := by
  cases e <;> simp_all [evTok, Ev.clientReq]

theorem decReq_shape (kd : String) (hkd : kd ∈ reqKinds) (l : Loc) (x : List w8) :
    decReq (GF := GF) kd l x ⊢ decReq kd l x ∗ ⌜reqShape (reqCode kd) x⌝ := by
  rcases reqKinds_cases hkd with rfl | rfl | rfl
  all_goals
    simp only [decReq, reqCode, ↓reduceIte, String.reduceEq]
    iintro ⟨%g, Hg, %hx⟩
    isplitl
    · iexists g; iframe Hg; ipureintro; exact hx
    ipureintro
    subst hx
    unfold reqShape
    first
    | exact Or.inl ⟨rfl, g, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, g, rfl⟩)
    | exact Or.inr (Or.inr ⟨rfl, g, rfl⟩)

theorem sintZ_nonneg_of_lt_peerMark {hs : w32} (h : hs < peerMark) : 0 ≤ sint.Z hs := by
  unfold peerMark at h
  have : hs.toNat < 2 ^ 31 := h
  simp only [sint.Z]
  rw [BitVec.toInt_eq_toNat_of_msb]
  · omega
  · rw [BitVec.msb_eq_decide]; simp; omega

theorem sintZ_neg1 : sint.Z (W64 (-1)) < 0 := by decide

/-- A decoded request of a client's grammar (`reqBytesOk`) is its request event, of the shape a
replica's step accepts (`Ev.Producible`). -/
theorem req_of_dec (kd : String) (hkd : kd ∈ reqKinds) (l : Loc) (x : List w8) (hs req : w32)
    (i : dsverify_lab.harness.RegInput w64) (hb : reqBytesOk hs req i x) (h0 : 0 ≤ sint.Z hs) :
    decReq (GF := GF) kd l x ⊢ ∃ e : Ev, reqAt kd l e ∗ ⌜e.clientReq = some (hs, req, i) ∧ e.Producible⌝ := by
  rcases reqKinds_cases hkd with rfl | rfl | rfl
  · simp only [decReq, ↓reduceIte, String.reduceEq]
    iintro ⟨%g, Hg, %hx⟩
    subst hx
    cases i with
    | read =>
      obtain ⟨r, hm, h1, h2, h3, h4⟩ := hb
      have := read_enc_inj (List.cons.inj hm).2
      subst this
      iexists readEvOf g
      isplitl
      · unfold reqAt; simp only [↓reduceIte, String.reduceEq]; iexists g; iframe Hg; ipureintro; rfl
      ipureintro
      refine ⟨by simp [readEvOf, Ev.clientReq, h1, h2], ?_⟩
      simp only [readEvOf, Ev.Producible, depOf, h2, h3, h4]
      exact ⟨rfl, sintZ_neg1, h0⟩
    | write v =>
      obtain ⟨r, hm, -⟩ := hb
      exact absurd (List.cons.inj hm).1 (by decide)
    | cas o n =>
      obtain ⟨r, hm, -⟩ := hb
      exact absurd (List.cons.inj hm).1 (by decide)
  · simp only [decReq, ↓reduceIte, String.reduceEq]
    iintro ⟨%g, Hg, %hx⟩
    subst hx
    cases i with
    | read =>
      obtain ⟨r, hm, -⟩ := hb
      exact absurd (List.cons.inj hm).1 (by decide)
    | write v =>
      obtain ⟨r, hm, h1, h2, h3, h5, h4⟩ := hb
      have := write_enc_inj (List.cons.inj hm).2
      subst this
      iexists writeEvOf g
      isplitl
      · unfold reqAt; simp only [↓reduceIte, String.reduceEq]; iexists g; iframe Hg; ipureintro; rfl
      ipureintro
      refine ⟨by simp [writeEvOf, Ev.clientReq, h1, h2, h5], ?_⟩
      simp only [writeEvOf, Ev.Producible, depOf, h2, h3, h4]
      exact ⟨rfl, sintZ_neg1, h0⟩
    | cas o n =>
      obtain ⟨r, hm, -⟩ := hb
      exact absurd (List.cons.inj hm).1 (by decide)
  · simp only [decReq, ↓reduceIte, String.reduceEq]
    iintro ⟨%g, Hg, %hx⟩
    subst hx
    cases i with
    | read =>
      obtain ⟨r, hm, -⟩ := hb
      exact absurd (List.cons.inj hm).1 (by decide)
    | write v =>
      obtain ⟨r, hm, -⟩ := hb
      exact absurd (List.cons.inj hm).1 (by decide)
    | cas o n =>
      obtain ⟨r, hm, h1, h2, h3, h5, h6, h4⟩ := hb
      have := rmw_enc_inj (List.cons.inj hm).2
      subst this
      iexists rmwEvOf g
      isplitl
      · unfold reqAt; simp only [↓reduceIte, String.reduceEq]; iexists g; iframe Hg; ipureintro; rfl
      ipureintro
      refine ⟨by simp [rmwEvOf, Ev.clientReq, h1, h2, h5, h6], ?_⟩
      simp only [rmwEvOf, Ev.Producible, depOf, h2, h3, h4]
      exact ⟨rfl, sintZ_neg1, h0⟩

/-- The client writers' escrow invariant's body (`genericOk`). -/
abbrev escrowBody (γ : GryffNames GF) (ρ : Repl2Names) : IProp GF :=
  iprop(∃ WM : GMap w32 Loc, ghostMapAuth ρ.writers (1 : Qp).half WM ∗
    [∗map] hs ↦ w ∈ WM, netN.clientWriterB γ hs w ∨
      ghostMapElem (escrowName ρ) hs (DFrac.own 1) w)

/-- The client-map lock's invariant (`genericOk`). -/
abbrev clientMapsInv (γ : GryffNames GF) (ρ : Repl2Names) (crm cwm : Loc) : IProp GF :=
  iprop(∃ (RM WM : GMap w32 Loc), crm ↦$ RM ∗ cwm ↦$ WM ∗
    ghostMapAuth ρ.writers (1 : Qp).half WM ∗
    [∗map] hs ↦ _w ∈ WM, ∃ c : Nat, clientConnAt γ hs c ∗ placedConn γ c)

/-- What `serveClient` reads of the generic replica's fixed parts. -/
theorem genericOk_serve (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ ∃ (ct st mu cwm crm : Loc) (CM : GMap w8 Loc),
      gR.[src.genericsmr.Replica, go!"clientRpcTable"] ↦□ ct ∗ ct ↦${DFrac.discard} CM ∗
      □ ([∗list] kd ∈ reqKinds, ∃ (c : w8) (pp obj ch : Loc),
        ⌜reqCode kd = c ∧ CM !! c = some pp⌝ ∗
        pp ↦□ src.genericsmr.ClientRPCPair.mk (interface.mkOk (reqTy kd) #obj) ch ∗
        isChanBag (ρ.chans kd) ch (reqChanP γ ρ k kd)) ∗
      gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ □ netN.statsOkB st ∗
      gR.[src.genericsmr.Replica, go!"clientIdMapsLock"] ↦□ mu ∗
      gR.[src.genericsmr.Replica, go!"clientWriters"] ↦□ cwm ∗
      gR.[src.genericsmr.Replica, go!"clientReaders"] ↦□ crm ∗
      sync.isMutex mu (clientMapsInv γ ρ crm cwm) ∗
      inv netN.escrowN (escrowBody γ ρ) ∗
      gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
      gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto := by
  unfold genericOk
  iintro #H
  icases H with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, -, -, -, #Hct, #HCM, #Hctab, #Hst,
    #Hsto, #Hmu, #Hcw, #Hcr, #Hmx, #Hinv, #HId, #HSh, -, #Hg, -, -⟩
  iexists ct, st, mu, cwm, crm, CM
  iframe #

/-- Registering client `hs`'s writer `w` (connection `c`, freshly accepted), under the client-map
lock: a second registration of `hs` is refuted (`placedConn_fresh`); the escrow invariant gets
the writer, the lock's invariant `c`'s binding; the acceptor's placing right. -/
theorem register_ghost (γ : GryffNames GF) (ρ : Repl2Names) (hs : w32) (c : Nat) (w : Loc)
    (WM : GMap w32 Loc) :
    inv netN.escrowN (escrowBody γ ρ) ∗ □ protoInvs γ ∗ clientConnAt γ hs c ∗
        connFresh c true ∗ netN.clientWriterB γ hs w ∗
        ghostMapAuth ρ.writers (1 : Qp).half WM ∗
        ([∗map] hs ↦ _w ∈ WM, ∃ c : Nat, clientConnAt γ hs c ∗ placedConn γ c) ⊢
      |={⊤}=> ghostMapAuth ρ.writers (1 : Qp).half (WM.insert hs w) ∗
        ([∗map] hs ↦ _w ∈ WM.insert hs w, ∃ c : Nat, clientConnAt γ hs c ∗ placedConn γ c) ∗
        writerIs ρ hs w ∗ placeRight γ c (-1) := by
  iintro ⟨#Hinv, #Hsh, #Hca, Hfresh, Hcw, Hauth, Hpl⟩
  cases hWM : WM !! hs with
  | some w0 =>
    ihave ⟨%c0, #Hca0, #Hpc0⟩ := (BigSepM.bigSepM_lookup
      (Φ := fun hs (_ : Loc) => iprop(∃ c : Nat, clientConnAt γ hs c ∗ placedConn γ c)) hWM) $$ Hpl
    ihave %Heq := clientConnAt_agree γ hs c c0 $$ [Hca Hca0]
    · iframe #
    subst Heq
    imod placedConn_fresh γ c $$ [Hpc0 Hfresh] with H
    · iframe Hfresh Hpc0
    iexfalso; iexact H
  | none =>
    imod placeRight_intro_placed γ c $$ [Hsh Hfresh] with ⟨Hpr, #Hpc⟩
    · iframe Hfresh Hsh
    iinv Hinv with Hi Hclose
    icases Hi with ⟨%WM', >HA, Hm⟩
    ihave %Hag := ghostMapAuth_agree ρ.writers _ _ WM WM' $$ Hauth HA
    subst Hag
    ihave Hfull := (ghostMapAuth_halves ρ.writers WM).2 $$ [Hauth HA]
    · iframe Hauth HA
    imod ghost_map_insert_persist hs w hWM $$ Hfull with ⟨Hfull, #Hel⟩
    icases (ghostMapAuth_halves ρ.writers (WM.insert hs w)).1 $$ Hfull with ⟨H1, H2⟩
    imod Hclose $$ [H2 Hm Hcw] with -
    · inext
      iexists WM.insert hs w
      iframe H2
      iapply (BigSepM.bigSepM_insert hWM).2
      isplitl [Hcw]
      · ileft; iexact Hcw
      · iexact Hm
    imodintro
    iframe H1 Hpr
    isplitl [Hpl]
    · iapply (BigSepM.bigSepM_insert hWM).2
      isplitr
      · iexists c; iframe #
      · iexact Hpl
    · unfold writerIs; iexact Hel

end

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF] [net.Assumptions] [netN.NetSpecs GF]

set_option hygiene false in
/-- `serveClient`'s exit: `if err != nil && err != io.EOF { log.Printf(...) }` (`Herr`: the
error's `errAny`, `Hptr`: it is pointer-typed). -/
macro "serve_exit" : tactic => `(tactic| (
  ihave #Heof := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold errors.newVar at Heof
  icases Heof with ⟨%x, #Hx, -⟩
  icombine HEOFv Hx gives %HeqE
  subst HeqE
  try wp_auto
  by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
  · obtain ⟨l, hl⟩ := Hptr ei _ rfl hty
    simp only [hty, ↓reduceIte]
    rw [hl]
    wp_auto
    by_cases hlx : l = x
    · subst hlx
      simp only [_root_.decide_true, Bool.not_true]
      wp_auto
      iapply HΦ; itrivial
    rw [decide_eq_false hlx]
    simp only [Bool.not_false]
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
    · iframe
      iintro !>
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_string
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ Herr
    try wp_auto
    iapply HΦ; itrivial
  · simp only [hty, ↓reduceIte]
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply log.wp_Printf_logArg _ _ _ _ $$ [Hasl] as -
    · iframe
      iintro !>
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set_cons_succ, List.set_cons_zero]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply logArg_string
      iapply BigSepL.bigSepL_singleton.2
      iapply logArg_err $$ Herr
    try wp_auto
    iapply HΦ; itrivial))

set_option goose.wp.extras true

theorem serveClient_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR : Loc)
    (conn : GoInterface) (rd : Loc) (hs : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ clientConnIn γ ρ k conn rd hs ∗
        ⌜hs < peerMark⌝ }}
      (App (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"serveClient"))
        (Val #conn)) (Val #rd)) (Val #hs))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrep, #HgR, Hcc, %Hhs⟩
  ihave Hr := (isReplica_open ..).1 $$ Hrep
  icases Hr with ⟨%gR2, %h, #Hex, #HgR2, -, -, -, -, -, -, -, #Hgen⟩
  icombine HgR HgR2 gives %Heq
  subst Heq
  ihave ⟨%ct, %st, %mu, %cwm, %crm, %CM, #Hct, #HCM, #Hctab, #Hst, #Hsto, #Hmuf, #Hcwf, #Hcrf,
    #Hmu, #Hesc, #HId, #HSh, #Hgp⟩ := genericOk_serve γ ρ k r gR h $$ Hgen
  iunfold clientConnIn at Hcc
  icases Hcc with ⟨%t, %c, %a, %a0, %la, %ra, %ed, %eof, %I, %Hconn, #Hcat, #HEOFv, #Hrdok, Hown,
    #Hbr, #Hwok, Hsend, #Hbridge, #Hca, Hfresh, #Hsh⟩
  obtain ⟨Htc, -⟩ := Hconn
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  -- the writer
  ihave #HQ0 : iprop(□ gryffWireQ γ a0 c []) $$ []
  · imodintro
    iapply (gryffWireQ_closed γ a0).nil c
  subst Htc
  wp_auto
  rw [show (interface.mkOk (go.GoType.PointerType Perennial.net.TCPConn.ty) #t : GoInterface) =
    GoInterface.ok (Perennial.net.connIface t) from rfl]
  wp_apply (wire.wp_NewWriter ⟨Perennial.net.connIface t, Perennial.net.connWriteE la ra ed, 4096⟩
    (sendTok c true (gryffWireQ γ a0)) (gryffWireQ γ a0 c) [] rfl
    (Perennial.net.connIface_ne_bufioWriter t)) $$ [Hsend] as %w Hw
  · iframe Hsend; iframe #
  -- the client's writer, for the escrow
  ihave Hcw : netN.clientWriterB γ hs w $$ [Hw]
  · iunfold netN.clientWriterB
    iexists ⟨Perennial.net.connIface t, Perennial.net.connWriteE la ra ed, 4096⟩,
      sendTok c true (gryffWireQ γ a0), gryffWireQ γ a0 c, [], [], [], interface.nil
    iframe Hwok Hw
    isplitr
    · ipureintro; simp
    isplitr
    · imodintro
      unfold msgsOk
      iexists []
      isplitr
      · ipureintro; simp
      · iapply BigSepL.bigSepL_nil.2; iempintro
    imodintro
    iintro %Y #HY
    ihave #HQ := Hbridge $$ HY
    imodintro
    iexact HQ
  -- register the writer under the client-map lock
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, ⟨%RM, %WM, Hrm, Hwm, Hauth, Hpl⟩⟩
  iapply fupd_wp
  imod register_ghost γ ρ hs c w WM $$ [Hcw Hfresh Hauth Hpl] with ⟨Hauth, Hpl, #Hwi, Hpr⟩
  · iframe Hcw Hfresh Hauth Hpl; iframe #
  imodintro
  wp_apply (wp_mapInsert (V := Loc) go.int32 crm RM hs rd) $$ Hrm as Hrm
  try wp_auto
  wp_apply (wp_mapInsert (V := Loc) go.int32 cwm WM hs w) $$ Hwm as Hwm
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hrm Hwm Hauth Hpl]
  · iexists _, _; iframe
  try wp_auto
  -- the requests
  ihave IH : iprop(∃ (mt : w8) (e : GoInterface) (es : GoString),
      "msgType" ∷ msgType_ptr ↦ mt ∗ "err" ∷ err_ptr ↦ e ∗ "errS" ∷ errS_ptr ↦ es ∗
      "Hst" ∷ ((⌜e = interface.nil⌝ ∗ ∃ (P : List (List w8)) (last : Int),
          wire.ownReader rd ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩ I
            (u32Le hs ++ P.flatten) ∗
          ⌜∀ x ∈ P, ∃ d, reqShape d x⌝ ∗ placeRight γ c last ∗
          (⌜last < 0⌝ ∨ connRepIs γ.proto c k) ∗
          ⌜last = -1 ∨ (0 ≤ last ∧ ∃ x ∈ P, ∃ r j, reqBytesOk hs r j x ∧ sint.Z r = last)⌝) ∨
        (⌜e ≠ interface.nil⌝ ∗ models_lab.errAny e ∗ ⌜_root_.Perennial.io.ptrTyped e⌝)))
      $$ [msgType err errS Hown Hpr]
  · iexists _, _, _
    iframe msgType err errS
    ileft
    isplitr
    · ipureintro; rfl
    iexists [], -1
    simp only [List.flatten_nil, List.append_nil]
    iframe Hown Hpr
    isplitr
    · ipureintro; simp
    isplitr
    · ileft; ipureintro; omega
    ipureintro; simp
  wp_for IH
  icases Hst with (⟨%He, %P, %last, Hown, %HP, Hpr, Hrepk, %Hlast⟩ | ⟨%He, #Herr, %Hptr⟩)
  rotate_left
  · -- an error: the loop ends
    obtain ⟨ei, rfl⟩ : ∃ ei, e = interface.ok ei := by
      cases e with
      | nil => exact absurd rfl He
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    rw [dec_ft]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_true]
    wp_auto
    serve_exit
  subst He
  wp_auto
  rw [dec_tt]
  simp only [↓reduceIte]
  wp_auto
  wp_apply (wire.wp_ReadByte rd ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩
    I (u32Le hs ++ P.flatten)) $$ [$Hrdok $Hown]
    as %c0 %err (⟨%Herr, Hown⟩ | ⟨%He, #Hrerr, Hown⟩)
  rotate_left
  · -- a read error: the loop ends
    ihave ⟨#Herr, %Hptr⟩ := netN.rdErr_conn' t eof la ra ed err $$ [$Hrerr $Hio $Hbin $HEOFv]
    obtain ⟨ei, rfl⟩ : ∃ ei, err = interface.ok ei := by
      cases err with
      | nil => exact absurd rfl He
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    wp_for_post
    serve_exit
  subst Herr
  wp_auto
  -- the next opcode is a request's
  iapply fupd_wp
  imod ownReader_client γ hs rd _ I (P.flatten ++ [c0]) $$ [Hown]
    with ⟨Hown, %last', %body, #Hreqs, %Hbody⟩
  · rw [← List.append_assoc]; iframe Hown Hbr
  imodintro
  ihave %Hc0 := clientReqs_next γ hs last' body P c0 HP Hbody $$ Hreqs
  have hc0 : c0 ≠ W8 0 ∧ c0 ≠ W8 2 ∧ c0 ≠ W8 4 := by
    rcases Hc0 with rfl | rfl | rfl <;> decide
  rw [← List.append_assoc]
  rw [decide_eq_false hc0.1]
  wp_auto
  rw [decide_eq_false hc0.2.1]
  wp_auto
  rw [decide_eq_false hc0.2.2]
  wp_auto
  -- the client table's entry for the request's kind
  obtain ⟨kd, hkd, hcode⟩ : ∃ kd, kd ∈ reqKinds ∧ reqCode kd = c0 :=
    ⟨codeKind c0, codeKind_mem c0, reqCode_codeKind Hc0⟩
  ihave #Hent := BigSepL.bigSepL_mem hkd $$ Hctab
  icases Hent with ⟨%c', %pp, %obj, %ch, %Hc', #Hpp, #Hbag⟩
  obtain ⟨hcc, hpp⟩ := Hc'
  rw [hcode] at hcc
  subst hcc
  wp_apply (wp_map_lookup2 (V := Loc) go.uint8 _ ct CM c0 DFrac.discard) $$ [HCM] as -
  · iexact HCM
  rw [hpp]
  simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
  iStructNamed Hpp
  wp_auto
  wp_apply (wp_New_req kd hkd obj) $$ [Hgp] as %l Hfresh
  wp_apply (wp_Unmarshal_req kd hkd l rd _ I (u32Le hs ++ P.flatten ++ [c0]))
    $$ [Hown Hfresh] as %err2 (⟨%Herr2, %e, Hdec, Hown⟩ | ⟨%He, #Hrerr, %R', Hown⟩)
  · iframe; iframe #
  rotate_left
  · -- an unmarshaling error: the loop ends
    ihave ⟨#Herr, %Hptr⟩ := netN.rdErr_conn' t eof la ra ed err2 $$ [$Hrerr $Hio $Hbin $HEOFv]
    obtain ⟨ei, rfl⟩ : ∃ ei, err2 = interface.ok ei := by
      cases err2 with
      | nil => exact absurd rfl He
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    iright
    iframe Herr
    ipureintro; exact ⟨He, Hptr⟩
  subst Herr2
  -- the request's token
  ihave ⟨Hdec, %Hshape⟩ := decReq_shape kd hkd l _ $$ Hdec
  iapply fupd_wp
  imod ownReader_client γ hs rd _ I (P.flatten ++ (reqCode kd :: e)) $$ [Hown]
    with ⟨Hown, %last2, %body2, #Hreqs2, %Hbody2⟩
  · rw [hcode, show u32Le hs ++ (P.flatten ++ c0 :: e) = u32Le hs ++ P.flatten ++ [c0] ++ e by
      simp]
    iframe Hown Hbr
  imodintro
  obtain ⟨post, hpost⟩ := Hbody2
  subst hpost
  ihave ⟨%req, %i, %Hreq, Hreg, %Hlt, %Hreq0⟩ := clientReqsOk_elim γ hs last2 (reqCode kd) P.flatten
    (reqCode kd :: e) post P ⟨rfl, HP⟩ Hshape $$ [Hreqs2]
  · rw [List.append_assoc]; iexact Hreqs2
  have hlt : last < sint.Z req ∧ 0 ≤ sint.Z req := by
    rcases Hlast with rfl | ⟨hl0, x0, hx0, r0, j0, hr0, rfl⟩
    · have h0 : 0 ≤ sint.Z req := Hreq0 -- N-8
      omega
    · have := Hlt x0 hx0 r0 j0 hr0; omega
  iapply fupd_wp
  imod req_mint γ k hs c last (sint.Z req) i hlt.1 hlt.2 $$ [Hpr Hrepk Hreg] with ⟨Hpr, #Hrk, Htok⟩
  · iframe; iframe #
  imodintro
  ihave ⟨%ev, Hra, %Hev⟩ := req_of_dec kd hkd l _ hs req i Hreq
    (sintZ_nonneg_of_lt_peerMark Hhs) $$ Hdec
  -- `conn.RemoteAddr().String()`
  ihave #Hcat' := Hcat
  iunfold Perennial.net.connAt at Hcat'
  icases Hcat' with ⟨%nw, -, -, -, #Hra', -⟩
  iunfold Perennial.net.netAddr at Hra'
  icases Hra' with ⟨%rp, %rv, %Hrp, -⟩
  wp_auto
  wp_apply (netN.NetSpecs.remoteAddr (GF := GF) t c true a la ra) $$ [Hcat]
  · iexact Hcat
  subst Hrp
  wp_auto
  wp_apply (lib.wp_TCPAddr_String rp) as %ras -
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  try wp_auto
  wp_apply (wp_bag_send (ρ.chans kd) ch «$v_ptr» (reqChanP γ ρ k kd)) $$ [«$v» Hra Htok]
  · iframe Hbag
    unfold reqChanP
    iexists l, w, ev, hs, req, i
    rw [← reqTy_eq kd, evTok_of_clientReq γ.proto k ev hs req i Hev.1]
    iframe
    iframe #
    ipureintro; exact Hev
  -- `Stats.Max(Sprintf("client_rpc_%d_chan_length", code), len(ch))`
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf
    go!"client_rpc_%d_chan_length"
    [.lit go!"client_rpc_", .dir none _root_.Perennial.fmt.verb_d, .lit go!"_chan_length"]
    _ _ _ _ (by fmt_encode) ?fits ?pa $$ [$Hfmt $Hasl] as %key ⟨-, %Hkey⟩
  case pa => exact .int _ _ _ _ (.uint8 _) .nil
  case fits => fmt_fits
  ihave #Hch := is_bag_is_chan _ _ _ $$ Hbag
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_Len $$ [$Hch] as %len -
  ihave #Hstats : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats $$ []
  · iPkgInit
  have hkey : key ∉ netN.strIntKeys := by
    rw [Hkey]
    simp [_root_.Perennial.fmt.render, netN.strIntKeys]
  wp_apply (netN.wp_Max st key len hkey) $$ [$Hsto] as %n -
  wp_for_post
  iframe
  iexists _, _, _
  iframe
  ileft
  isplitr
  · ipureintro; rfl
  iexists P ++ [reqCode kd :: e], sint.Z req
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]
  try rw [hcode]
  iframe Hown Hpr
  isplitr
  · ipureintro
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact HP x hx
    · simp only [List.mem_singleton] at hx; subst hx; rw [← hcode]; exact ⟨_, Hshape⟩
  isplitr
  · iright; iexact Hrk
  ipureintro
  exact Or.inr ⟨hlt.2, reqCode kd :: e, by simp [hcode], req, i, Hreq, rfl⟩

end

end Perennial.gryff.replica2
