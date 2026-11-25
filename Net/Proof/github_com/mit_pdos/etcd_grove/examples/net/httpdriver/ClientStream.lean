/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the client's connection, as the stream `ReadResponse` reads

The client's end of a connection `cn` it dialed to the server (`drvAddr`), registered in the
connection registry (`http_register`: its slots are the mono-list `γ`, `httpConn cn γ`), read through a
`*bufio.Reader` as a stream reader (`hcStream`, over `Conn.Read.specLc`) of the state `hcSt cn γ γe`:
what was read meets the server's protocol (`httpRespP drvP`, its fact without a later, kept as in
`DialHTTPPath`'s `crSt`), half of the slots' mono-list (at most `4` slots: what bounds the stream, with
`respFacts`' head bound), and after a read error nothing more is read (`γe`, `hcErr`, `readDead`).

The laws `ReadResponse.spec_resp` takes of the stream (`hcSt_bound`, `hcErr_final`, `hcSt_law`: what is
read past the answers already delivered, `D`, is the wire of the next answer, which answers the slot at
its index, `drvQ`); the lower bound of the server's bytes a reader has delivered (`ownReader_hcLb`);
adding a slot to the mono-list while the reader holds half of it (`ownReader_addSlot`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.WireLemmas
public import Net.Spec.net.Conn__Read
public import Net.Proof.net.ConnIo
public import GooseLang.Ext.Net.Stream
public import Proof.io.ReaderStreamNE
public import Proof.bufio.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-! ## The answers the client reads (pure) -/

/-- An answer the server writes on the client's connection, as the protocol's facts make it: a
handler's answer delimited by its `Content-Length`, with a head of at most `2 ^ 22` bytes and a body
of at most `32` (`drvP.resp`), or the `400` answer; never a chunked one (its body is over `2048`
bytes). -/
def hcSlotOk : RespSlot → Prop
  | .ans ρ => net.http.respOk ρ ∧ ρ.close = false ∧
      (net.http.respHeadWire ρ.st ρ.reason ρ.hc).length ≤ 2 ^ 22 ∧ ρ.body.length ≤ 32
  | .chunked .. => False
  | .bad => True

/-- net/http's `400` answer is one `ReadResponse` reads as written. -/
theorem badResp_ok : net.http.respOk net.http.badResp := by
  have h1 : net.http.badResp.close = true := rfl
  unfold net.http.respOk
  rw [if_pos h1]
  refine ⟨by decide, by decide, by decide, net.http.badHdr_ok, by decide, by decide, by decide,
    by decide, by decide⟩

theorem badResp_len : (net.http.respWire net.http.badResp).length ≤ 256 := by
  have h : (fmt.decimalNat (uint.nat net.http.badResp.st)).length ≤ 3 :=
    fmt.length_decimalNat_le _ 3 (by decide) (by decide)
  unfold net.http.respWire net.http.respHeadWire
  generalize fmt.decimalNat (uint.nat net.http.badResp.st) = d at h ⊢
  simp [net.http.badResp, net.http.hdrWire, net.http.badHdr, net.http.hdrLineWire,
    List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons]
  omega

theorem hcSlot_len (x : RespSlot) (h : hcSlotOk x) :
    (net.http.respSlotWire x).length ≤ 8388608 := by
  cases x with
  | ans ρ =>
    simp only [hcSlotOk] at h
    obtain ⟨-, -, hh, hb⟩ := h
    simp only [net.http.respSlotWire, net.http.respWire, List.length_append]
    omega
  | chunked => simp [hcSlotOk] at h
  | bad =>
    have := badResp_len
    simp only [net.http.respSlotWire]
    omega

theorem respsWire_len (Rs : List RespSlot) (h : ∀ x ∈ Rs, hcSlotOk x) :
    (net.http.respsWire Rs).length ≤ Rs.length * 8388608 := by
  induction Rs with
  | nil => simp [net.http.respsWire]
  | cons x Rs ih =>
    have h1 := hcSlot_len x (h x (by simp))
    have h2 := ih (fun y hy => h y (by simp [hy]))
    simp only [net.http.respsWire, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at h2 ⊢
    omega

/-- Without a chunked answer, what is covered is a prefix of the answers' wire. -/
theorem hc_cover_wire (Rs : List RespSlot) (ext : List w8) (hc : net.http.respsCover Rs ext)
    (hg : ∀ x ∈ Rs, hcSlotOk x) : ext <+: net.http.respsWire Rs := by
  rcases hc.2 with h | ⟨st, reason, hc', hl, -⟩
  · exact h
  · exfalso
    have := hg _ (List.mem_of_getLast? hl)
    simp [hcSlotOk] at this

/-- Answers that are all the `400` answer: at most one (it is last). -/
theorem allBad_len (Rs : List RespSlot) (ext : List w8) (h : ∀ x ∈ Rs, x = RespSlot.bad)
    (hc : net.http.respsCover Rs ext) : Rs.length ≤ 1 := by
  match Rs, h, hc with
  | [], _, _ => simp
  | x :: xs, h, hc =>
    have hx := h x (by simp)
    have := hc.1 0 x (by simp) (by subst hx; rfl)
    simp only [List.length_cons] at this ⊢
    omega

theorem hc_bound_pure (r ext : List w8) (Rs : List RespSlot) (hr : r <+: ext)
    (hc : net.http.respsCover Rs ext) (hg : ∀ x ∈ Rs, hcSlotOk x) (hl : Rs.length ≤ 4) :
    r.length + 2 ^ 12 < 2 ^ 62 := by
  have h1 := respsWire_len Rs hg
  have h2 := (hr.trans (hc_cover_wire Rs ext hc hg)).length_le
  omega

/-- Past the answers `A` (`D`), what is read (`r`, not a prefix of `D`) is the next answer's: a
handler's (`r` and its wire comparable) or the `400` answer (`r` a prefix of its wire). -/
theorem hc_law_pure (D r ext : List w8) (A : List Resp) (Rs : List RespSlot)
    (hD : D = net.http.respsWire (A.map RespSlot.ans))
    (hA : ∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false)
    (hr : r <+: ext) (hc : net.http.respsCover Rs ext) (hg : ∀ x ∈ Rs, hcSlotOk x)
    (hDr : D <+: r ∨ r <+: D) (hn : ¬ r <+: D) :
    (∃ ρ, Rs[A.length]? = some (RespSlot.ans ρ) ∧ net.http.respOk ρ ∧ ρ.close = false ∧
        (r <+: D ++ net.http.respWire ρ ∨ D ++ net.http.respWire ρ <+: r)) ∨
      (Rs[A.length]? = some RespSlot.bad ∧ r <+: D ++ net.http.respWire net.http.badResp) := by
  have he := hr.trans (hc_cover_wire Rs ext hc hg)
  obtain ⟨y, rfl⟩ := hDr.resolve_right hn
  have hy : y ≠ [] := by
    rintro rfl
    exact hn (by simp)
  have hRs : ∀ x ∈ Rs, (∃ ρ, x = RespSlot.ans ρ ∧ net.http.respOk ρ ∧ ρ.close = false) ∨
      x = RespSlot.bad := by
    intro x hx
    have := hg x hx
    cases x with
    | ans ρ =>
      simp only [hcSlotOk] at this
      exact Or.inl ⟨ρ, rfl, this.1, this.2.1⟩
    | chunked => simp [hcSlotOk] at this
    | bad => exact Or.inr rfl
  have hp : net.http.respsWire (A.map RespSlot.ans) ++ y <+: net.http.respsWire Rs := by
    rw [← hD]; exact he
  obtain ⟨x, rest, hRs'⟩ := respsWire_prefix_decode A Rs y hA hRs hp hy
  have hidx : Rs[A.length]? = some x := by
    rw [hRs', List.getElem?_append_right (by simp)]
    simp
  have hw : net.http.respsWire Rs =
      D ++ net.http.respSlotWire x ++ net.http.respsWire rest := by
    rw [hRs', hD]
    simp [net.http.respsWire, List.flatten_append, List.append_assoc]
  have hr' : D ++ y <+: D ++ net.http.respSlotWire x ++ net.http.respsWire rest := by
    rw [← hw]; exact he
  have hx := hg x (List.mem_of_getElem? hidx)
  cases x with
  | ans ρ =>
    simp only [hcSlotOk] at hx
    refine Or.inl ⟨ρ, hidx, hx.1, hx.2.1, ?_⟩
    exact List.prefix_or_prefix_of_prefix hr' (List.prefix_append _ _)
  | chunked => simp [hcSlotOk] at hx
  | bad =>
    refine Or.inr ⟨hidx, ?_⟩
    have hlast := hc.1 A.length RespSlot.bad hidx rfl
    rw [hRs'] at hlast
    simp only [List.length_append, List.length_map, List.length_cons] at hlast
    have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    simpa [net.http.respsWire, net.http.respSlotWire] using hr'

/-- Two lower bounds of a list agree below the length of the first. -/
theorem lb_index (L L' : List ReqSlot) (i : Nat) (s : ReqSlot) (hi : i < L.length)
    (h : L <+: L' ∨ L' <+: L) (h' : L'[i]? = some s) : L[i]? = some s := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.getElem?_append_left hi] at h'; exact h'
  · have hi' : i < L'.length := by
      rcases Nat.lt_or_ge i L'.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at h'; cases h'
    rw [List.getElem?_append_left hi']; exact h'

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions] [net.Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The client's read state of `cn` at `r` (see the file header). -/
def hcSt (cn : Nat) (γ γe : GName) (r : List w8) : IProp GF :=
  iprop(recvTok (Gg := hG.goose_globalGS) cn false (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) r ∗
    rdlTok (Gg := hG.goose_globalGS) cn false false ∗
    net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗
    (∃ L : List ReqSlot, monoListAuthOwn γ (1 : Qp).half L ∗ ⌜L.length ≤ 4⌝) ∗
    ((monoListAuthOwn γe 1 [r] ∗ readDead (Gg := hG.goose_globalGS) cn false) ∨
      monoListAuthOwn γe 1 ([] : List (List w8))))

/-- The evidence of a read error at `r` (persistent). -/
def hcErr (γe : GName) (r : List w8) (_err : GoInterface) : IProp GF :=
  monoListLbOwn γe [r]

instance hcErr_persistent (γe : GName) (r : List w8) (err : GoInterface) :
    Persistent (hcErr (GF := GF) γe r err) := by
  unfold hcErr; infer_instance

/-- The server has written at least `D` on `cn` (persistent). -/
def hcLb (cn : Nat) (D : List w8) : IProp GF := sentLb (Gg := hG.goose_globalGS) cn true D

instance hcLb_persistent (cn : Nat) (D : List w8) : Persistent (hcLb (GF := GF) cn D) := by
  unfold hcLb; infer_instance

theorem hc_ml_halves {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ 1 l ⊣⊢
      monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  have := (monoListAuthOwn_fractional (GF := GF) γ l).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

instance httpRegInv_timeless : Timeless (net.http.httpRegInv (Gg := hG.goose_globalGS)) := by
  unfold net.http.httpRegInv
  have : ∀ M : GMap Nat GName,
      Timeless ([∗map] cn ↦ _γ ∈ M, connFresh (Gg := hG.goose_globalGS) cn false) :=
    fun _ => BigSepM.bigSepM_timeless (fun _ => inferInstance)
  infer_instance

/-- The client's reader keeps its token and learns that what it read was written. -/
theorem hc_recvTok_sentLb (cn : Nat) (P : Proto GF) (R : List w8) :
    recvTok (Gg := hG.goose_globalGS) cn false P R ⊢
      recvTok (Gg := hG.goose_globalGS) cn false P R ∗ sentLb (Gg := hG.goose_globalGS) cn true R :=
  persistent_entails_left (recvTok_sentLb (Gg := hG.goose_globalGS) cn false P R)

/-- A reader with its protocol fact back. -/
theorem hc_recvTokL_back (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTokL (Gg := hG.goose_globalGS) cn s P R ∗ protoPrefix P cn R ⊢
      recvTok (Gg := hG.goose_globalGS) cn s P R := by
  unfold recvTokL recvTok
  iintro ⟨⟨H, -⟩, #Hp⟩
  iframe H Hp

/-- A read's error other than for bytes is a pointer: not `nil`. -/
theorem hc_readErr_some (r : ReadRes) (la ra ed err : GoInterface) (xe : Loc)
    (hr : ∀ bs, r ≠ .bytes bs) :
    net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ⊢
      ⌜err ≠ interface.nil ∧ _root_.Perennial.io.ptrTyped err⌝ := by
  cases r with
  | bytes bs => exact absurd rfl (hr bs)
  | eof =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro
    refine ⟨by simp [interface.mkOk], ?_⟩
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨xe, rfl⟩
  | err k =>
    simp only [net.ReadErr]
    iintro HE
    ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    ipureintro
    refine ⟨by simp [interface.mkOk], ?_⟩
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨pe, rfl⟩

/-- An answer's facts make it one the client's stream can carry (`hcSlotOk`): `drvP.resp` bounds a
body by `32` bytes, against a chunked answer's over `2048`. -/
theorem respFact_good (L : List ReqSlot) (i : Nat) (x : RespSlot) :
    net.http.respFacts (drvP (GF := GF) (hG := hG)) L i x ⊢ ⌜hcSlotOk x⌝ := by
  cases x with
  | ans ρ =>
    unfold net.http.respFacts
    simp only [drvP]
    iintro ⟨%R, %τ, %B, %hs, ⟨%-, %hok, %hcl, %-, %hh⟩, %hb, -⟩
    ipureintro
    simp only [hcSlotOk]
    exact ⟨hok, hcl, hh, hb⟩
  | chunked st reason hc =>
    unfold net.http.respFacts
    simp only [drvP]
    iintro ⟨%R, %τ, %B, %hs, %w, ⟨%-, %-, %hw, %-⟩, %hb⟩
    ipureintro
    omega
  | bad =>
    iintro -
    ipureintro
    simp only [hcSlotOk]

theorem respFacts_good (L : List ReqSlot) (Rs : List RespSlot) :
    ([∗list] i ↦ x ∈ Rs, net.http.respFacts (drvP (GF := GF) (hG := hG)) L i x) ⊢
      ⌜∀ x ∈ Rs, hcSlotOk x⌝ := by
  refine (BigSepL.bigSepL_mono (Ψ := fun _ x => iprop(⌜hcSlotOk x⌝))
    fun {i x} _ => respFact_good L i x).trans ?_
  refine BigSepL.bigSepL_pure_intro.trans (pure_mono fun h x hx => ?_)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  exact h i x hi

/-- What the server wrote on `cn` (`httpRespP drvP`): answers the client's stream can carry, all
the `400` answer or answering the slots `L'` of `cn`, a lower bound of its mono-list `γ`. -/
theorem hc_respP_good (cn : Nat) (γ : GName) (ext : List w8) :
    net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗
      net.http.httpRespP (Gg := hG.goose_globalGS) drvP cn ext ⊢
    ∃ Rs : List RespSlot, ⌜net.http.respsCover Rs ext ∧ ∀ x ∈ Rs, hcSlotOk x⌝ ∗
      (⌜∀ x ∈ Rs, x = RespSlot.bad⌝ ∨
        ∃ L' : List ReqSlot, monoListLbOwn γ L' ∗ ⌜Rs.length ≤ L'.length⌝ ∗
          [∗list] i ↦ x ∈ Rs, net.http.respFacts (drvP (GF := GF) (hG := hG)) L' i x) := by
  iintro ⟨#Hcn, HP⟩
  iunfold net.http.httpRespP at HP
  icases HP with ⟨%Rs, %Hcov, (%Hbad | ⟨%γ', %L', #Hcn', #Hlb, %Hlen, #Hfs⟩)⟩
  · iexists Rs
    isplitr
    · ipureintro
      refine ⟨Hcov, fun x hx => ?_⟩
      rw [Hbad x hx]
      simp only [hcSlotOk]
    · ileft; ipureintro; exact Hbad
  · iunfold net.http.httpConn at Hcn Hcn'
    ihave %Hg := ghostMapElem_agree _ _ _ _ _ _ $$ Hcn Hcn'
    subst γ'
    ihave %Hgood := respFacts_good L' Rs $$ Hfs
    iexists Rs
    isplitr
    · ipureintro; exact ⟨Hcov, Hgood⟩
    iright
    iexists L'
    iframe Hlb Hfs
    ipureintro; exact Hlen

/-- Registering a dialed connection: its fresh token given up to the registry, its slots a new
mono-list. -/
theorem http_register (cn : Nat) :
    inv net.http.httpRegN (net.http.httpRegInv (Gg := hG.goose_globalGS)) ∗
      connFresh (Gg := hG.goose_globalGS) cn false ⊢
    |={⊤}=> ∃ γ : GName, net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗
      monoListAuthOwn γ 1 ([] : List ReqSlot) := by
  iintro ⟨#Hreg, Hfresh⟩
  imod mono_list_own_alloc (GF := GF) ([] : List ReqSlot) with ⟨%γ, Hγ, -⟩
  iinv Hreg with >Hi Hclose
  iunfold net.http.httpRegInv at Hi
  icases Hi with ⟨%M, HM, HMs⟩
  cases hM : M.lookup cn with
  | some n =>
    ihave Hf := BigSepM.bigSepM_lookup (Φ := fun cn (_n : GName) =>
      connFresh (Gg := hG.goose_globalGS) cn false) (m := M) (i := cn) (x := n)
      (by rw [gmap_get?_eq, hM]) $$ HMs
    iexfalso
    iapply connFresh_excl $$ [$Hf $Hfresh]
  | none =>
    imod ghost_map_insert_persist cn γ hM $$ HM with ⟨HM, #He⟩
    imod Hclose $$ [HM HMs Hfresh] with -
    · inext
      iunfold net.http.httpRegInv
      iexists M.insert cn γ
      iframe HM
      iapply (BigSepM.bigSepM_insert (Φ := fun cn (_n : GName) =>
        connFresh (Gg := hG.goose_globalGS) cn false) (by rw [gmap_get?_eq, hM])).2
      iframe Hfresh HMs
    imodintro
    iexists γ
    iframe Hγ
    iunfold net.http.httpConn
    iexact He

/-- The state at the start: nothing read, no slot. -/
theorem hcSt_init (cn : Nat) (γ : GName) :
    recvTok (Gg := hG.goose_globalGS) cn false (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) [] ∗
      rdlTok (Gg := hG.goose_globalGS) cn false false ∗
      net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗ monoListAuthOwn γ (1 : Qp).half ([] : List ReqSlot) ⊢
    |==> ∃ γe : GName, hcSt cn γ γe [] := by
  iintro ⟨Hrecv, Hrdl, #Hcn, Hh⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (List w8)) with ⟨%γe, Hγe, -⟩
  imodintro
  iexists γe
  iunfold hcSt
  iframe Hrecv Hrdl Hcn
  isplitl [Hh]
  · iexists []
    iframe Hh
    ipureintro; simp
  · iright; iexact Hγe

/-- The client's end of `cn` is a stream reader over `hcSt` (see the file header). -/
theorem hcStream (wp_Read : net.Conn.Read.specLc (GF := GF) (hG := hG))
    (cn : Nat) (γ γe : GName) (t : Loc) (la ra : GoInterface) (ed : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      net.connAt (GF := GF) t cn false addrS la ra ⊢
    EtcdGrove.io.readerStreamNE (net.connIface t) (hcSt cn γ γe) (hcErr γe) := by
  unfold net.connIface
  iintro ⟨#Hio, #Hed, #Hconn⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, -, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  iunfold EtcdGrove.io.readerStreamNE
  imodintro
  iintro %r %p %xs
  imodintro
  iintro %Φ ⟨-, Hst, Hp⟩ HΦ
  iunfold hcSt at Hst
  icases Hst with ⟨Hrecv, Hrdl, #Hcn, HL, Hc⟩
  ihave %Hlen := ownSlice_len $$ Hp
  have hxl : xs.length = p.len.toNat := by
    rw [Hlen.1]; have := Hlen.2; unfold sint.nat; word
  icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv with ⟨Hrecv, #Hpp0⟩
  ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv
  iapply wp_fupd
  icases Hc with (⟨Hc, #Hdead⟩ | Hc)
  · -- failed before: no byte
    wp_apply wp_Read t cn false addrS la ra p xs
        (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn false
            (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) r ∗
          ⌜res.got = [] ∧ (p.len.toNat ≠ 0 → ∀ bs, res ≠ .bytes bs)⌝)) $$ [Hp HrL]
      as %k %err ⟨%res, %bs', ⟨HrL, %Hres⟩, Hp, %Hout, HE, -⟩
    · iframe Hconn Hp Hxe Hed
      imod read_after_dead_au (Gg := hG.goose_globalGS) cn false _ _ p.len.toNat $$ [$HrL $Hdead]
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      iapply Hcl $$ %r' %d' %Hrd HE HD
    ihave HrT := hc_recvTokL_back cn false _ _ $$ [$HrL $Hpp0]
    imod monoListAuthOwn_update (GF := GF) [r] (List.prefix_refl _) $$ Hc with ⟨Hc, #Hlb⟩
    rcases res with bs | _ | k0
    · -- `(0, nil)` on an empty buffer
      obtain ⟨hk, rfl⟩ := Hout
      obtain ⟨hg, hne⟩ := Hres
      simp only [ReadRes.got] at hg
      subst hg
      have hx0 : p.len.toNat = 0 := by
        rcases Nat.eq_zero_or_pos p.len.toNat with h | h
        · exact h
        · exact absurd rfl (hne (by omega) [])
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hxs
      imodintro
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append, List.take_nil]
      iframe Hp
      isplitr
      · ipureintro
        refine ⟨?_, by simp, fun h => absurd rfl h⟩
        simpa using hk
      isplitl [HE]
      · try simp only [net.ReadErr]
        icases HE with %h; subst h
        iapply EtcdGrove.io.errAt_nil
      iunfold hcSt
      iframe HrT Hrdl Hcn HL
      ileft; iframe Hc Hdead
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      ihave %Hne := hc_readErr_some _ la ra ed err xe (by intro bs h; cases h) $$ HE
      obtain ⟨Hne, Hptr⟩ := Hne
      imodintro
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro
        exact ⟨by rw [hk]; rfl, by simp, fun _ => Or.inr Hne⟩
      isplitr
      · unfold EtcdGrove.io.errAt
        isplitl []
        · iright; imodintro; iunfold hcErr; iexact Hlb
        · ipureintro; exact Hptr
      iunfold hcSt
      iframe HrT Hrdl Hcn HL
      ileft; iframe Hc Hdead)
  · -- not failed: read into `p`
    wp_apply wp_Read t cn false addrS la ra p xs
        (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn false
            (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) (r ++ res.got) ∗
          rdlTok (Gg := hG.goose_globalGS) cn false false ∗
          ⌜∃ st d d', st.rdl = false ∧ ReadOutcome st d p.len.toNat res d'⌝ ∗
          (⌜res = .eof ∨ res = .err .sys ∨ res = .err .closed⌝ -∗
            readDead (Gg := hG.goose_globalGS) cn false))) $$ [Hp HrL Hrdl]
      as %k %err ⟨%res, %bs', ⟨HrL, Hrdl, %Hro, Hdead⟩, Hp, %Hout, HE, Hlc1, -⟩
    · iframe Hconn Hp Hxe Hed
      imod read_dead_au (Gg := hG.goose_globalGS) cn false _ _ p.len.toNat false $$ [$HrL $Hrdl]
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      iapply Hcl $$ %r' %d' %Hrd HE HD
    obtain ⟨st, d, d', hrdl, Hro⟩ := Hro
    have Hgl := readOutcome_got_le Hro
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HrL
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    rcases res with bs | _ | (_ | _ | _)
    · -- bytes: no error
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got] at Hgl ⊢
      have hbl : bs.length ≤ xs.length := by rw [hxl]; exact Hgl.1
      imodintro
      iapply HΦ
      iexists bs
      rw [List.take_of_length_le hbl]
      iframe Hp
      isplitr
      · ipureintro
        refine ⟨?_, hbl, fun hx => Or.inl ?_⟩
        · rw [Nat.min_eq_right hbl] at hk; exact hk
        · rintro rfl
          have := Hgl.2 rfl
          exact hx (List.eq_nil_of_length_eq_zero (by omega))
      isplitr
      · iapply EtcdGrove.io.errAt_nil
      iunfold hcSt
      iframe HrT Hrdl Hcn HL
      iright; iexact Hc
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got, List.append_nil] at ⊢
      ihave %Hne := hc_readErr_some _ la ra ed err xe (by intro bs h; cases h) $$ HE
      obtain ⟨Hne, Hptr⟩ := Hne
      ihave #Hd : readDead (Gg := hG.goose_globalGS) cn false $$ [Hdead]
      · iapply Hdead
        ipureintro
        first
        | exact absurd Hro (fun h => readOutcome_no_timeout hrdl h)
        | simp
      imod monoListAuthOwn_update_app (GF := GF) [r] $$ Hc with ⟨Hc, #Hlb⟩
      simp only [List.nil_append]
      imodintro
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro
        exact ⟨by rw [hk]; rfl, by simp, fun _ => Or.inr Hne⟩
      isplitr
      · unfold EtcdGrove.io.errAt
        isplitl []
        · iright; imodintro; iunfold hcErr; iexact Hlb
        · ipureintro; exact Hptr
      iunfold hcSt
      iframe HrT Hrdl Hcn HL
      ileft; iframe Hc Hd)

/-- `bufio.NewReader`'s law. -/
theorem hcSt_bound (cn : Nat) (γ γe : GName) (r : List w8) :
    hcSt (GF := GF) cn γ γe r ⊢ ⌜r.length + 2 ^ 12 < 2 ^ 62⌝ := by
  iintro Hst
  iunfold hcSt at Hst
  icases Hst with ⟨Hrecv, -, #Hcn, ⟨%L, Hh, %HL⟩, -⟩
  icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv with ⟨-, #Hpp⟩
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · subst Hnil; ipureintro; simp
  ihave ⟨%Rs, ⟨%Hcov, %Hgood⟩, Hor⟩ := hc_respP_good cn γ ext $$ [$Hcn $HP]
  ihave %HRs : (⌜Rs.length ≤ 4⌝ : IProp GF) $$ [Hh Hor]
  · icases Hor with (%Hbad | ⟨%L', #Hlb, %Hlen, -⟩)
    · ipureintro
      have := allBad_len Rs ext Hbad Hcov
      omega
    · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hh Hlb
      ipureintro
      have := Hv.2.length_le
      omega
  ipureintro
  exact hc_bound_pure r ext Rs Hext Hcov Hgood HRs

/-- After an error at `r`, the stream stays at `r`. -/
theorem hcErr_final (cn : Nat) (γ γe : GName) (r r' : List w8) (err : GoInterface) :
    hcErr (GF := GF) γe r err ∗ hcSt cn γ γe r' ⊢ ⌜r <+: r' → r' = r⌝ := by
  iintro ⟨#He, Hst⟩
  iunfold hcSt at Hst
  icases Hst with ⟨-, -, -, -, Hc⟩
  iunfold hcErr at He
  icases Hc with (⟨Hc, -⟩ | Hc)
  · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hc He
    obtain ⟨-, Hp⟩ := Hv
    ipureintro
    intro _
    obtain ⟨t, ht⟩ := Hp
    cases t with
    | nil => simpa using ht.symm
    | cons _ _ => simp at ht
  · ihave %Hv := mono_list_auth_lb_valid _ _ _ _ $$ Hc He
    obtain ⟨-, Hp⟩ := Hv
    exact absurd (List.prefix_nil.1 Hp) (by simp)

/-- **What `ReadResponse` reads next**: past the answers `A` delivered (`D`, the server's bytes so far),
a prefix of the wire of the answer at index `A.length`, or, for one delimited by its `Content-Length`,
that wire and more; and what the client knows of it (`drvQ`), the slots being at least `L`. -/
theorem hcSt_law (cn : Nat) (γ γe : GName) (D : List w8) (A : List Resp) (L : List ReqSlot)
    (hD : D = net.http.respsWire (A.map RespSlot.ans))
    (hA : ∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false) (hL : A.length < L.length) :
    hcLb cn D ∗ monoListLbOwn γ L ⊢
    □ ∀ r, hcSt cn γ γe r -∗ ⌜r <+: D⌝ ∨ ∃ ρ : Resp, ⌜net.http.respOk ρ ∧
        (r <+: D ++ net.http.respWire ρ ∨ (ρ.close = false ∧ D ++ net.http.respWire ρ <+: r))⌝ ∗
      □ drvQ L A.length ρ := by
  iintro ⟨#HD, #HL⟩
  imodintro
  iintro %r Hst
  iunfold hcSt at Hst
  icases Hst with ⟨Hrecv, -, #Hcn, -, -⟩
  icases hc_recvTok_sentLb cn _ r $$ Hrecv with ⟨Hrecv, #Hsr⟩
  iunfold hcLb at HD
  ihave %Hcmp := sentLb_agree (Gg := hG.goose_globalGS) cn true D r $$ [$HD $Hsr]
  by_cases hn : r <+: D
  · ileft; ipureintro; exact hn
  icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv with ⟨-, #Hpp⟩
  iunfold protoPrefix at Hpp
  icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
  · exfalso; subst Hnil; exact hn List.nil_prefix
  ihave ⟨%Rs, ⟨%Hcov, %Hgood⟩, Hor⟩ := hc_respP_good cn γ ext $$ [$Hcn $HP]
  rcases hc_law_pure D r ext A Rs hD hA Hext Hcov Hgood Hcmp hn with
    ⟨ρ, hidx, hok, hcl, hpre⟩ | ⟨hidx, hpre⟩
  · -- a handler's answer: its facts
    icases Hor with (%Hbad | ⟨%L', #Hlb, %Hlen, #Hfs⟩)
    · exfalso
      have := Hbad _ (List.mem_of_getElem? hidx)
      cases this
    ihave #Hf := BigSepL.bigSepL_lookup (Φ := fun i (x : RespSlot) =>
      net.http.respFacts (drvP (GF := GF) (hG := hG)) L' i x) hidx $$ Hfs
    iunfold net.http.respFacts at Hf
    icases Hf with ⟨%R, %τ, %B, %hs, ⟨%HL', %-, %-, %Hv, %-⟩, -, #Hend⟩
    ihave %Hv2 := mono_list_lb_valid _ _ _ $$ HL Hlb
    iright
    iexists ρ
    isplitr
    · ipureintro
      exact ⟨hok, hpre.imp id (fun h => ⟨hcl, h⟩)⟩
    imodintro
    iunfold drvQ
    iright
    iexists R, τ, B, hs
    iframe Hend
    ipureintro
    exact ⟨lb_index L L' _ _ hL Hv2 HL', hok, hcl, Hv⟩
  · -- the `400` answer
    iright
    iexists net.http.badResp
    isplitr
    · ipureintro
      exact ⟨badResp_ok, Or.inl hpre⟩
    imodintro
    iunfold drvQ
    ileft
    ipureintro; rfl

/-- A reader over `hcSt` has delivered bytes the server wrote. -/
theorem ownReader_hcLb (b : Loc) (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF)
    (cn : Nat) (γ γe : GName) (D : List w8) :
    EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ⊢
      EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ∗ hcLb cn D := by
  iintro Hb
  ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri _ E D $$ Hb
  iunfold hcSt at HS
  icases HS with ⟨Hrecv, Hrdl, #Hcn, HL, Hc⟩
  icases hc_recvTok_sentLb cn _ (D ++ q) $$ Hrecv with ⟨Hrecv, #Hsl⟩
  ihave #HlbD := sentLb_le (Gg := hG.goose_globalGS) cn true D (List.prefix_append D q) $$ Hsl
  ihave Hb := Hcl $$ [Hrecv Hrdl HL Hc]
  · iunfold hcSt
    iframe Hrecv Hrdl Hcn HL Hc
  iframe Hb
  iunfold hcLb
  iexact HlbD

/-- A slot added to the mono-list, the reader holding its other half (at most `4` slots). -/
theorem ownReader_addSlot (b : Loc) (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF)
    (cn : Nat) (γ γe : GName) (D : List w8) (L : List ReqSlot) (s : ReqSlot) (hL : L.length < 4) :
    EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ∗ monoListAuthOwn γ (1 : Qp).half L ⊢
      |==> (EtcdGrove.bufio.ownReader b ri (hcSt cn γ γe) E D ∗
        monoListAuthOwn γ (1 : Qp).half (L ++ [s])) := by
  iintro ⟨Hb, Hh⟩
  ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri _ E D $$ Hb
  iunfold hcSt at HS
  icases HS with ⟨Hrecv, Hrdl, #Hcn, ⟨%L0, Hh0, %HL0⟩, Hc⟩
  ihave %Hag := monoListAuthOwn_agree _ _ _ _ _ $$ Hh0 Hh
  obtain ⟨-, hL0⟩ := Hag
  subst L0
  ihave Hfull := (hc_ml_halves γ L).2 $$ [$Hh0 $Hh]
  ihave Hup := monoListAuthOwn_update (GF := GF) (L ++ [s]) (List.prefix_append _ _) $$ Hfull
  imod Hup with ⟨Hfull, -⟩
  icases (hc_ml_halves γ (L ++ [s])).1 $$ Hfull with ⟨Hh1, Hh2⟩
  imodintro
  iframe Hh2
  iapply Hcl
  iunfold hcSt
  iframe Hrecv Hrdl Hcn Hc
  iexists L ++ [s]
  iframe Hh1
  ipureintro
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end defs

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
