/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Conn.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.waitForPeerConnections(done)`: the peers' handshake (P1), proved over its callees' specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnAddr
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Printf
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Results
public import Perennial.Proof.encoding.binary.Results

-- PORT: lab imports dropped: Harness.Proof.net.Listen, Harness.Proof.net.TCPListener__Accept

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [io.Assumptions]
  [errors.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [strings.Assumptions] [encoding.binary.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- A rejected peer id: log, close the connection, next. -/
local macro "reject" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface)
  isplitr
  · ipureintro; rfl
  iintro %s1 ⟨-, -⟩
  try wp_auto
  wp_apply replica.wp_Println wp_Println $$ [Hlg Hq]
  · iframe Hlg Hq
  try wp_auto
  wp_apply net.TCPConn.Close.wp_proof c cid true $$ [Hown] as %e3 -
  · iframe Hown
  wp_for_post
  iframe
  iexists _, pcsl, pcs, _
  iframe
  ipureintro; exact hbb'))

/-- The promoted `r.Fatal(...)` (the embedded quiet logger's: it returns). -/
theorem replica.wp_Fatal (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Fatal" #r)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Fatal $$ [$Hq]
  wp_end

theorem replica.wp_Println (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Println" #r)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Println $$ [$Hq]
  wp_end

theorem replica.wp_Printf (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (r lg : Loc) (f : GoString) (sl : GoSlice) :
    {{ replica.fld r go!"Logger" ↦□ lg ∗ dlog.quiet (GF := netDistGF) lg }}
      (App (App (Val #(methods (go.GoType.PointerType replica.Replica.ty) go!"Printf" #r)) (Val #f))
        (Val #sl))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hlg, #Hq⟩
  wp_auto
  wp_apply wp_Printf $$ [$Hq]
  wp_end

/-- The 5-byte buffer `bs`: its part `bs[1:]`, and back with any 4 bytes there. -/
theorem replica.bs5_acc (p : Loc) (bb : List w8) (hb : bb.length = 5) :
    (slice.mk p (W64 5) (W64 5) ↦* bb : IProp netDistGF) ⊢
      slice.slice (slice.mk p (W64 5) (W64 5)) w8 (W64 1) (W64 5) ↦*
        subslice (sint.nat (W64 1)) (sint.nat (W64 5)) bb ∗
      (∀ m : List w8, ⌜m.length = 4⌝ -∗
        slice.slice (slice.mk p (W64 5) (W64 5)) w8 (W64 1) (W64 5) ↦* m -∗
        slice.mk p (W64 5) (W64 5) ↦* (bb.take 1 ++ m)) := by
  have hsl5 : sint.Z (slice.mk p (W64 5) (W64 5)).len = 5 := rfl
  obtain ⟨x0, x1, x2, x3, x4, rfl⟩ : ∃ x0 x1 x2 x3 x4 : w8, bb = [x0, x1, x2, x3, x4] := by
    match bb, hb with
    | [x0, x1, x2, x3, x4], _ => exact ⟨x0, x1, x2, x3, x4, rfl⟩
  iintro Hsl
  icases (ownSlice_slice (W64 1) (W64 5) _ _ _ ⟨by decide, by decide, by rw [hsl5]; decide⟩).1
    $$ Hsl with ⟨Hs0, Hs1, Hs2⟩
  iframe Hs1
  iintro %m %Hm Hs1
  obtain ⟨y1, y2, y3, y4, rfl⟩ : ∃ y1 y2 y3 y4 : w8, m = [y1, y2, y3, y4] := by
    match m, Hm with
    | [y1, y2, y3, y4], _ => exact ⟨y1, y2, y3, y4, rfl⟩
  iapply (ownSlice_slice (W64 1) (W64 5) _ _ ([x0, x1, x2, x3, x4].take 1 ++ [y1, y2, y3, y4])
    ⟨by decide, by decide, by rw [hsl5]; decide⟩).2
  iframe

theorem replica.Replica.waitForPeerConnections.wp_proof
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.waitForPeerConnections.spec (hG := hG) := by
  intro r γ γc γm N me asl l a ip lg pssl prsl pwsl alsl lv0 pcsl0 done γd
  wp_start as ⟨#Hlg, #Hq, #HN, #HId, #HAL, #Hl, #HPs, #HPR, #HPW, #HAl, HLis, Hpc, %Hpure,
    Htok, %Hip, #Hap, Hslots, #Hdone⟩
  obtain ⟨hpc0, hla, hmem, hpre, hme0, hmeN, hN7, hlN, hpsl, hprl, hpwl, hall⟩ := Hpure
  ihave %Hll := ownSlice_len _ _ _ $$ Hl
  have hmez : sint.Z (W64 (sint.Z me)) = me.toInt := by
    have : sint.Z me = me.toInt := rfl
    rw [this]; simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have haslen : sint.Z asl.len = N := by
    have e1 : sint.nat asl.len = (sint.Z asl.len).toNat := rfl
    omega
  obtain ⟨port, hsplit, haddr⟩ := addr_split a ip (List.elem_iff.1 (by simpa using hmem)) hpre
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_load_slice_index _ _ _ _ a (by omega) $$ [Hl] as -
  · iframe Hl; ipureintro; rw [hmez]; exact hla
  have hcolon : (go!":" : GoString) = [W8 58] := by decide
  wp_apply strings.wp_Split a go!":" (by decide) as %ssl ⟨Hssl, -⟩
  rw [hcolon, hsplit]
  try wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hssl
  have hsl2 : sint.Z ssl.len = 2 := by
    have e1 : sint.nat ssl.len = (sint.Z ssl.len).toNat := rfl
    simp at Hsl; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hsl2]; decide⟩)]
  wp_apply wp_load_slice_index _ _ _ _ port (by decide) $$ [Hssl] as -
  · iframe Hssl; ipureintro; rfl
  try wp_auto
  have hwild : ([48#8, 46#8, 48#8, 46#8, 48#8, 46#8, 48#8, W8 58] ++ port : GoString) =
      go!"0.0.0.0" ++ [W8 58] ++ port := by rfl
  have hL := net.ListenWild.wp_proof (hG := hG) ip go!"0.0.0.0" port (by decide)
  rw [hcolon, haddr] at hL
  rw [hwild]
  wp_apply hL $$ [$Htok] as %lv %er ⟨Htok, Hres⟩
  · ipureintro; exact Hip
  try wp_auto
  ihave HL : (∃ (lv : GoInterface) (er : GoInterface),
      "l" ∷ l_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ er ∗ "Htok" ∷ addrTok a ∗
      "Hres" ∷ ((∃ (ll : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #ll ∧
            er = interface.nil⌝ ∗ net.ownListener ll lid a) ∨
        (∃ i, ⌜lv = interface.nil ∧ er = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code er)) : IProp netDistGF)
    $$ [l err Htok Hres]
  · iexists lv, er; iframe
  wp_for HL
  icases Hres with (⟨%ll, %lid, ⟨%Hlv, %Her⟩, #Hlis⟩ | ⟨%i, ⟨%Hlv, %Her⟩, Herr⟩)
  · subst Hlv Her
    wp_auto
    cleanup_bool_decide
    wp_pures
    wp_auto
    ihave Hsl := slice_array b_ptr 5 (Perennial.zero_val (GoArray w8 5)) (by decide) $$ b
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 5 - W64 0 = W64 5 from rfl]
    rw [show (Perennial.zero_val (GoArray w8 5)).arr = List.replicate 5 (W8 0) from rfl]
    ihave Hpcs0 : (slice.nil ↦* ([] : List replica.pendingClient) : IProp netDistGF) $$ []
    · iapply ownSlice_nil
    ihave Hcap0 := ownSliceCap_nil (GF := netDistGF) (V := replica.pendingClient)
    ihave Hsl2 : ([∗list] j ∈ List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1)),
        replica.peerSlot γ γc γm me pssl prsl pwsl alsl j) $$ [Hslots]
    · iapply BigSepL.bigSepL_mono _ $$ Hslots
      iintro %j %x %_ ⟨%cv, %rd, %w, %al, H1, H2, H3, H4, %Hn⟩
      unfold replica.peerSlot
      iexists cv, rd, w, al
      iframe
      ileft; ipureintro; exact Hn
    subst hpc0
    ihave HL2 : (∃ (iv : w32) (pcsl : GoSlice) (pcs : List replica.pendingClient) (bb : List w8),
        "i" ∷ i_ptr ↦ iv ∗ "Hpc" ∷ replica.fld r go!"pendingClients" ↦ pcsl ∗
        "Hpcs" ∷ pcsl ↦* pcs ∗ "Hcap" ∷ ownSliceCap replica.pendingClient pcsl (DFrac.own 1) ∗
        "Hpok" ∷ ([∗list] p ∈ pcs, replica.pendingOk γ γc γm p) ∗
        "Hslots" ∷ ([∗list] j ∈ List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1)),
          replica.peerSlot γ γc γm me pssl prsl pwsl alsl j) ∗
        "Hsl" ∷ slice.mk b_ptr (W64 5) (W64 5) ↦* bb ∗ "%Hbb" ∷ ⌜bb.length = 5⌝ : IProp netDistGF)
      $$ [i Hpc Hpcs0 Hcap0 Hsl2 Hsl]
    · iexists _, slice.nil, [], _
      iframe
      isplitl [Hcap0]
      · iexact Hcap0
      isplitl []
      · iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
      ipureintro; rfl
    wp_for HL2
    wp_if_destruct
    · wp_apply net.TCPListener.Accept.wp_proof ll lid a (sp.inP γ γc γm) (sp.outQ γ γc γm)
        $$ [$Hlis $Hap] as %cv %er Hres
      unfold net.newConnResult
      icases Hres with (⟨%c, %cid, ⟨%Hcv, %Her⟩, #Hown, ⟨Hsend, Hrecv⟩, -⟩ | ⟨%i, ⟨%Hcv, %Her⟩, Herr⟩)
      · subst Hcv Her
        wp_auto
        ihave #Hci : net.rpc.connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
          cid true $$ []
        · unfold net.rpc.connIface; iexists c; iframe Hown; ipureintro; rfl
        ihave #Hrdok := bufio.readerOk_conn _ cid true (sp.inP γ γc γm) $$ [$Hpkg3 $Hci]
        wp_apply bufio.wp_NewReader _ _ [] $$ [$Hrdok $Hrecv] as %br Hrd
        try wp_auto
        wp_apply bufio.wp_ReadByte br _ _ [] $$ [$Hpkg2 $Hrdok $Hrd] as %c0 %er Hres
        icases Hres with (⟨%Hen, Hrd⟩ | ⟨%Hen, #Hea, Hrd⟩)
        · subst Hen
          icases sp.ownReader_proto br _ cid true _ ([] ++ [c0]) $$ Hrd with
            ⟨Hrd, (%Hn | ⟨%ext, %He, #HP⟩)⟩
          · simp at Hn
          try wp_auto
          wp_if_destruct
          · -- the peers' hello byte: a peer's connection
            ihave #Hkind : sp.connKind γ cid .peer $$ []
            · iapply sp.peer_of_hello cid ext (by simpa using He) $$ HP
            ihave #Hrs := bufio.bufioReadsOk br _ _ $$ [$Hpkg2 $Hrdok]
            wp_apply wp_store_slice_index _ (sint.Z (W64 0)) bb (W8 255) $$ [Hsl] as Hsl
            · iframe Hsl; ipureintro; rw [Hbb]; decide
            have hbb0 : (bb.set 0 (W8 255)).length = 5 := by simp [Hbb]
            icases replica.bs5_acc b_ptr _ hbb0 $$ Hsl with ⟨Hs1, Hback⟩
            try wp_auto
            wp_apply bufio.wp_ReadFull _ _ ([] ++ [W8 255]) _ _ $$ [$Hpkg4 $Hrs $Hrd $Hs1]
              as %n %er2 ⟨%data, %Hd, Hs1, Hrd, #He2⟩
            obtain ⟨hn, hdl, herr⟩ := Hd
            have hsub4' : (subslice 1 5 (bb.set 0 (W8 255))).length = 4 := by
              simp [subslice, Hbb]
            have hsub4 : (subslice (sint.nat (W64 1)) (sint.nat (W64 5))
                (bb.set 0 (W8 255))).length = 4 := hsub4'
            ihave Hsl := Hback $$ %_ [] Hs1
            · ipureintro; simp [subslice, Hbb] at hdl ⊢; simp only [show sint.nat (5#64 : w64) = 5 from rfl, show sint.nat (1#64 : w64) = 1 from rfl] at hdl ⊢; omega
            have hbb' : ((bb.set 0 (W8 255)).take 1 ++
                (data ++ (subslice (sint.nat (W64 1)) (sint.nat (W64 5))
                  (bb.set 0 (W8 255))).drop data.length)).length = 5 := by
              simp [subslice, Hbb] at hdl ⊢; simp only [show sint.nat (5#64 : w64) = 5 from rfl, show sint.nat (1#64 : w64) = 1 from rfl] at hdl ⊢; omega
            rcases er2 with eo2 | _
            · wp_auto
              wp_apply wp_slice_literal (V := GoInterface)
              isplitr
              · ipureintro; rfl
              iintro %s1 ⟨-, -⟩
              try wp_auto
              wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hq]
              wp_for_post
              iframe
              iexists _, pcsl, pcs, _
              iframe
              ipureintro; exact hbb'
            · have h4 : data.length = 4 := by
                have := herr.1 rfl
                simp [subslice, Hbb] at this
                simp only [show sint.nat (5#64 : w64) = 5 from rfl,
                  show sint.nat (1#64 : w64) = 1 from rfl] at this
                omega
              icases sp.ownReader_proto br _ cid true _ ([] ++ [W8 255] ++ data) $$ Hrd with
                ⟨Hrd, (%Hnil | ⟨%ext2, %Hext2, #HP2⟩)⟩
              · simp at Hnil
              ihave %Hhello := sp.hello_read cid ext2 ([] ++ [W8 255] ++ data) Hext2
                (by simp [h4]) $$ [$Hkind $HP2]
              obtain ⟨id', hid'⟩ := Hhello
              have hdata : data = sp.le32 id' := by
                simp [sp.helloBytes] at hid'; exact hid'
              subst hdata
              have hrd : [] ++ [W8 255] ++ sp.le32 id' = sp.helloBytes id' := rfl
              rw [hrd]
              have hdrop : (subslice (sint.nat (W64 1)) (sint.nat (W64 5))
                  (bb.set 0 (W8 255))).drop (sp.le32 id').length = [] :=
                List.drop_eq_nil_of_le (by omega)
              rw [hdrop, List.append_nil] at hbb'
              have hdrop' : (subslice 1 5 (bb.set 0 (W8 255))).drop (sp.le32 id').length = [] :=
                List.drop_eq_nil_of_le (by rw [hsub4']; omega)
              isimp only [hdrop', List.append_nil] at Hsl
              wp_auto
              icases replica.bs5_acc b_ptr _ hbb' $$ Hsl with ⟨Hs1, Hback⟩
              have hsub : subslice (sint.nat (W64 1)) (sint.nat (W64 5))
                  ((bb.set 0 (W8 255)).take 1 ++ sp.le32 id') =
                  sp.le32 id' ++ [] := by
                have hl : (sp.le32 id').length = 4 := h4
                have h1 : ((bb.set 0 (W8 255)).take 1).length = 1 := by
                  simp [Hbb]
                rw [show sint.nat (W64 1) = 1 from rfl, show sint.nat (W64 5) = 5 from rfl]
                simp only [subslice, List.append_nil]
                rw [List.take_of_length_le (by simp [hl]; omega)]
                rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
                  List.nil_append]
              rw [hsub]
              wp_apply encoding.binary.wp_LittleEndian_Uint32 _ (sp.le32 id') _ []
                (by simp [sp.le32, u32Le_length]) $$ [$Hpkg5 $Hs1] as Hs1
              ihave Hsl := Hback $$ %(sp.le32 id' ++ []) [] Hs1
              · ipureintro; simpa using h4
              rw [show leToU32 (sp.le32 id') = id' from u32Le_to_word id']
              clear hbb'
              have hbb' : (((bb.set 0 (W8 255)).take 1 ++ sp.le32 id').take 1 ++
                  (sp.le32 id' ++ [])).length = 5 := by simp [Hbb, h4]
              wp_if_destruct
              · reject
              · try wp_auto
                wp_if_destruct
                · reject
                · -- accepted: peer `id'` (above this replica, below `N`)
                  have hid0 : me.toInt < id'.toInt := by
                    have : sint.Z id' = id'.toInt := rfl
                    have : sint.Z me = me.toInt := rfl
                    omega
                  have hidN : id'.toInt < N := by
                    have e0 : sint.Z (W64 (N : Int)) = N := by
                      simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
                      exact Int.bmod_eq_of_le (by omega) (by omega)
                    have e1 : sint.Z (W32 (sint.Z (W64 (N : Int)))) = N := by
                      rw [e0]; simp only [W32, sint.Z]; rw [BitVec.toInt_ofInt]
                      exact Int.bmod_eq_of_le (by omega) (by omega)
                    have : sint.Z id' = id'.toInt := rfl
                    omega
                  obtain ⟨j, hj⟩ : ∃ j, j = id'.toInt.toNat := ⟨_, rfl⟩
                  have hidz : sint.Z (W64 (sint.Z id')) = (j : Int) := by
                    have : sint.Z id' = id'.toInt := rfl
                    rw [this]; simp only [W64, sint.Z]; rw [BitVec.toInt_ofInt]
                    rw [Int.bmod_eq_of_le (by omega) (by omega)]; omega
                  have hjr : (List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1)))[j - (me.toInt.toNat + 1)]?
                      = some j := by
                    rw [List.getElem?_range' (by omega)]; congr 1; omega
                  icases (BigSepL.bigSepL_lookup_acc hjr).1 $$ Hslots with ⟨Hslot, Hslots⟩
                  iunfold replica.peerSlot at Hslot
                  icases Hslot with ⟨%cv0, %rd0, %w0, %al0, Hps1, Hpr1, Hpw1, Hal1, -⟩
                  rw [hidz]
                  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
                  try wp_auto
                  try rw [hidz]
                  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
                  try wp_auto
                  ihave #Hpc : bufio.prefixClosed (sp.outQ γ γc γm cid) $$ []
                  · iunfold bufio.prefixClosed; iapply sp.outQ_prefixClosed
                  ihave #Hwok := bufio.writerOk_conn _ cid true (sp.outQ γ γc γm) $$ [$Hpkg3 $Hci $Hpc]
                  ihave Hq0 : (□ sp.outQ γ γc γm cid [] : IProp netDistGF) $$ []
                  · imodintro; iapply sp.outQ_nil
                  wp_apply bufio.wp_NewWriter _ _ _ [] $$ [$Hwok $Hsend $Hq0] as %w Hw
                  try wp_auto
                  try rw [hidz]
                  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
                  try wp_auto
                  try rw [hidz]
                  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
                  try wp_auto
                  wp_apply wp_slice_literal (V := GoInterface)
                  isplitr
                  · ipureintro; rfl
                  iintro %s1 ⟨-, -⟩
                  try wp_auto
                  wp_apply replica.wp_Printf wp_Printf $$ [$Hlg $Hq]
                  wp_for_post
                  ihave Hslots := Hslots $$ %j [Hps1 Hpr1 Hpw1 Hal1 Hrd Hw]
                  · unfold replica.peerSlot
                    iexists _, br, w, true
                    iframe Hps1 Hpr1 Hpw1 Hal1
                    iright
                    have hk : sp.peerRdKind me j = .peerIn id' := by
                      unfold sp.peerRdKind
                      rw [if_neg (by omega)]
                      congr 1
                      apply BitVec.eq_of_toInt_eq
                      simp only [W32]; rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by omega) (by omega)]
                      omega
                    have hw : sp.peerWrKind me j = .peerIn := by
                      unfold sp.peerWrKind; rw [if_neg (by omega)]
                    rw [hk, hw]
                    simp only [sp.RdKind.side, sp.RdKind.proto]
                    iexists cid, (sp.helloBytes id')
                    iframe Hci Hkind Hrd
                    isplitr
                    · ipureintro; exact ⟨by simp [sp.RdKind.head, sp.framesOf], by simp⟩
                    unfold sp.wrSt
                    simp only [sp.WrKind.side, sp.WrKind.proto, sp.WrKind.conn]
                    iexists _, cid, [], [], _
                    iframe Hci Hkind Hwok Hw
                    iright
                    unfold sp.wrAt
                    iexists []
                    isplitr
                    · ipureintro; simp [sp.WrKind.head, sp.framesOf]
                    iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
                  have hset : (List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1))).set
                      (j - (me.toInt.toNat + 1)) j =
                      List.range' (me.toInt.toNat + 1) (N - (me.toInt.toNat + 1)) := by
                    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hjr
                    conv => rhs; rw [← List.set_getElem_self hlt]
                    rw [heq]
                  rw [hset]
                  iframe
                  iexists _, pcsl, pcs, _
                  iframe
                  ipureintro; exact hbb'
          · -- a client's connection (P1): kept aside
            try wp_auto
            wp_apply wp_slice_literal (V := replica.pendingClient)
              [replica.pendingClient.mk (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) br c0]
            isplitr
            · ipureintro; rfl
            iintro %s1 ⟨Hs1, -⟩
            try wp_auto
            wp_apply wp_slice_append pcsl pcs _ _ (DFrac.own 1) $$ [$Hpcs $Hcap $Hs1] as %pcsl' ⟨Hpcs, Hcap, -⟩
            try wp_auto
            wp_for_post
            iframe
            iexists _, pcsl', pcs ++ [replica.pendingClient.mk
              (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) br c0], bb
            iframe i Hpc Hpcs Hcap Hslots Hsl
            isplitl [Hpok Hrd Hsend]
            · iapply (BigSepL.bigSepL_snoc).2
              iframe Hpok
              unfold replica.pendingOk
              iexists cid
              iframe Hci Hsend
              simp only [List.nil_append]
              iframe Hrd
              ipureintro; exact Hif
            ipureintro; exact Hbb
        · rcases er with eo | _
          · wp_auto
            wp_apply wp_slice_literal (V := GoInterface)
            isplitr
            · ipureintro; rfl
            iintro %s1 ⟨-, -⟩
            try wp_auto
            wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hq]
            wp_for_post
            iframe
            iexists _, pcsl, pcs, bb
            iframe
            ipureintro; exact Hbb
          · exact absurd rfl Hen
      · subst Hcv Her
        wp_auto
        wp_apply wp_slice_literal (V := GoInterface)
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨-, -⟩
        try wp_auto
        wp_apply replica.wp_Println wp_Println $$ [$Hlg $Hq]
        wp_for_post
        iframe
        iexists _, pcsl, pcs, bb
        iframe
        ipureintro; exact Hbb
    · -- the loop ends: the slots go back on `done`
      wp_pures
      try wp_auto
      wp_apply (wp_bag_send (V := Bool) γd done true _) $$ [HLis Hpc Hpcs Hpok Hslots]
      · iframe Hdone
        unfold replica.acceptSt
        iexists _, pcsl, pcs
        iframe
        unfold replica.listenerOk
        iexists ll, lid
        iframe Hlis
        ipureintro; rfl
      try wp_auto
      iapply HΦ; itrivial
  · subst Hlv Her
    wp_auto
    rw [if_pos (by simp)]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply wp_load_slice_index _ _ _ _ a (by omega) $$ [Hl] as -
    · iframe Hl; ipureintro; rw [hmez]; exact hla
    try wp_auto
    wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #a, GoInterface.ok i]
    isplitr
    · ipureintro; rfl
    iintro %s1 ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_Fatal wp_Fatal $$ [$Hlg $Hq]
    wp_apply time.wp_Sleep
    try wp_auto
    rw [hwild]
    wp_apply hL $$ [$Htok] as %lv' %er' ⟨Htok, Hres⟩
    · ipureintro; exact Hip
    try wp_auto
    wp_for_post
    iframe
    iexists lv', er'
    iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
