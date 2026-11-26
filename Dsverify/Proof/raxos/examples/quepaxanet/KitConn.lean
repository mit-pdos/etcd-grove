/-
Client machine `c`'s connections to the replicas' proxies (`kit.go`'s `replica`): the lock
invariant `repInv`, the persistent `isReplica`, and `connect`, `tryConnect`, `drop`, `reset`,
`send` (the lab's `Kit/{ConnDefs,ConnOps,ConnSend}.lean`, re-based on `Net/` and the landed
`bufio`).

* **Disconnected**: `r.c` is `nil` (`r.w` anything).
* **Connected** (`connInv`): `r.c` holds the dialer end of a connection `cn` to `proxyAddr k`
  (`net.connAt`), `r.w` a `*bufio.Writer` over it writing with the proxy port's protocol
  `proxyInProto γ k` (`ownBufWriter`): what went to the connection and what is buffered is exactly
  client `c`'s handshake and the frames of `L` (`hs (21 + c) ++ frs L`), each fit, frame `n` of a
  registered batch carrying a ticket of replica `k` at `(cn, n)` (`tixAt`).

A frame whose batch the codec rejects (`Marshal` fails after its code byte) is written as the
code byte only, a prefix of the `nil` batch's frame (`frameBatch`): its ticket is registered before
the code byte is written, and the connection is dropped after.

The library specs (`net`'s) are parameters; `bufio`'s and `proto`'s are the landed proofs and
`cbMarshal_proof` (`KitWire.lean`).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitWire
public import Dsverify.Proof.raxos.examples.quepaxanet.KitAwait
public import Dsverify.Proof.raxos.Proxy.NetDial

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure raxos.msg
open EtcdGrove (bufio.ownBufWriter)

/-! ## Pure facts of the frames -/

/-- A batch a frame may carry: well formed, its encoding below `2^63`. -/
abbrev frOk (b : Batch) : Prop := batchFit b

theorem kc_nilBatch_ok : batchOk nilBatch := by
  refine ⟨?_, by unfold strOk; decide, ?_⟩
  · unfold i64Ok nilBatch; simp only; omega
  · intro m hm; simp [nilBatch] at hm

theorem nilBatch_frOk : frOk nilBatch := ⟨kc_nilBatch_ok, by decide +kernel⟩

/-- The batch a frame carries: `b` if fit, else the `nil` batch. -/
def frameBatch (b : Batch) : Batch := by
  classical exact if frOk b then b else nilBatch

theorem frameBatch_ok (b : Batch) : frOk (frameBatch b) := by
  unfold frameBatch; split
  · assumption
  · exact nilBatch_frOk

theorem frameBatch_of_ok (b : Batch) (h : frOk b) : frameBatch b = b := by
  unfold frameBatch; simp [h]

theorem decStr_proxy (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) :
    decStr (7606 + k) = [BitVec.ofNat 8 55, BitVec.ofNat 8 54, BitVec.ofNat 8 (48 + (6 + k) / 10),
      BitVec.ofNat 8 (48 + (6 + k) % 10)] := by
  rw [show 7606 + k = 7600 + (6 + k) by omega]
  exact decStr_76 _ (by omega)

/-- Replica `k`'s proxy address is valid and its wildcard listener takes it. -/
theorem proxyAddr_ok (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) :
    addrOk (proxyAddr k) = true ∧ lisAccepts (proxyLis k) (proxyAddr k) := by
  rw [← lisAcceptsB_iff]
  unfold proxyAddr proxyLis portAddr
  rw [decStr_proxy k hk]
  obtain ⟨h1, h5⟩ := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem proxyIdx_mem (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) : k ∈ ([1, 2, 3, 4, 5] : List Nat) := by
  obtain ⟨h1, h5⟩ := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem hs_client_bytes (c : Nat) (hc : c < 6) (x0 x1 : w8) :
    ([x0, x1, W8 0, W8 0].set 0 (W8 (uint.Z (W16 (uint.Z (W64 ((21 + c : Nat) : Int))))))).set 1
      (W8 (uint.Z (W16 (uint.Z (W64 ((21 + c : Nat) : Int))) >>> W64 8))) = raxos.hs (21 + c) := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Replica `k`'s proxy address's protocols, from the shared facts. -/
theorem proxyProto_of_shared (γ : QNames) (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) :
    sharedRes (GF := GF) γ ⊢ addrProto (proxyAddr k) (proxyInProto γ k) silentProto := by
  unfold sharedRes netProtos
  iintro ⟨-, -, ⟨-, -, -, -, #Hps, -⟩, -⟩
  ihave #Hl := (BigSepL.bigSepL_mem (Φ := fun k : Nat => lisProto (Gg := Gg) (proxyLis k)
    (proxyInProto (GF := GF) γ k) silentProto) (proxyIdx_mem k hk)) $$ Hps
  iapply lisProto_addr _ _ _ _ (proxyAddr_ok k hk).1 (proxyAddr_ok k hk).2 $$ Hl

/-- The proxy port's protocol is prefix-closed. -/
theorem proxyInProto_prefixClosed (γ : QNames) (k : Nat) :
    ProtoPrefixClosed (GF := GF) (proxyInProto γ k) where
  nil cn := by
    iintro !>
    unfold proxyInProto
    iexists 0, []
    isplitr
    · ipureintro; exact ⟨by decide, List.nil_prefix, by simp⟩
    · iempintro
  pre cn a b h := by
    iintro #H
    iintro !>
    unfold proxyInProto
    icases H with ⟨%c, %L, %Hp, #HL⟩
    iexists c, L
    iframe HL
    ipureintro
    exact ⟨Hp.1, h.trans Hp.2.1, Hp.2.2⟩

instance tixAt_persistent' (γ : QNames) (t : Ticket) (cn n : Nat) :
    Persistent (tixAt (GF := GF) γ t cn n) := by
  unfold tixAt; infer_instance

/-- The frames' facts of a connection that carried `L`. -/
def framesOk (γ : QNames) (k : Nat) (cn : Nat) (L : List Batch) : IProp GF :=
  iprop([∗list] n ↦ b ∈ L, batchReg γ b.id b ∗ ∃ c j, tixAt γ ((k : Int), c, j) cn n)

instance framesOk_persistent (γ : QNames) (k cn : Nat) (L : List Batch) :
    Persistent (framesOk (GF := GF) γ k cn L) := by
  unfold framesOk; infer_instance

theorem framesOk_snoc (γ : QNames) (k cn : Nat) (L : List Batch) (b : Batch) (c j : Nat) :
    framesOk (GF := GF) γ k cn L ∗ batchReg γ b.id b ∗ tixAt γ ((k : Int), c, j) cn L.length ⊢
      framesOk γ k cn (L ++ [b]) := by
  iintro ⟨HL, Hb, Ht⟩
  unfold framesOk
  iapply BigSepL.bigSepL_snoc.2
  iframe HL Hb
  iexists c, j
  iexact Ht

/-- A prefix of the stream with one more frame is allowed. -/
theorem proto_of_frames (γ : QNames) (k cn : Nat) (L : List Batch) (b : Batch) (c j : Nat)
    (hc : c < 6) (pre : List w8) (hpre : pre <+: frame b) (hok : ∀ x ∈ L, frOk x)
    (hb : frOk b) :
    framesOk (GF := GF) γ k cn L ∗ batchReg γ b.id b ∗ tixAt γ ((k : Int), c, j) cn L.length ⊢
      proxyInProto γ k cn (raxos.hs (21 + c) ++ frs L ++ pre) := by
  iintro H
  ihave HL := framesOk_snoc γ k cn L b c j $$ H
  unfold proxyInProto
  iexists c, L ++ [b]
  unfold framesOk
  iframe HL
  ipureintro
  refine ⟨hc, ?_, ?_⟩
  · have : (L ++ [b]).map frame = L.map frame ++ [frame b] := by simp
    rw [this, List.flatten_append, List.flatten_singleton, ← List.append_assoc]
    exact (List.prefix_append_right_inj _).2 hpre
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hok x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hb

theorem frameBatch_reg (γ : QNames) (b : Batch) :
    batchReg (GF := GF) γ b.id b ∗ sharedRes γ ⊢ batchReg γ (frameBatch b).id (frameBatch b) := by
  iintro ⟨Hb, Hsh⟩
  unfold frameBatch
  split
  · iexact Hb
  · unfold sharedRes
    icases Hsh with ⟨-, -, -, Hn, -⟩
    iExactEq Hn; rfl


end ghost

/-! ## The connection's state -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "repTy" => raxos.examples.quepaxanet.replica

/-- The connected state: see the file header. -/
def connInv (γ : QNames) (c k : Nat) (cv : GoInterface) (w : Loc) : IProp GF :=
  iprop(∃ (t : Loc) (cn : Nat) (la ra ed : GoInterface) (L : List Batch) (sent pend : List w8)
      (err : GoInterface),
    ⌜cv = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t⌝ ∗
    net.connAt t cn false (proxyAddr k) la ra ∗ connIs cn ∗
    globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
    bufio.ownBufWriter w (net.connIface t) (sendTok cn false (proxyInProto γ k))
      (proxyInProto γ k cn) (net.connWriteE la ra ed) 4096 sent pend err ∗
    ⌜sent ++ pend = raxos.hs (21 + c) ++ frs L ∧ ∀ b ∈ L, frOk b⌝ ∗
    framesOk γ k cn L)

/-- The lock invariant of client `c`'s connection `r` to replica `k`. -/
def repInv (γ : QNames) (c k : Nat) (r : Loc) : IProp GF :=
  iprop(∃ (cv : GoInterface) (w : Loc),
    structFieldRef repTy go!"c" r ↦ cv ∗ structFieldRef repTy go!"w" r ↦ w ∗
    (⌜cv = interface.nil⌝ ∨ connInv γ c k cv w))

/-- The persistent facts of client `c`'s connection `r` to replica `k` (besides its lock). -/
def repFacts (γ : QNames) (c k : Nat) (r : Loc) : IProp GF :=
  iprop(⌜c < 6 ∧ 1 ≤ k ∧ k ≤ 5⌝ ∗
    structFieldRef repTy go!"name" r ↦□ W64 ((21 + c : Nat) : Int) ∗
    structFieldRef repTy go!"addr" r ↦□ proxyAddr k ∗ sharedRes γ)

/-- Client `c`'s connection `r` to replica `k` (persistent). -/
def isReplica (γ : QNames) (c k : Nat) (r : Loc) : IProp GF :=
  iprop(repFacts γ c k r ∗ sync.isMutex (structFieldRef repTy go!"mu" r) (repInv γ c k r))

instance repFacts_persistent (γ : QNames) (c k : Nat) (r : Loc) :
    Persistent (repFacts (GF := GF) γ c k r) := by
  unfold repFacts; infer_instance

instance isReplica_persistent (γ : QNames) (c k : Nat) (r : Loc) :
    Persistent (isReplica (GF := GF) γ c k r) := by
  unfold isReplica; infer_instance

/-- A fresh `replica` (`&replica{name: 21 + c, addr: proxyAddr k}`) is client `c`'s connection to
replica `k`. -/
theorem replica_init (γ : QNames) (c k : Nat) (hc : c < 6) (hk : 1 ≤ k ∧ k ≤ 5) (r : Loc) :
    ⊢ r ↦ ({ (zero_val raxos.examples.quepaxanet.replica) with
          name' := W64 ((21 + c : Nat) : Int), addr' := proxyAddr k } :
        raxos.examples.quepaxanet.replica) -∗
      sharedRes γ ={⊤}=∗ isReplica (GF := GF) γ c k r := by
  iintro Hr #Hsh
  iStructNamed Hr
  ipersist addr
  ipersist name
  imod sync.init_Mutex (repInv γ c k r) ⊤ _ $$ mu [«c» w] with #Hmu
  · inext
    unfold repInv
    iexists _, _
    iframe «c» w
    ileft; ipureintro; rfl
  imodintro
  unfold isReplica repFacts
  iframe Hmu Hsh addr name
  ipureintro; exact ⟨hc, hk⟩

end defs

/-! ## The operations -/

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [_root_.Perennial.bufio.Assumptions]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]
variable [QpBufioDeps GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet
local notation "repTy" => raxos.examples.quepaxanet.replica

set_option goose.wp.extras true

/-- `tix_register` at the full mask. -/
theorem tix_register_top (γ : QNames) (t : Ticket) (cn n : Nat) (ht : t ∈ tickets) :
    ⊢ inv consN (consInv (GF := GF) γ) -∗ ticketTok γ t ={⊤}=∗ tixAt γ t cn n :=
  tix_register γ ⊤ (by simp) t cn n ht

/-- `r.drop()`: close the connection, `r.c` and `r.w` `nil`. -/
theorem wp_drop (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (r : Loc) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) (w : Loc) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ net.connAt (GF := GF) t cn false a la ra ∗ connIs cn ∗
        structFieldRef repTy go!"c" r ↦ interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
        structFieldRef repTy go!"w" r ↦ w }}
      (App (Val (r @!! go.GoType.PointerType raxos.examples.quepaxanet.replica.ty @!! go!"drop"))
        (Val #()))
    {{ RET #(); structFieldRef repTy go!"c" r ↦ interface.nil ∗
        structFieldRef repTy go!"w" r ↦ Loc.null }} := by
  wp_start as ⟨#Hca, #Hconn, Hc, Hw⟩
  wp_auto
  wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [] as %e -
  · iframe Hca
    imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  wp_end

/-- `r.connect()` (`r.mu` held, `r.c` `nil`): dial replica `k`'s proxy and send the handshake;
on success the connected state, with no frame yet. -/
theorem wp_connect (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γ : QNames) (c k : Nat) (r : Loc) (w : Loc) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ repFacts γ c k r ∗
        structFieldRef repTy go!"c" r ↦ interface.nil ∗ structFieldRef repTy go!"w" r ↦ w }}
      (App (Val (r @!! go.GoType.PointerType raxos.examples.quepaxanet.replica.ty @!! go!"connect"))
        (Val #()))
    {{ (ok : Bool), RET #ok; ∃ (cv : GoInterface) (w' : Loc),
        structFieldRef repTy go!"c" r ↦ cv ∗ structFieldRef repTy go!"w" r ↦ w' ∗
        if ok then connInv γ c k cv w' else ⌜cv = interface.nil⌝ }} := by
  wp_start as ⟨#Hf, Hc, Hw⟩
  unfold repFacts
  icases Hf with ⟨%hck, #Hname, #Haddr, #Hsh⟩
  obtain ⟨hc, hk⟩ := hck
  ihave #Hpr := proxyProto_of_shared γ k hk $$ Hsh
  ihave %Hok2 := addrTok_ok (proxyAddr k) $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  wp_auto
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp (proxyAddr k) iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (proxyInProto γ k) silentProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %cv %err (⟨%Herr, %cn, #Hc2, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · (try iframe HnetPk)
    isplitr
    · ipureintro; exact Hok2
    isplit
    · itrivial
    · iapply dial_au (proxyAddr k) (proxyInProto γ k) silentProto $$ Hpr
  · subst Herr
    iunfold connEnd at Hend
    icases Hend with ⟨Hs, -⟩
    ihave #Hconn := sendTok_connIs cn false _ _ $$ Hs
    iunfold net.isConn at Hc2
    icases Hc2 with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
    · iPkgInit
    ihave #Hle := encoding.binary.isInit_access $$ Hbin
    icases Hle with ⟨#Hle, -⟩
    have h0 : sint.Z (W64 0) = 0 := rfl
    have h4 : W64 4 - W64 0 = W64 4 := rfl
    rw [h0, go.arrayIndexRef_0, h4]
    ihave Hsl := slice_array hs_ptr 4 _ (by decide) $$ hs
    rw [show (zero_val (GoArray w8 4)).arr = [W8 0, W8 0, W8 0, W8 0] from rfl]
    wp_method_call
    wp_call
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_load_slice_index _ (sint.Z (W64 1)) [W8 0, W8 0, W8 0, W8 0] _ (W8 0) (by word) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    wp_apply wp_store_slice_index _ (sint.Z (W64 0)) _ _ $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; simp
    (try wp_auto)
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro
      simp
    rw [hs_client_bytes c hc (W8 0) (W8 0)]
    ihave #Hhs : □ proxyInProto (GF := GF) γ k cn (raxos.hs (21 + c)) $$ []
    · iintro !>
      unfold proxyInProto
      iexists c, []
      isplitr
      · ipureintro; exact ⟨hc, by simp, by simp⟩
      · iapply BigSepL.bigSepL_nil.2; iempintro
    ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
    · iPkgInit
    ihave ⟨%ed, #Hed⟩ := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
    rw [h0, go.arrayIndexRef_0, h4]
    wp_apply wp_Write t cn false (proxyAddr k) la ra _ (raxos.hs (21 + c)) (DFrac.own 1) ed
        (writeP cn false (proxyInProto γ k) []) $$ [Hsl Hs]
      as %n %err ⟨%w0, %res, Hs, Hsl, %Hw0, #HE⟩
    · iframe Hca Hsl Hed
      isplitl [Hs]
      · iapply writeP_init $$ Hs
      · iapply write_acc cn false (proxyInProto γ k) [] (raxos.hs (21 + c))
        simp only [List.nil_append]; iexact Hhs
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨hw, -, hnone, -⟩ := Hw0
    unfold writeP
    cases res with
    | some ke =>
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply wp_Close t cn false (proxyAddr k) la ra (fun _ => iprop(True)) $$ [] as %e -
      · iframe Hca
        imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
        imodintro
        iexists st, dd
        iframe Hst Hdd
        iintro %res %st' %d' %Hd' Hst Hdd
        imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
        imodintro
        itrivial
      wp_end
      iexists _, _
      iframe Hc Hw
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; first | rfl | trivial
    | none =>
      have herr := Hne.1 rfl
      subst herr
      have hw' : w0 = raxos.hs (21 + c) := hnone rfl
      subst hw'
      simp only [List.nil_append]
      wp_auto
      ihave #Hwok := net.conn_streamWriterOk wp_Write t cn false (proxyAddr k) la ra ed
        (proxyInProto γ k) (proxyInProto_prefixClosed γ k) $$ [$Hca $Hed]
      ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
      · iPkgInit
      rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t =
        GoInterface.ok (net.connIface t) from rfl]
      wp_apply QpBufioDeps.newWriter
          (net.connIface t) (sendTok cn false (proxyInProto γ k))
          (proxyInProto γ k cn) (net.connWriteE la ra ed) (raxos.hs (21 + c)) $$ [Hs] as %bw Hbw
      · iframe Hbufio Hwok Hs Hhs
        ipureintro; exact net.connIface_ne_bufioWriter t
      wp_end
      iexists _, bw
      iframe Hc Hw
      simp only [↓reduceIte]
      unfold connInv
      iexists t, cn, la, ra, ed, [], raxos.hs (21 + c), [], interface.nil
      iframe Hca Hconn Hed Hbw
      isplitr
      · ipureintro; first | rfl | exact ⟨by simp [frs], by simp⟩
      isplitr
      · ipureintro; exact ⟨by simp [frs], by simp⟩
      · unfold framesOk; iapply BigSepL.bigSepL_nil.2; iempintro
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_end
    iexists _, _
    iframe Hc Hw
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; first | rfl | trivial

/-- The connected state's connection value. -/
theorem connInv_cv (γ : QNames) (c k : Nat) (cv : GoInterface) (w : Loc) :
    connInv (GF := GF) γ c k cv w ⊢ connInv γ c k cv w ∗
      ∃ (t : Loc) (cn : Nat) (la ra : GoInterface),
        ⌜cv = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t⌝ ∗
        net.connAt t cn false (proxyAddr k) la ra ∗ connIs cn := by
  unfold connInv
  iintro ⟨%t, %cn, %la, %ra, %ed, %L, %sent, %pend, %err, %Hcv, #Hca, #Hconn, #Hed, Hbw, %HS, #HL⟩
  isplitl
  · iexists t, cn, la, ra, ed, L, sent, pend, err
    iframe Hca Hconn Hed Hbw HL
    ipureintro; exact ⟨Hcv, HS⟩
  · iexists t, cn, la, ra
    iframe Hca Hconn
    ipureintro; exact Hcv

/-- `r.tryConnect()`. -/
theorem wp_tryConnect (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γ : QNames) (c k : Nat) (r : Loc) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isReplica γ c k r }}
      (App (Val (r @!! go.GoType.PointerType raxos.examples.quepaxanet.replica.ty @!!
        go!"tryConnect")) (Val #()))
    {{ (ok : Bool), RET #ok; True }} := by
  wp_start as #Hr
  unfold isReplica
  icases Hr with ⟨#Hf, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HR⟩
  unfold repInv
  icases HR with ⟨%cv, %w, Hc, Hw, (%Hnil | Hconn)⟩
  · subst Hnil
    wp_auto
    wp_apply wp_connect wp_Dial wp_Write wp_Close γ c k r w $$ [$Hf $Hc $Hw]
      as %ok ⟨%cv', %w', Hc, Hw, Hst⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw Hst]
    · iexists cv', w'
      iframe Hc Hw
      cases ok
      · ileft; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hst
      · iright; simp only [↓reduceIte]; iexact Hst
    wp_end
  · icases connInv_cv γ c k cv w $$ Hconn with ⟨Hconn, %t, %cn, %la, %ra, %Hcv, #Hca, #Hcis⟩
    subst Hcv
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw Hconn]
    · iexists _, w
      iframe Hc Hw
      iright; iexact Hconn
    wp_end

/-- `r.reset()`. -/
theorem wp_reset (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γ : QNames) (c k : Nat) (r : Loc) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isReplica γ c k r }}
      (App (Val (r @!! go.GoType.PointerType raxos.examples.quepaxanet.replica.ty @!!
        go!"reset")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hr
  unfold isReplica
  icases Hr with ⟨#Hf, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HR⟩
  unfold repInv
  icases HR with ⟨%cv, %w, Hc, Hw, (%Hnil | Hconn)⟩
  · subst Hnil
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw]
    · iexists _, w
      iframe Hc Hw
      ileft; ipureintro; rfl
    wp_end
  · icases connInv_cv γ c k cv w $$ Hconn with ⟨-, %t, %cn, %la, %ra, %Hcv, #Hca, #Hcis⟩
    subst Hcv
    wp_auto
    wp_apply wp_drop wp_Close r t cn _ la ra w $$ [$Hca $Hcis $Hc $Hw] as ⟨Hc, Hw⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw]
    · iexists _, _
      iframe Hc Hw
      ileft; ipureintro; rfl
    wp_end

/-- `r.send(b)`: batch `bv` (registered) sent by client `c` to replica `k`'s proxy with ticket
`(k, c, j)`, or the connection dropped. -/
theorem wp_send (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γ : QNames) (k : Nat) (r b : Loc) (dq : DFrac) (bv : Batch) (c j : Nat) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isReplica γ c k r ∗ repCB b dq bv ∗
        batchReg γ bv.id bv ∗ ticketTok γ ((k : Int), c, j) ∗ ⌜((k : Int), c, j) ∈ tickets⌝ }}
      (App (Val (r @!! go.GoType.PointerType raxos.examples.quepaxanet.replica.ty @!! go!"send"))
        (Val #b))
    {{ RET #(); repCB b dq bv }} := by
  wp_start as ⟨#Hr, HCB, #Hreg, Htk, %ht⟩
  unfold isReplica
  icases Hr with ⟨#Hf, #Hmu⟩
  ihave #Hf2 := Hf
  iunfold repFacts at Hf2
  icases Hf2 with ⟨%hck, -, -, #Hsh⟩
  obtain ⟨hc, hk⟩ := hck
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HR⟩
  unfold repInv
  icases HR with ⟨%cv, %w, Hc, Hw, HR⟩
  ipersist r
  wp_join (Q := fun v => iprop(∃ ok : Bool, ⌜v = #ok⌝ ∗ ∃ (cv : GoInterface) (w : Loc),
      structFieldRef repTy go!"c" r ↦ cv ∗ structFieldRef repTy go!"w" r ↦ w ∗
      if ok then connInv γ c k cv w else ⌜cv = interface.nil⌝)) at (If _ (Val #true) _)
    with [Hc Hw HR]
  · icases HR with (%Hnil | Hconn)
    · subst Hnil
      wp_auto
      wp_apply wp_connect wp_Dial wp_Write wp_Close γ c k r w $$ [$Hf $Hc $Hw] as %ok Hst
      iexists ok
      isplitr
      · ipureintro; rfl
      · iexact Hst
    · icases connInv_cv γ c k cv w $$ Hconn with ⟨Hconn, %t, %cn, %la, %ra, %Hcv, -, -⟩
      subst Hcv
      wp_auto
      iexists true
      isplitr
      · ipureintro; rfl
      iexists _, w
      iframe Hc Hw
      simp only [↓reduceIte]
      iexact Hconn
  iintro ⟨%ok, %Hv, %cv', %w', Hc, Hw, Hst⟩
  subst Hv
  cases ok
  · -- not connected
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw Hst]
    · iexists _, w'
      iframe Hc Hw
      ileft; iexact Hst
    wp_end
  simp only [↓reduceIte]
  -- connected: register the frame's ticket
  iunfold connInv at Hst
  icases Hst with ⟨%t, %cn, %la, %ra, %ed, %L, %sent, %pend, %err, %Hcv, #Hca, #Hcis, #Hed, Hbw,
    %HS, #HL⟩
  subst Hcv
  ihave #Hsh2 := Hsh
  iunfold sharedRes at Hsh2
  icases Hsh2 with ⟨#Hinv, -⟩
  imod tix_register_top γ _ cn L.length ht $$ Hinv Htk with #Htix
  ihave #Hreg' := frameBatch_reg γ bv $$ [$Hreg $Hsh]
  have hfok := frameBatch_ok bv
  ihave #HQ1 : (□ proxyInProto (GF := GF) γ k cn (sent ++ pend ++ [W8 1])) $$ []
  · iintro !>
    rw [HS.1]
    iapply proto_of_frames γ k cn L (frameBatch bv) c j hc [W8 1] (by simp [frame]) HS.2 hfok
    iframe HL Hreg' Htix
  wp_auto
  wp_apply QpBufioDeps.writeByte w'
      (net.connIface t) _ _ _ 4096 sent pend err (W8 1) $$ [Hbw]
    as %e1 ⟨%s1, %p1, %H1, Hbw⟩
  · iframe Hbw; iintro %_; iexact HQ1
  rcases e1 with ei | _
  · -- `WriteByte` failed
    dsimp only
    wp_auto
    wp_apply wp_drop wp_Close r t cn _ la ra w' $$ [$Hca $Hcis $Hc $Hw] as ⟨Hc, Hw⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw]
    · iexists _, _; iframe Hc Hw; ileft; ipureintro; rfl
    wp_end
  have H1 := H1.2.1 rfl
  dsimp only
  wp_auto
  ihave #HQ2 : □ (⌜batchFit bv⌝ → proxyInProto (GF := GF) γ k cn
      (s1 ++ p1 ++ le8 (encBatch bv).length) ∗ proxyInProto γ k cn
      (s1 ++ p1 ++ le8 (encBatch bv).length ++ encBatch bv)) $$ []
  · iintro !> %hb
    have e : s1 ++ p1 = raxos.hs (21 + c) ++ frs L ++ [W8 1] := by
      rw [H1, HS.1]
    rw [e]
    isplitl []
    · rw [show raxos.hs (21 + c) ++ frs L ++ [W8 1] ++ le8 (encBatch bv).length =
          raxos.hs (21 + c) ++ frs L ++ ([W8 1] ++ le8 (encBatch bv).length) by
          simp [List.append_assoc]]
      iapply proto_of_frames γ k cn L bv c j hc ([W8 1] ++ le8 (encBatch bv).length)
        (by simp [frame]) HS.2 hb
      rw [frameBatch_of_ok bv hb]
      iframe HL Hreg Htix
    · rw [show raxos.hs (21 + c) ++ frs L ++ [W8 1] ++ le8 (encBatch bv).length ++ encBatch bv =
          raxos.hs (21 + c) ++ frs L ++ frame bv by simp [frame, List.append_assoc]]
      iapply proto_of_frames γ k cn L bv c j hc (frame bv) (List.prefix_refl _) HS.2 hb
      rw [frameBatch_of_ok bv hb]
      iframe HL Hreg Htix
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client $$ []
  · iPkgInit
  wp_apply cbMarshal_proof b dq bv w' (net.connIface t) _ _ _ 4096 s1 p1 GoInterface.nil $$
    [$HCB $Hbw $HQ2 $Hcl] as %e2 ⟨HCB, %s2, %p2, %e2', %H2, Hbw⟩
  rcases e2 with ei | _
  · -- `Marshal` failed
    dsimp only
    wp_auto
    wp_apply wp_drop wp_Close r t cn _ la ra w' $$ [$Hca $Hcis $Hc $Hw] as ⟨Hc, Hw⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw]
    · iexists _, _; iframe Hc Hw; ileft; ipureintro; rfl
    wp_end
  obtain ⟨hb, H2⟩ := H2 rfl
  dsimp only
  wp_auto
  wp_apply QpBufioDeps.flush w' _ _ _ _ 4096 s2 p2 e2' $$ Hbw
    as %e3 ⟨%k3, %H3, Hbw⟩
  rcases e3 with ei | _
  · -- `Flush` failed
    dsimp only
    wp_auto
    wp_apply wp_drop wp_Close r t cn _ la ra w' $$ [$Hca $Hcis $Hc $Hw] as ⟨Hc, Hw⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw]
    · iexists _, _; iframe Hc Hw; ileft; ipureintro; rfl
    wp_end
  dsimp only
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hc Hw Hbw]
  · iexists _, _
    iframe Hc Hw
    iright
    unfold connInv
    iexists t, cn, la, ra, ed, L ++ [bv], _, _, GoInterface.nil
    iframe Hca Hcis Hed Hbw
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro
      refine ⟨?_, ?_⟩
      · rw [List.append_assoc, List.take_append_drop, H2, H1, HS.1, frs_append]
        simp [frs, frame, List.append_assoc]
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact HS.2 x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hb
    · rw [show L.length = L.length from rfl]
      iapply framesOk_snoc γ k cn L bv c j
      iframe HL Hreg Htix
  wp_end

end ops

end raxos.examples.quepaxanet
end Perennial
