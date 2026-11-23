/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Handler.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B2: `NewEPaxosRMWHandler(r, false, false)` (the EPaxos handler at the initial model state;
the executor is not started here: fork ba86001, B-R7).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.Lib.MathHyps
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model replica2
open Perennial.gryff.replica (XS rowOwn stackOwn euOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

set_option goose.wp.extras true

theorem setAppRep {α : Type} (l : List α) (a b : α) (n : Nat) (h : l.length < n) :
    (l ++ List.replicate (n - l.length) a).set l.length b =
      (l ++ [b]) ++ List.replicate (n - (l ++ [b]).length) a := by
  obtain ⟨k, hk⟩ : ∃ k, n - l.length = k + 1 := ⟨n - l.length - 1, by omega⟩
  have hk' : n - (l ++ [b]).length = k := by simp; omega
  rw [hk, hk', List.replicate_succ, List.set_append_right _ _ (Nat.le_refl _)]
  simp

theorem setRepRep {α : Type} (a b : α) (m n : Nat) (h : m < n) :
    (List.replicate m b ++ List.replicate (n - m) a).set m b =
      List.replicate (m + 1) b ++ List.replicate (n - (m + 1)) a := by
  have := setAppRep (List.replicate m b) a b n (by simpa using h)
  simp only [List.length_replicate, List.length_append, List.length_singleton] at this
  rw [this, ← List.replicate_succ']

theorem setAppRep' {α : Type} (l : List α) (a b : α) (n i : Nat) (h : l.length < n)
    (hi : i = l.length) :
    (l ++ List.replicate (n - l.length) a).set i b =
      (l ++ [b]) ++ List.replicate (n - (l ++ [b]).length) a := by
  rw [hi]; exact setAppRep l a b n h

theorem setRepRep' {α : Type} (a b : α) (m n i : Nat) (h : m < n) (hi : i = m) :
    (List.replicate m b ++ List.replicate (n - m) a).set i b =
      List.replicate (m + 1) b ++ List.replicate (n - (m + 1)) a := by
  rw [hi]; exact setRepRep a b m n h

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]


/-- The handler's registrations, in `NewEPaxosRMWHandler`'s order: the channel field, the code
field, the registered object's type, the kind (`ρ.chans`' name). -/
def hKinds : List (GoString × GoString × go.GoType × String) :=
  [(go!"prepareChan", go!"prepareRPC", go.GoType.PointerType src.epaxosproto.Prepare.ty, "prepare"),
   (go!"prepareReplyChan", go!"prepareReplyRPC", go.GoType.PointerType src.gryffproto.PrepareReply.ty,
     "prepareReply"),
   (go!"preAcceptChan", go!"preAcceptRPC", go.GoType.PointerType src.gryffproto.PreAccept.ty,
     "preAccept"),
   (go!"preAcceptReplyChan", go!"preAcceptReplyRPC",
     go.GoType.PointerType src.gryffproto.PreAcceptReply.ty, "preAcceptReply"),
   (go!"preAcceptOKChan", go!"preAcceptOKRPC", go.GoType.PointerType src.epaxosproto.PreAcceptOK.ty,
     "preAcceptOK"),
   (go!"acceptChan", go!"acceptRPC", go.GoType.PointerType src.gryffproto.EAccept.ty, "accept"),
   (go!"acceptReplyChan", go!"acceptReplyRPC", go.GoType.PointerType src.epaxosproto.AcceptReply.ty,
     "acceptReply"),
   (go!"commitChan", go!"commitRPC", go.GoType.PointerType src.gryffproto.ECommit.ty, "commit"),
   (go!"commitShortChan", go!"commitShortRPC", go.GoType.PointerType src.epaxosproto.CommitShort.ty,
     "commitShort"),
   (go!"tryPreAcceptChan", go!"tryPreAcceptRPC",
     go.GoType.PointerType src.epaxosproto.TryPreAccept.ty, "tryPreAccept"),
   (go!"tryPreAcceptReplyChan", go!"tryPreAcceptReplyRPC",
     go.GoType.PointerType src.epaxosproto.TryPreAcceptReply.ty, "tryPreAcceptReply"),
   (go!"executedChan", go!"executedRPC", go.GoType.PointerType src.gryffproto.Executed.ty,
     "executed"),
   (go!"preAcceptOKReplyChan", go!"preAcceptOKReplyRPC",
     go.GoType.PointerType src.gryffproto.PreAcceptOKReply.ty, "preAcceptOKReply"),
   (go!"acceptOKReplyChan", go!"acceptOKReplyRPC",
     go.GoType.PointerType src.gryffproto.AcceptOKReply.ty, "acceptOKReply")]

/-- The registrations' entries (`genericBuilt`'s `regs`) from the codes, objects, channels. -/
def hRegs (es : List (w8 × Loc × Loc)) : List (w8 × GoInterface × Loc) :=
  (List.zip hKinds es).map fun ⟨k, c, o, ch⟩ => (c, interface.mkOk k.2.2.1 #o, ch)

/-- The empty search state. -/
def xs0 : XS := (([] : List (Int × Int)), (∅ : GMap (Int × Int) Nat), (∅ : GMap (Int × Int) Nat))

/-- One registration's resources after `NewEPaxosRMWHandler`: the channel field (a fresh
buffered channel, its names `γc`), the code field. -/
def hRegOwn (h : Loc) (k : GoString × GoString × go.GoType × String) (e : w8 × Loc × Loc)
    (γc : ChanNames) : IProp GF :=
  iprop(h.[src.gryff.EPaxosRMWHandler, k.1] ↦□ e.2.2 ∗ isChan e.2.2 γc GoInterface ∗
    ownChan γc GoInterface (ChanState.Buffered []) ∗ h.[src.gryff.EPaxosRMWHandler, k.2.1] ↦□ e.1)

/-- A raw fresh buffered channel of `*T` in field `f` of the handler. -/
def hChanRaw (h : Loc) (f : GoString) (γc : ChanNames) : IProp GF :=
  iprop(∃ ch : Loc, h.[src.gryff.EPaxosRMWHandler, f] ↦□ ch ∗ isChan ch γc Loc ∗
    ownChan γc Loc (ChanState.Buffered []))

/-- The `gryff` globals `NewEPaxosRMWHandler` writes or hands to the lock (`epaxosRest`'s, and
`bf_PT`), as `gryffGlobals` holds them. -/
def hGlobals : IProp GF :=
  iprop((∃ v : src.gryffproto.PreAccept, globalAddr src.gryff.pa ↦ v) ∗
    (∃ v : src.gryffproto.EAccept, globalAddr src.gryff.ea ↦ v) ∗
    (∃ v : src.gryffproto.ECommit, globalAddr src.gryff.ec ↦ v) ∗
    (∃ v : src.epaxosproto.CommitShort, globalAddr src.gryff.ecs ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.conflicted ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.happy ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.slow ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.weird ↦ v) ∗
    (∃ v : w64, globalAddr src.gryff.cpcounter ↦ v) ∗
    (∃ v : GoSlice, globalAddr src.gryff.cpMarker ↦ v))

/-- `netN.RegisterRPC_wp` with the length bound in the precondition. -/
theorem RegisterRPC_wp' (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) (obj : GoInterface)
    (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗
        netN.genericBuiltB gR id nodes regs cregs ∗ ⌜regs.length < 248⌝ }}
      (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"RegisterRPC"))
        (Val #obj)) (Val #ch))
    {{ (code : w8), RET #code; netN.genericBuiltB gR id nodes (regs ++ [(code, obj, ch)]) cregs ∗
        ⌜∀ c ∈ regs, c.1 ≠ code⌝ }} := by
  iintro %Φ ⟨#Hp, Hb, %hl⟩ HΦ
  iapply (netN.RegisterRPC_wp gR id nodes regs cregs obj ch hl) $$ [Hb] HΦ
  iframe; iframe #

/-- A fresh row of `nSlots` nil pointers: no instance (the empty pointer map). -/
theorem rowOwn_init (q : Nat) (sq : GoSlice) :
    sq ↦* List.replicate nSlots (zero_val Loc) ⊢ (rowOwn ∅ q sq : IProp GF) := by
  iintro H
  unfold rowOwn
  iexists _
  iframe
  ipureintro
  refine ⟨by simp, ?_⟩
  intro i p hp
  have : p = zero_val Loc := List.eq_of_mem_replicate (List.mem_of_getElem? hp)
  subst this
  simp [GMap.lookup]
  rfl

/-- An empty conflict table (`confRep`'s `none`). -/
theorem confRep_init (m : Loc) : m ↦$ (∅ : GMap w64 Loc) ⊢ (confRep m none : IProp GF) := by
  iintro H
  unfold confRep
  iexists ∅
  iframe
  ipureintro
  exact ⟨fun _ _ => rfl, rfl⟩

theorem exMap_init (c : Loc) : c ↦$ (∅ : GMap w64 w32) ⊢ (∃ m : GMap w64 w32, c ↦$ m : IProp GF) := by
  iintro H; iexists _; iexact H

theorem crt_init (kk : Nat) (q : Fin 3) : (sint.Z ((RState.init kk).crt (rid32 q))).toNat = 0 := by
  match q with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- `dlog.Printf(f, v)` (a no-op: `DLOG` is false). -/
theorem wp_dlog_Printf2 (f : GoString) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog ∗
        globalAddr gryff.src.dlog.DLOG ↦□ false }}
      (App (App (Val (@! gryff.src.dlog.Printf)) (Val #f)) (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hd
  wp_auto
  wp_end

variable [mathA : lib.MathPowHyp GF]

set_option maxHeartbeats 2000000 in
/-- **`NewEPaxosRMWHandler(r, false, false)`** (B-R7: the executor is started by the caller):
the handler at the initial model state (`epaxosOwn`, for any names whose pointer map and `crt`
lower bounds are the given fresh ones), its 14 registrations (fresh buffered channels, codes
`genericBuilt` gave), the executor's channels (raw), `ExecedUpTo` at `-1`, the fixed fields. -/
theorem NewEPaxosRMWHandler_wp (k : Fin 3) (r gR : Loc) (id : w64) (nodes : List GoString)
    (cregs : List (w8 × Loc)) (gp : GName) (gc : Fin 3 → GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
        genericBuilt gR id nodes [] cregs ∗
        ghostMapAuth gp 1 (∅ : GMap (Int × Int) Loc) ∗
        ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (gc q) 1 0) ∗
        hGlobals ∗ (∃ v : w32, globalAddr src.gryff.bf_PT ↦ v) }}
      (App (App (App (Val (@! src.gryff.NewEPaxosRMWHandler)) (Val #r)) (Val #false))
        (Val #false))
    {{ (h : Loc), RET #h; ∃ (ex : Loc) (euS : GoSlice) (es : List (w8 × Loc × Loc))
          (γs : List ChanNames) (γr γeo : ChanNames),
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
        h.[src.gryff.EPaxosRMWHandler, go!"exec"] ↦□ ex ∗ ex.[src.gryff.Exec, go!"r"] ↦□ h ∗
        h.[src.gryff.EPaxosRMWHandler, go!"broadcastOptimizationEnabled"] ↦□ false ∗
        ⌜es.length = 14 ∧ γs.length = 14⌝ ∗ genericBuilt gR id nodes (hRegs es) cregs ∗
        ([∗list] x ∈ List.zip hKinds (List.zip es γs), hRegOwn h x.1 x.2.1 x.2.2) ∗
        hChanRaw h go!"instancesToRecover" γr ∗ hChanRaw h go!"executeOverwriteChan" γeo ∗
        h.[src.gryff.EPaxosRMWHandler, go!"ExecedUpTo"] ↦□ euS ∗ euOwn euS [] ∗
        (∃ v : w32, globalAddr src.gryff.bf_PT ↦ v) ∗
        (∀ ρ : Repl2Names, ⌜ρ.ptrs = gp ∧ ρ.crt = gc⌝ -∗
          epaxosOwn ρ h r xs0 (RState.init k.val)) }} := by
  wp_start as ⟨#HgR, #HN, Hgb, Hptrs, Hcrt, Hglob, Hbf⟩
  iapply wp_fupd
  ihave #Hgsmr : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
  · iPkgInit
  ihave #Hdlp : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
  · iapply replica.dlog_init_access; iexact Hdlp
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c1 %γ1 ⟨#Hc1, -, Ho1⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c2 %γ2 ⟨#Hc2, -, Ho2⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c3 %γ3 ⟨#Hc3, -, Ho3⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c4 %γ4 ⟨#Hc4, -, Ho4⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c5 %γ5 ⟨#Hc5, -, Ho5⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c6 %γ6 ⟨#Hc6, -, Ho6⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 600000)) $$ [] as %c7 %γ7 ⟨#Hc7, -, Ho7⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 600000)) $$ [] as %c8 %γ8 ⟨#Hc8, -, Ho8⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 400000)) $$ [] as %c9 %γ9 ⟨#Hc9, -, Ho9⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c10 %γ10 ⟨#Hc10, -, Ho10⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c11 %γ11 ⟨#Hc11, -, Ho11⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c12 %γ12 ⟨#Hc12, -, Ho12⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c13 %γ13 ⟨#Hc13, -, Ho13⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 200000)) $$ [] as %c14 %γ14 ⟨#Hc14, -, Ho14⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := GoSlice) (W64 3)) as %ispS ⟨HispS, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 3)) as %crtS ⟨HcrtS, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 3)) as %euS ⟨HeuS, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) (W64 3)) as %c1S ⟨Hc1S, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) _ _) as %msR HmsR
  try wp_auto
  wp_apply (wp_slice_make2 (V := Loc) (W64 3)) as %cS ⟨HcS, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w32) _ _) as %mskR HmskR
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %crec %γr ⟨#Hcrec, -, Horec⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := src.gryffproto.ValTag) _ _) as %pvtR HpvtR
  try wp_auto
  wp_apply (wp_slice_make2 (V := GoSlice) (W64 3)) as %paoS ⟨HpaoS, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (wp_slice_make2 (V := GoSlice) (W64 3)) as %aoS ⟨HaoS, -⟩
  · ipureintro; decide
  try wp_auto
  wp_apply (chan.wp_make2 (V := Loc) (W64 200000)) $$ [] as %ceo %γeo ⟨#Hceo, -, Hoeo⟩
  · ipureintro; decide
  try wp_auto
  simp only [src.gryff.EPaxosRMWHandler.fieldsUnsealed, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  try wp_auto
  iStructNamedPrefix «$r0» "f"
  ipersist fR
  ipersist fprepareChan
  ipersist fpreAcceptChan
  ipersist facceptChan
  ipersist fcommitChan
  ipersist fcommitShortChan
  ipersist fprepareReplyChan
  ipersist fpreAcceptReplyChan
  ipersist fpreAcceptOKChan
  ipersist facceptReplyChan
  ipersist ftryPreAcceptChan
  ipersist ftryPreAcceptReplyChan
  ipersist fexecutedChan
  ipersist fpreAcceptOKReplyChan
  ipersist facceptOKReplyChan
  ipersist fInstanceSpace
  ipersist fcrtInstance
  ipersist fExecedUpTo
  ipersist fconflicts1
  ipersist fmaxSeqPerKey1
  ipersist fconflicts
  ipersist fmaxSeqPerKey
  ipersist finstancesToRecover
  ipersist fnoConflicts
  ipersist fPrevValTag
  ipersist fpreAcceptOKs
  ipersist facceptOKs
  ipersist fexecuteOverwriteChan
  ipersist fbroadcastOptimizationEnabled
  -- the slices' lengths
  ihave %HLisp := ownSlice_len _ _ _ $$ HispS
  ihave %HLcrt := ownSlice_len _ _ _ $$ HcrtS
  ihave %HLeu := ownSlice_len _ _ _ $$ HeuS
  ihave %HLc1 := ownSlice_len _ _ _ $$ Hc1S
  ihave %HLc := ownSlice_len _ _ _ $$ HcS
  ihave %HLpao := ownSlice_len _ _ _ $$ HpaoS
  ihave %HLao := ownSlice_len _ _ _ $$ HaoS
  simp only [List.length_replicate] at HLisp HLcrt HLeu HLc1 HLc HLpao HLao
  have e3 : sint.nat (W64 3) = 3 := by decide
  have hL : ∀ s : GoSlice, 3 = sint.nat s.len → 0 ≤ sint.Z s.len → sint.Z s.len = 3 := by
    intro s h1 h2; have : (sint.nat s.len : Int) = sint.Z s.len := Int.toNat_of_nonneg h2
    omega
  have lisp := hL _ (e3 ▸ HLisp.1) HLisp.2
  have lcrt := hL _ (e3 ▸ HLcrt.1) HLcrt.2
  have leu := hL _ (e3 ▸ HLeu.1) HLeu.2
  have lc1 := hL _ (e3 ▸ HLc1.1) HLc1.2
  have lc := hL _ (e3 ▸ HLc.1) HLc.2
  have lpao := hL _ (e3 ▸ HLpao.1) HLpao.2
  have lao := hL _ (e3 ▸ HLao.1) HLao.2
  -- the rows loop
  ihave IH : iprop(∃ (j : w64) (isp : List GoSlice) (c1s cs : List Loc) (l1 l2 : List GoSlice),
      "i" ∷ i_ptr ↦ j ∗
      "HispS" ∷ ispS ↦* (isp ++ List.replicate (3 - isp.length) (zero_val GoSlice)) ∗
      "Hrows" ∷ ([∗list] sq ∈ isp, sq ↦* List.replicate nSlots (zero_val Loc)) ∗
      "HcrtS" ∷ crtS ↦* List.replicate 3 (W32 0) ∗
      "HeuS" ∷ euS ↦* (List.replicate isp.length (W32 (-1)) ++
        List.replicate (3 - isp.length) (W32 0)) ∗
      "Hc1S" ∷ c1S ↦* (c1s ++ List.replicate (3 - c1s.length) (zero_val Loc)) ∗
      "Hc1s" ∷ ([∗list] m ∈ c1s, m ↦$ (∅ : GMap w64 Loc)) ∗
      "HcS" ∷ cS ↦* (cs ++ List.replicate (3 - cs.length) (zero_val Loc)) ∗
      "Hcs" ∷ ([∗list] m ∈ cs, m ↦$ (∅ : GMap w64 w32)) ∗
      "HpaoS" ∷ paoS ↦* l1 ∗ "HaoS" ∷ aoS ↦* l2 ∗
      "%Hj" ∷ ⌜sint.Z j = isp.length ∧ c1s.length = isp.length ∧ cs.length = isp.length ∧
        isp.length ≤ 3 ∧ l1.length = 3 ∧ l2.length = 3⌝) $$ [i HispS HcrtS HeuS Hc1S HcS HpaoS HaoS]
  · iexists _, [], [], [], _, _
    simp only [List.length_nil, List.nil_append, Nat.sub_zero, List.replicate_zero]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for IH
  wp_if_destruct
  · try wp_auto
    have hj3 : isp.length < 3 := by
      have : sint.Z (W64 3) = 3 := by decide
      omega
    wp_apply (wp_slice_make2 (V := Loc) (W64 2097152)) as %sq ⟨Hsq, -⟩
    · ipureintro; decide
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [lisp]; omega⟩]
    wp_apply wp_store_slice_index ispS (sint.Z j) _ sq $$ [HispS] as HispS
    · iframe; ipureintro; simp; omega
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [lcrt]; omega⟩]
    wp_apply wp_store_slice_index crtS (sint.Z j) _ (W32 0) $$ [HcrtS] as HcrtS
    · iframe; ipureintro; simp; omega
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [leu]; omega⟩]
    wp_apply wp_store_slice_index euS (sint.Z j) _ (W32 (-1)) $$ [HeuS] as HeuS
    · iframe; ipureintro; simp; omega
    try wp_auto
    wp_apply (wp_map_make2 (K := w64) (V := Loc) _ _ _) as %m1 Hm1
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [lc1]; omega⟩]
    wp_apply wp_store_slice_index c1S (sint.Z j) _ m1 $$ [Hc1S] as Hc1S
    · iframe; ipureintro; simp; omega
    try wp_auto
    wp_apply (wp_map_make2 (K := w64) (V := w32) _ _ _) as %m2 Hm2
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [lc]; omega⟩]
    wp_apply wp_store_slice_index cS (sint.Z j) _ m2 $$ [HcS] as HcS
    · iframe; ipureintro; simp; omega
    try wp_auto
    wp_apply (wp_slice_make2 (V := w64) (W64 2097152)) as %s1 ⟨-, -⟩
    · ipureintro; decide
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [lpao]; omega⟩]
    wp_apply wp_store_slice_index paoS (sint.Z j) _ s1 $$ [HpaoS] as HpaoS
    · iframe; ipureintro; omega
    try wp_auto
    wp_apply (wp_slice_make2 (V := w64) (W64 2097152)) as %s2 ⟨-, -⟩
    · ipureintro; decide
    try wp_auto
    rw [if_pos ⟨Hj.1 ▸ by omega, by rw [lao]; omega⟩]
    wp_apply wp_store_slice_index aoS (sint.Z j) _ s2 $$ [HaoS] as HaoS
    · iframe; ipureintro; omega
    rw [setAppRep' isp _ sq 3 _ hj3 (by omega), setAppRep' c1s _ m1 3 _ (by omega) (by omega),
      setAppRep' cs _ m2 3 _ (by omega) (by omega), List.set_replicate_self,
      setRepRep' _ _ _ 3 _ hj3 (by omega)]
    wp_for_post
    iframe
    iexists _, isp ++ [sq], c1s ++ [m1], cs ++ [m2], _, _
    simp only [List.length_append, List.length_singleton]
    iframe i HispS HcrtS HeuS Hc1S HcS HpaoS HaoS
    isplitl [Hrows Hsq]
    · iapply BigSepL.bigSepL_snoc.2; iframe Hrows; rw [show nSlots = 2097152 from rfl]; iexact Hsq
    isplitl [Hc1s Hm1]
    · iapply BigSepL.bigSepL_snoc.2; iframe
    isplitl [Hcs Hm2]
    · iapply BigSepL.bigSepL_snoc.2; iframe
    ipureintro
    simp only [List.length_set]
    refine ⟨?_, by omega, by omega, by omega, Hj.2.2.2.2.1, Hj.2.2.2.2.2⟩
    have : sint.Z j < 3 := by omega
    have h1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
    omega
  have hisp3 : isp.length = 3 := by
    have : sint.Z (W64 3) = 3 := by decide
    omega
  icases Hbf with ⟨%bv, Hbf⟩
  iunfold hGlobals at Hglob
  icases Hglob with ⟨Hpa, Hea, Hec, Hecs, Hcon, Hhap, Hslow, Hweird, Hcpc, ⟨%cpm, Hcpm⟩⟩
  try wp_auto
  ihave IHb : iprop(∃ v : w32, "Hbf" ∷ globalAddr src.gryff.bf_PT ↦ v) $$ [Hbf]
  · iexists _; iframe
  wp_for IHb
  wp_apply (lib.MathPowHyp.pow (GF := GF)) as %pw -
  try wp_auto
  try simp only [src.gryff.MAX_BATCH_F, src.gryff.BF_M_N]
  try wp_auto
  wp_apply wp_float64_div as %fd -
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_for_post
    iframe
    iexists _; iframe
  rw [if_pos (by
    revert Hif
    generalize (float64Leb fd (W64 4629700416936869888) &&
      !float64Eq fd (W64 4629700416936869888)) = bb
    cases bb <;> simp)]
  try wp_auto
  wp_apply (wp_slice_make2 (V := src.state.Command) (W64 0)) as %cpS ⟨-, -⟩
  · ipureintro; decide
  try wp_auto
  wp_alloc o1 as Hob1
  wp_auto
  wp_method_call; wp_call
  wp_auto
  iunfold genericBuilt at Hgb
  wp_apply (RegisterRPC_wp' gR id nodes [] cregs _ c1) $$ [Hgb] as %cd1 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o2 as Hob2
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c6) $$ [Hgb] as %cd2 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o3 as Hob3
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c2) $$ [Hgb] as %cd3 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o4 as Hob4
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c7) $$ [Hgb] as %cd4 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o5 as Hob5
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c8) $$ [Hgb] as %cd5 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o6 as Hob6
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c3) $$ [Hgb] as %cd6 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o7 as Hob7
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c9) $$ [Hgb] as %cd7 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o8 as Hob8
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c4) $$ [Hgb] as %cd8 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o9 as Hob9
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c5) $$ [Hgb] as %cd9 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o10 as Hob10
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c10) $$ [Hgb] as %cd10 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o11 as Hob11
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c11) $$ [Hgb] as %cd11 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o12 as Hob12
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c12) $$ [Hgb] as %cd12 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o13 as Hob13
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c13) $$ [Hgb] as %cd13 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_alloc o14 as Hob14
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply (RegisterRPC_wp' gR id nodes _ cregs _ c14) $$ [Hgb] as %cd14 ⟨Hgb, -⟩
  · iframe; ipureintro; simp
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf2 $$ []
  · iframe #
  try wp_auto
  iStructNamedPrefix «$r0» "x"
  ipersist xr
  ipersist fexec
  ipersist fprepareRPC
  ipersist fprepareReplyRPC
  ipersist fpreAcceptRPC
  ipersist fpreAcceptReplyRPC
  ipersist fpreAcceptOKRPC
  ipersist facceptRPC
  ipersist facceptReplyRPC
  ipersist fcommitRPC
  ipersist fcommitShortRPC
  ipersist ftryPreAcceptRPC
  ipersist ftryPreAcceptReplyRPC
  ipersist fexecutedRPC
  ipersist fpreAcceptOKReplyRPC
  ipersist facceptOKReplyRPC
  have hisp' : isp = isp ++ List.replicate (3 - isp.length) (zero_val GoSlice) := by
    rw [hisp3]; simp
  have hc1' : c1s.length = 3 := by omega
  have hcs' : cs.length = 3 := by omega
  rw [hisp3, hc1', hcs']
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  ipersist HispS
  ipersist Hc1S
  ipersist HcS
  imodintro
  iapply HΦ
  iexists _, euS, [(cd1, o1, c1), (cd2, o2, c6), (cd3, o3, c2), (cd4, o4, c7), (cd5, o5, c8), (cd6, o6, c3), (cd7, o7, c9), (cd8, o8, c4), (cd9, o9, c5), (cd10, o10, c10), (cd11, o11, c11), (cd12, o12, c12), (cd13, o13, c13), (cd14, o14, c14)], [γ1, γ6, γ2, γ7, γ8, γ3, γ9, γ4, γ5, γ10, γ11, γ12, γ13, γ14], γr, γeo
  iframe #
  isplitr
  · ipureintro; simp
  isplitl [Hgb]
  · iunfold genericBuilt
    simp only [hRegs, hKinds, List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append]
    iexact Hgb
  isplitl [Ho1 Ho2 Ho3 Ho4 Ho5 Ho6 Ho7 Ho8 Ho9 Ho10 Ho11 Ho12 Ho13 Ho14]
  · simp only [hKinds, List.zip_cons_cons, List.zip_nil_right, BigSepL.bigSepL_cons,
      BigSepL.bigSepL_nil, hRegOwn]
    iframe
    iframe #
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Horec]
  · iunfold hChanRaw; iexists crec; iframe; iframe #
  isplitl [Hoeo]
  · iunfold hChanRaw; iexists ceo; iframe; iframe #
  isplitl [HeuS]
  · unfold euOwn; iexists _; iframe
    ipureintro
    refine ⟨by simp, ?_⟩
    intro q e he
    have hm : e ∈ List.replicate 3 (W32 (-1)) := List.mem_of_getElem? he
    rw [List.eq_of_mem_replicate hm]
    have h1 : sint.Z (W32 (-1)) = -1 := by decide
    rw [h1]
    exact ⟨Int.le_refl _, fun i hi hi' => by omega⟩
  isplitl [Hbf]
  · iexists _; iframe
  iintro %ρ %hρ
  obtain ⟨hp, hc⟩ := hρ
  unfold epaxosOwn
  iexists ispS, crtS, c1S, isp, msR, pvtR, c1s, ∅, _, ∅
  rw [hp, hc]
  iframe #
  iframe
  isplitr
  · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitl [Hrows]
  · iapply BigSepL.bigSepL_mono (fun _ => rowOwn_init _ _) $$ Hrows
  isplitr
  · iapply BigSepM.bigSepM_empty.2; iempintro
  isplitl [Hcrt]
  · simp only [crt_init]; iexact Hcrt
  isplitl [Hc1s]
  · have hcf : ∀ (kk q : Nat), (RState.init kk).confAt q = none := by
      intro kk q; unfold RState.confAt; simp only [RState.init]
      rcases q with _ | _ | _ | q <;> simp
    simp only [hcf]
    iapply BigSepL.bigSepL_mono (fun _ => confRep_init _) $$ Hc1s
  isplitl [HmsR]
  · rw [show ∀ kk, (RState.init kk).maxSeqK0 = none from fun _ => rfl]
    iapply confRep_init $$ HmsR
  isplitl
  · unfold epaxosRest
    iexists W32 0, W32 0, W32 (-1), cS, cs, mskR, ∅
    iframe
    iframe #
    iapply BigSepL.bigSepL_mono (fun _ => exMap_init _) $$ Hcs
  ipureintro
  refine ⟨hisp3, hc1', rfl, rfl, fun _ _ => rfl, rfl, fun q i _ => rfl, fun q i _ => rfl, ?_, ?_, rfl⟩
  · intro n hn; simp [xs0, XS.numF, XS.lowF] at hn
  · intro n hn; simp [xs0, XS.numF, XS.lowF] at hn

end

end Perennial.gryff.unitB
