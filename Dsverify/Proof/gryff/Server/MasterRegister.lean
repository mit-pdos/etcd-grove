/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/MasterRegister.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).
-/
module

public import Dsverify.Proof.gryff.Server.MasterDefs
public import Dsverify.Proof.gryff.Server.LogErr
public import Dsverify.Proof.gryff.src.masterlib.Base
public import Dsverify.Proof.gryff.examples.gryffnet.Base
public import Dsverify.GeneratedProof.gryff.src.masterlib
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net fmt

attribute [local instance] GooseGlobalGS.gooseInvGS

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

theorem intArg_int_uniq (n : w64) (z : Int) (h : IntArgValue (interface.mk go.int #n) z) :
    z = sint.Z n := by
  obtain ⟨n', hv, rfl⟩ := IntArgValue.of_int h
  rw [go.intoVal_inj hv.symm]

/-- The master's `Sprintf("%s:%d", addr, port)` of replica node `k`'s arguments. -/
theorem sprintf_addr (k : Nat) (hk : k < 3) (s : GoString)
    (h : SprintfOut go!"%s:%d"
      [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #(portNum k)] s) :
    s = addrOf k := by
  have hf : go!"%s:%d" = W8 37 :: W8 115 :: go!":%d" := rfl
  rw [hf] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.byte_inv (by decide) h1
  have hp : parseIntVerb go!"d" = some (0, []) := by decide
  obtain ⟨o3, rfl, h3⟩ := SprintfOut.int_inv hp (IntArgValue.int (portNum k))
    (fun z' hz' => intArg_int_uniq _ _ hz') h2
  rw [SprintfOut.done_inv h3]
  have hz : sint.Z (portNum k) = 7502 + k := by unfold portNum; word
  rw [hz]
  rcases k with _|_|_|k
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, ipOf, addrOf, portAddr]; try rfl
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, ipOf, addrOf, portAddr]; try rfl
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, ipOf, addrOf, portAddr]; try rfl
  · omega

theorem bval_true {P : Prop} [Decidable P] (h : (#(decide P) : val) = #true) : P :=
  of_decide_eq_true (GoGlobalContext.intoVal_inj_bool h)

theorem bval_false {P : Prop} [Decidable P] (h : ¬ (#(decide P) : val) = #true) : ¬ P :=
  fun hp => h (by rw [decide_eq_true hp])

theorem bval_ff : decide ((#false : val) = #false) = true := decide_eq_true rfl

theorem regArgs_argsWf (k : Nat) :
    ArgsWf [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #(portNum k)] :=
  .cons_string _ _ (.cons_int _ _ _ (.int (portNum k)) .nil)

theorem list_set_snoc {A : Type} (l : List A) (x y : A) (n : Nat) (h : n = l.length) :
    (l ++ [x]).set n y = l ++ [y] := by
  subst h; simp

/-- Reslicing `s[0 : len(s)+1]` within its capacity: one more element (of the capacity's
value). -/
theorem ownSlice_extend1 {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (vs : List V) (n : w64) (hn : s.len = n) (h : sint.Z s.len < sint.Z s.cap) :
    (s ↦* vs ∗ ownSliceCap V s (DFrac.own 1) : IProp GF) ⊢
      ∃ x : V, slice.slice s V (W64 0) (n + W64 1) ↦* (vs ++ [x]) ∗
        ownSliceCap V (slice.slice s V (W64 0) (n + W64 1)) (DFrac.own 1) := by
  subst hn
  iintro ⟨Hs, Hc⟩
  ihave %Hl := ownSlice_len $$ Hs
  ihave %Hw := ownSliceCap_wf $$ Hc
  icases ownSlice_slice_into_capacity (W64 0) (s.len + W64 1) s vs $$ [Hs Hc]
    with ⟨%vc, -, Hs', Hc'⟩
  · iframe; ipureintro; refine ⟨by decide, by word, by word, by word⟩
  ihave %Hl' := ownSlice_len $$ Hs'
  have hz : sint.nat (W64 0) = 0 := rfl
  rw [hz, List.drop_zero] at Hl' ⊢
  obtain ⟨x, rfl⟩ : ∃ x, vc = [x] := by
    have : vc.length = 1 := by
      simp only [List.length_append, slice.slice] at Hl'
      have h1 : sint.nat (s.len + W64 1 - W64 0) = sint.nat s.len + 1 := by word
      rw [h1, Hl.1] at Hl'; omega
    match vc, this with
    | [x], _ => exact ⟨x, rfl⟩
  iexists x
  iframe

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [sem : go.Semantics]

/-- `*masterproto.RegisterArgs` `p` holds `{addr, port}` (fraction `dq`). -/
def regArgsPt (p : Loc) (dq : DFrac) (addr : GoString) (port : w64) : IProp GF :=
  iprop(structFieldRef src.masterproto.RegisterArgs go!"Addr" p ↦{dq} addr ∗
    structFieldRef src.masterproto.RegisterArgs go!"Port" p ↦{dq} port)

/-- `*masterproto.RegisterReply` `p` holds `{id, nl, rd}`. -/
def regReplyPt (p : Loc) (id : w64) (nl : GoSlice) (rd : Bool) : IProp GF :=
  iprop(structFieldRef src.masterproto.RegisterReply go!"ReplicaId" p ↦ id ∗
    structFieldRef src.masterproto.RegisterReply go!"NodeList" p ↦ nl ∗
    structFieldRef src.masterproto.RegisterReply go!"Ready" p ↦ rd)

end proof

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [pA : gryff.src.masterlib.Assumptions]

set_option goose.wp.extras true

theorem wp_Master_Register (γ : GryffNames GF) (m ap rp : Loc) (k : Nat) (hk : k < 3) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗ masterReg γ m ∗
        regCarry γ.proto k ∗
        regArgsPt ap (DFrac.own 1) (ipOf k) (portNum k) ∗ regReplyPt rp (W64 0) slice.nil false }}
      (App (App (Val (m @!! go.GoType.PointerType gryff.src.masterlib.Master.ty @!!
          go!"Register")) (Val #ap)) (Val #rp))
    {{ RET #interface.nil; ∃ (id : w64) (nl : GoSlice) (rd : Bool) (nodes : List GoString)
        (dq : DFrac), regReplyPt rp id nl rd ∗ nl ↦*{dq} nodes ∗
        ((⌜id = W64 0 ∧ nodes = [] ∧ rd = false⌝) ∨
          (⌜rd = true⌝ ∗ regReady γ.deploy k id nodes)) }} := by
  wp_start as ⟨#Hm, #Hcar, Hargs, Hrep⟩
  unfold masterReg
  iNamed Hm
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  unfold masterLockInv
  iNamed Hinv
  unfold regArgsPt regReplyPt
  icases Hargs with ⟨Haddr, Hport⟩
  icases Hrep with ⟨Hid, HnlR, Hrd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #(portNum k)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %psl ⟨Hpsl, -⟩
  wp_apply log.wp_Printf_logArg _ _
    [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #(portNum k)] _ $$ [Hpsl]
  · iframe Hpsl
    iintro !>
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply logArg_string
    iapply BigSepL.bigSepL_singleton.2
    iapply logArg_wf
    intro ii h
    exact fmt.ArgsWf.cons_int _ _ _ (.int (portNum k)) .nil ii (List.mem_singleton.2 (by rw [← h]))
  iintro -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #(portNum k)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %ssl ⟨Hssl, -⟩
  wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (regArgs_argsWf k) $$ [Hssl] as %s ⟨-, %Hs⟩
  · iframe
  rw [sprintf_addr k hk s Hs]
  rename_i ig_ptr
  irename : (ig_ptr ↦ zero_val w64 : IProp GF) => ig
  ihave %Hnllen := ownSlice_len $$ Hnl
  wp_join iprop(∃ idx : w64, "index" ∷ index_ptr ↦ idx ∗
      "addrPort" ∷ addrPort_ptr ↦ addrOf k ∗
      "Hnl" ∷ nl ↦*{dqOf ks} (ks.map addrOf) ∗
      "%Hidx" ∷ ⌜(addrOf k ∈ ks.map addrOf → (ks.map addrOf)[sint.nat idx]? = some (addrOf k) ∧
          0 ≤ sint.Z idx) ∧ (addrOf k ∉ ks.map addrOf → idx = nl.len)⌝) at next
    with [i ig ap index Hnl addrPort] as ⟨%idx, index, addrPort, Hnl, %Hidx⟩
  · ihave IH : iprop(∃ (j iv : w64) (apv : GoString),
        "i" ∷ i_ptr ↦ j ∗ "ig" ∷ ig_ptr ↦ iv ∗ "ap" ∷ ap_ptr ↦ apv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nl.len ∧
          ∀ t, t < sint.nat j → (ks.map addrOf)[t]? ≠ some (addrOf k)⌝) $$ [i ig ap]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro t ht; simp at ht; omega
    wp_for IH
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < (ks.map addrOf).length := by word
      obtain ⟨x, Hx⟩ : ∃ x, (ks.map addrOf)[(sint.Z j).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nl.len from ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index nl (sint.Z j) _ (dqOf ks) x Hj.1 $$ [Hnl] as Hnl
      · iframe; ipureintro; exact Hx
      wp_if_destruct
      · wp_for_post
        isplitr
        · ipureintro; rfl
        iexists j
        iframe
        ipureintro
        constructor
        · intro _; exact ⟨Hx, Hj.1⟩
        · intro hn; exact absurd (List.mem_of_getElem? Hx) hn
      · wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro t ht
        have hsucc : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rw [hsucc] at ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
        · exact Hj.2.2 t ht
        · intro h; rw [show sint.nat j = (sint.Z j).toNat from rfl, Hx] at h
          exact Hif (Option.some.inj h).symm
    · isplitr
      · itrivial
      iexists nl.len
      iframe
      ipureintro
      constructor
      · intro hm
        exfalso
        obtain ⟨t, ht, hte⟩ := List.getElem_of_mem hm
        exact Hj.2.2 t (by word) (by rw [List.getElem?_eq_getElem ht, hte])
      · intro _; rfl
  ihave %Hallen := ownSlice_len $$ Hal
  ihave %Hpllen := ownSlice_len $$ Hpl
  have hnlZ : sint.Z nl.len = ks.length := by
    have h := Hnllen; simp only [List.length_map] at h; word
  have halZ : sint.Z al.len = ks.length := by
    have h := Hallen; simp only [List.length_map] at h; word
  have hplZ : sint.Z pl.len = ks.length := by
    have h := Hpllen; simp only [List.length_map] at h; word
  wp_join iprop(∃ (ks' : List Nat) (nl' al' pl' : GoSlice) (idx' nv : w64),
      "nlen" ∷ nlen_ptr ↦ nv ∗ "index" ∷ index_ptr ↦ idx' ∗
      "master" ∷ master_ptr ↦ m ∗
      "Hnlf" ∷ structFieldRef gryff.src.masterlib.Master go!"nodeList" m ↦{dqOf ks'} nl' ∗
      "Half" ∷ structFieldRef gryff.src.masterlib.Master go!"addrList" m ↦{dqOf ks'} al' ∗
      "Hplf" ∷ structFieldRef gryff.src.masterlib.Master go!"portList" m ↦{dqOf ks'} pl' ∗
      "Hnl" ∷ nl' ↦*{dqOf ks'} (ks'.map addrOf) ∗
      "Hal" ∷ al' ↦*{dqOf ks'} (ks'.map ipOf) ∗
      "Hpl" ∷ pl' ↦*{dqOf ks'} (ks'.map portNum) ∗
      "Hcap" ∷ capOwn ks' nl' al' pl' ∗
      "Hreg" ∷ regAuth γ.deploy (1 : Qp).half (ks'.map addrOf) ∗
      "%Hks'" ∷ ⌜ks'.Nodup ∧ (∀ x ∈ ks', x < 3) ∧ sint.Z nl'.cap = 3 ∧ sint.Z al'.cap = 3 ∧
        sint.Z pl'.cap = 3 ∧ ks'[sint.nat idx']? = some k ∧ 0 ≤ sint.Z idx' ∧
        sint.Z nv = ks'.length⌝) at next
    with [nlen index master args Hnlf Half Hplf Hnl Hal Hpl Hcap Hreg Haddr Hport addrPort]
    as ⟨%ks', %nl', %al', %pl', %idx', %nv, nlen, index, master, Hnlf, Half, Hplf, Hnl, Hal, Hpl, Hcap, Hreg,
      %Hks'⟩
  · wp_if_destruct
    · -- not registered yet: append
      have hkn : k ∉ ks := by
        intro hm
        have := (Hidx.1 (List.mem_map_of_mem hm)).1
        rw [List.getElem?_eq_none (by rw [Hnllen.1]; exact Nat.le_refl _)] at this
        cases this
      have hlen3 : ks.length < 3 := by
        have := nodup_bound_length (ks := k :: ks) (List.nodup_cons.mpr ⟨hkn, Hks.1⟩)
          (by intro x hx; simp at hx; rcases hx with rfl | hx; exact hk; exact Hks.2.1 x hx)
        simp at this; omega
      rw [dqOf_open ks (by omega)]
      icases (capOwn_open ks nl al pl (by omega)).1 $$ Hcap with ⟨Hcnl, Hcal, Hcpl⟩
      rw [if_pos (by refine ⟨by decide, by word, by word⟩)]
      wp_auto
      icases ownSlice_extend1 nl _ nl.len rfl (by word) $$ [Hnl Hcnl] with ⟨%x1, Hnl, Hcnl⟩
      · iframe
      rw [if_pos (by refine ⟨by word, by word⟩)]
      wp_apply wp_store_slice_index _ (sint.Z nl.len) _ (addrOf k) $$ [Hnl] as Hnl
      · iframe; ipureintro; simp; word
      rw [list_set_snoc _ _ _ _ (by simp; word)]
      rw [if_pos (by refine ⟨by decide, by word, by word⟩)]
      wp_auto
      icases ownSlice_extend1 al _ nl.len (by word) (by word) $$ [Hal Hcal] with ⟨%x2, Hal, Hcal⟩
      · iframe
      rw [if_pos (by refine ⟨by word, by word⟩)]
      wp_apply wp_store_slice_index _ (sint.Z nl.len) _ (ipOf k) $$ [Hal] as Hal
      · iframe; ipureintro; simp; word
      rw [list_set_snoc _ _ _ _ (by simp; word)]
      rw [if_pos (by refine ⟨by decide, by word, by word⟩)]
      wp_auto
      icases ownSlice_extend1 pl _ nl.len (by word) (by word) $$ [Hpl Hcpl] with ⟨%x3, Hpl, Hcpl⟩
      · iframe
      rw [if_pos (by refine ⟨by word, by word⟩)]
      wp_apply +noauto wp_store_slice_index _ (sint.Z nl.len) _ (portNum k) $$ [Hpl] as Hpl
      · iframe; ipureintro; simp; word
      rw [list_set_snoc _ _ _ _ (by simp; word)]
      iapply fupd_wp
      unfold regCarry
      icases Hcar with ⟨%ws, #Hcar⟩
      imod deploy_register γ.deploy γ.proto ks k ws hk Hks.2.1 hkn ⊤ (by simp) gryffN_sub_top_deployN
        $$ [Hdep Hg Hcar Hreg] with Hreg
      · iframe Hreg; iframe #
      have hfacts : (ks ++ [k]).Nodup ∧ (∀ x ∈ ks ++ [k], x < 3) := by
        refine ⟨List.nodup_append.mpr ⟨Hks.1, by simp, ?_⟩, ?_⟩
        · intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb
          intro h; subst h; exact hkn ha
        · intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact Hks.2.1 x hx
          · exact hk
      have hnln : sint.nat nl.len = ks.length := by word
      have hidx : (ks ++ [k])[sint.nat nl.len]? = some k := by
        rw [hnln, List.getElem?_append_right (Nat.le_refl _)]
        simp
      by_cases hfull : ks.length + 1 = 3
      · ipersist Hnlf
        ipersist Half
        ipersist Hplf
        ipersist Hnl
        ipersist Hal
        ipersist Hpl
        imodintro
        wp_auto
        isplitr
        · ipureintro; rfl
        iexists ks ++ [k], (slice.slice nl GoString (W64 0) (nl.len + W64 1)),
          (slice.slice al GoString (W64 0) (nl.len + W64 1)),
          (slice.slice pl w64 (W64 0) (nl.len + W64 1)), nl.len, (nl.len + W64 1)
        rw [dqOf_full (ks ++ [k]) (by simp; omega)]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        iframe #
        isplitr
        · iapply capOwn_full; simp; omega
        ipureintro
        have hc := Hks.2.2
        refine ⟨hfacts.1, hfacts.2, ?_, ?_, ?_, hidx, by word, ?_⟩
        · simp only [slice.slice]; word
        · simp only [slice.slice]; word
        · simp only [slice.slice]; word
        · simp only [List.length_append, List.length_singleton]; word
      · imodintro
        wp_auto
        isplitr
        · ipureintro; rfl
        iexists ks ++ [k], (slice.slice nl GoString (W64 0) (nl.len + W64 1)),
          (slice.slice al GoString (W64 0) (nl.len + W64 1)),
          (slice.slice pl w64 (W64 0) (nl.len + W64 1)), nl.len, (nl.len + W64 1)
        rw [dqOf_open (ks ++ [k]) (by simp; omega)]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iframe
        isplitl [Hcnl Hcal Hcpl]
        · iapply (capOwn_open _ _ _ _ (by simp; omega)).2; iframe
        ipureintro
        have hc := Hks.2.2
        refine ⟨hfacts.1, hfacts.2, ?_, ?_, ?_, hidx, by word, ?_⟩
        · simp only [slice.slice]; word
        · simp only [slice.slice]; word
        · simp only [slice.slice]; word
        · simp only [List.length_append, List.length_singleton]; word
    · -- already registered
      have hmem : addrOf k ∈ ks.map addrOf :=
        Classical.byContradiction (fun hn => Hif (Hidx.2 hn))
      obtain ⟨hget, hidx0⟩ := Hidx.1 hmem
      rw [List.getElem?_map] at hget
      obtain ⟨k', hk', hak⟩ : ∃ k', ks[sint.nat idx]? = some k' ∧ addrOf k' = addrOf k := by
        rcases h : ks[sint.nat idx]? with _ | k'
        · rw [h] at hget; simp at hget
        · rw [h] at hget; simp only [Option.map_some, Option.some.injEq] at hget
          exact ⟨k', rfl, hget⟩
      have hkk := addrOf_inj (Hks.2.1 k' (List.mem_of_getElem? hk')) hk hak
      subst hkk
      isplitr
      · itrivial
      iexists ks, nl, al, pl, idx, nl.len
      iframe
      ipureintro
      exact ⟨Hks.1, Hks.2.1, Hks.2.2.1, Hks.2.2.2.1, Hks.2.2.2.2, hk', hidx0, hnlZ⟩
  wp_if_destruct
  · -- all three registered: `Ready`
    have hfull : ks'.length = 3 := by have := Hks'.2.2.2.2.2.2.2; word
    rw [dqOf_full ks' hfull]
    icases Hnlf with #Hnlf
    icases Half with #Half
    icases Hplf with #Hplf
    icases Hnl with #Hnl
    icases Hal with #Hal
    icases Hpl with #Hpl
    iapply fupd_wp
    imod deploy_lb γ.deploy γ.proto (ks'.map addrOf) ⊤ (by simp) $$ [Hdep Hreg] with ⟨Hreg, #Hlb⟩
    · iframe Hdep Hreg
    imodintro
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hreg Hcap]
    · iexists ks', nl', al', pl'
      rw [dqOf_full ks' hfull]
      iframe
      iframe #
      ipureintro
      exact ⟨Hks'.1, Hks'.2.1, Hks'.2.2.1, Hks'.2.2.2.1, Hks'.2.2.2.2.1⟩
    iapply HΦ
    iexists idx', nl', true, ks'.map addrOf, DFrac.discard
    iframe
    iframe #
    iright
    isplitr
    · ipureintro; rfl
    unfold regReady
    isplitr
    · iexact Hlb
    ipureintro
    constructor
    · exact (nodup_bound_perm Hks'.1 Hks'.2.1 hfull).map addrOf
    · rw [List.getElem?_map, show uint.nat idx' = sint.nat idx' by word, Hks'.2.2.2.2.2.1]
      rfl
  · -- not all registered yet
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnlf Half Hplf Hnl Hal Hpl Hreg Hcap]
    · iexists ks', nl', al', pl'
      iframe
      ipureintro
      exact ⟨Hks'.1, Hks'.2.1, Hks'.2.2.1, Hks'.2.2.2.1, Hks'.2.2.2.2.1⟩
    iapply HΦ
    iexists (W64 0), slice.nil, false, [], DFrac.discard
    iframe
    isplitr
    · iapply ownSlice_nil
    ileft
    ipureintro
    exact ⟨rfl, rfl, rfl⟩

end proof



section rcvr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [pA : gryff.src.masterlib.Assumptions] [kA : examples.gryffnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions]

set_option goose.wp.extras true

theorem regArgs_zero_pt (p : Loc) :
    (p ↦ zero_val src.masterproto.RegisterArgs : IProp GF) ⊢
      p ↦ src.masterproto.RegisterArgs.mk go!"" (W64 0) := by
  rfl

theorem regReply_zero_pt (p : Loc) :
    (p ↦ zero_val src.masterproto.RegisterReply : IProp GF) ⊢
      p ↦ src.masterproto.RegisterReply.mk (W64 0) slice.nil false := by
  rfl

/-- What a `Register` deposit says of its arguments: replica node `k`'s. -/
theorem masterSvc_shape (δ : DeployNames) (R : Nat → IProp GF) (args : List w8)
    (Φ : List w8 → GoString → IProp GF) :
    masterSvc δ R go!"Register" args Φ ⊢
      masterSvc δ R go!"Register" args Φ ∗ ⌜∃ k, k < 3 ∧ args = encRegArgs (ipOf k) (portNum k)⌝ := by
  refine persistent_entails_left ?_
  unfold masterSvc withErr masterSvc0
  iintro H
  icases H with ⟨⟨-, %k, %hk, -⟩, -⟩
  ipureintro; exact ⟨k, hk⟩

/-- **The master's `Register` as a net/rpc method** (`methodOk`'s `NewArg` obligation): the
deposit's arguments decode into `NewArg()`'s fresh `RegisterArgs`, the call runs
`wp_Master_Register`, and its reply encodes into the deposit's continuation (`masterSvc0`'s
two answers). -/
theorem newArg_Register (L : CodecLaws (GF := GF)) (γ : GryffNames GF) (m : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ masterReg γ m ∗
      net.rpc.codecSet gryffCodec ⊢
    newArgOk gryffCodec (ptrIface src.masterlib.Master.ty m)
      (masterSvc γ.deploy (regCarry γ.proto) go!"Register") mRegister := by
  iintro ⟨#Hpkg, #Hkit, #Hm, #Hcs⟩
  unfold newArgOk
  imodintro
  iintro %Ψ HΨ
  simp only [mOf]
  wp_func_call
  wp_call
  wp_auto
  wp_alloc p as Hp
  wp_auto
  ihave Hp := regArgs_zero_pt p $$ Hp
  have hne : ptrIface src.masterproto.RegisterArgs.ty p ≠ interface.nil := by
    simp [ptrIface, interface.mkOk]
  ihave #Hdec : net.rpc.argDec gryffCodec (ptrIface src.masterproto.RegisterArgs.ty p)
      (p ↦ src.masterproto.RegisterArgs.mk go!"" (W64 0))
      (masterSvc γ.deploy (regCarry γ.proto) go!"Register")
      (fun args _ => iprop(∃ k : Nat, ⌜k < 3 ∧ args = encRegArgs (ipOf k) (portNum k)⌝ ∗
        p ↦ src.masterproto.RegisterArgs.mk (ipOf k) (portNum k))) $$ []
  · unfold net.rpc.argDec
    iframe Hcs
    imodintro
    iintro Hp %args %Φ HS
    ihave ⟨HS, %Hsh⟩ := masterSvc_shape _ _ _ _ $$ HS
    obtain ⟨k, hk, rfl⟩ := Hsh
    iframe HS
    iapply L.decA_RegisterArgs
    isplitl [Hp]
    · iexact Hp
    iintro Hp
    iexists k
    iframe Hp
    ipureintro; exact ⟨hk, rfl⟩
  iapply HΨ $$ %_ %_ %_ %hne Hdec [Hp]
  · iexact Hp
  iintro %args %Φ HS ⟨%k, ⟨%hk, %Hargs⟩, Hp⟩
  subst Hargs
  unfold masterSvc withErr masterSvc0
  icases HS with ⟨⟨-, %k', %hk', #Hcar, HΦ⟩, -⟩
  obtain ⟨hk3', Heq'⟩ := hk'
  have hkk : k = k' := by
    rcases k with _|_|_|k <;> rcases k' with _|_|_|k' <;>
      first | rfl | omega | (exfalso; revert Heq'; decide)
  subst hkk
  unfold net.rpc.callObl
  wp_func_call
  wp_call
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  wp_func_call
  wp_call
  wp_auto
  ihave Hr0 := regReply_zero_pt «$r0_ptr» $$ «$r0»
  ihave ⟨Hr0, %hnn⟩ := persistent_entails_left (typedPointsto_not_null _ _ _) $$ Hr0
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  icases typedPointsto_split _ _ _ $$ Hr0 with Hr0
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hp
  iNamed Hr0
  wp_apply (wp_Master_Register γ m p «$r0_ptr» k hk) $$ [Addr Port ReplicaId NodeList Ready]
    as ⟨%id, %nl, %rd, %nodes, %dq, Hrp, Hnl, Hcase⟩
  · isplitr
    · iexact Hm
    isplitr
    · iexact Hcar
    unfold regArgsPt regReplyPt
    iframe
  iexists _
  isplitr
  · ipureintro; rfl
  unfold net.rpc.callRet
  ileft
  isplitr
  · ipureintro; rfl
  iapply L.enc_RegisterReply
  unfold regReplyPt
  isplitl [Hrp]
  · iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    icases Hrp with ⟨H1, H2, H3⟩
    iframe
  iframe Hnl
  iintro - -
  icases Hcase with (%Hz | ⟨%Hrd, #Hready⟩)
  · obtain ⟨rfl, rfl, rfl⟩ := Hz
    icases HΦ with ⟨HΦ, -⟩
    iexact HΦ
  · subst Hrd
    icases HΦ with ⟨-, HΦ⟩
    iapply HΦ $$ Hready

/-- A deposit at a method the master's service does not name is impossible. -/
theorem masterSvc_other (δ : DeployNames) (R : Nat → IProp GF) (mth : GoString)
    (h : mth ≠ go!"Register") (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    masterSvc δ R mth args Φ ⊢ False := by
  unfold masterSvc withErr masterSvc0
  iintro H
  icases H with ⟨⟨%hm, -⟩, -⟩
  exact absurd hm h

/-- **The master is the `"Master"` service's net/rpc receiver** (what `Server.Register` asks):
`Register` by `newArg_Register`, `GetLeader` and `GetReplicaList` named by no deposit. -/
theorem master_rcv (L : CodecLaws (GF := GF)) (RL : RcvLaws (GF := GF)) (γ : GryffNames GF)
    (m : Loc) (hm : m ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ masterReg γ m ∗
      net.rpc.codecSet gryffCodec ⊢
    gryffCodec.rcv (ptrIface src.masterlib.Master.ty m)
      (net.rpc.rcvrIs gryffCodec (ptrIface src.masterlib.Master.ty m)
        (masterSvc γ.deploy (regCarry γ.proto)) go!"Master" false) := by
  iintro ⟨#Hpkg, #Hkit, #Hm, #Hcs⟩
  iapply RL.rcv_Master m _ hm
  isplitr
  · iapply RL.newArg_GetLeader _ _ (fun args Φ => masterSvc_other _ _ _ (by decide) args Φ)
    iexact Hcs
  isplitr
  · iapply RL.newArg_GetReplicaList _ _ (fun args Φ => masterSvc_other _ _ _ (by decide) args Φ)
    iexact Hcs
  iapply newArg_Register L γ m
  iframe #

end rcvr

end Perennial.gryff
