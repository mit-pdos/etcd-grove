/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientOp.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Op(sys, c, in)` (`kit.go`), client `c`'s `j`-th operation on its node, logically atomic:
connect at the first operation (or after a failed connect: the registrations peeked from the
update first, `driverAU_peek`), then `BufferClient.Write` (a put) or `Read` (a get) with the
update passed in (`ClientAU.lean`). A failed connect returns `(nil, false)` with the update
dropped (an unknown outcome) and the client still unconnected: it used the operation index `j`,
not a SwiftPaxos sequence number. Also `key` (8 bytes, little-endian) and `returned`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientAU
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

/-- `key`'s loop: the first `n` bytes of `k`, little-endian. -/
def keyAcc (k : List w8) : Nat → w64
  | 0 => W64 0
  | n + 1 => keyAcc k n ||| (W64 (uint.Z (k.getD n (W8 0))) <<< W64 ((8 * n : Nat) : Int))

/-- `key` inverts `lin.keyName` on 8-byte keys. -/
theorem keyName_keyAcc (k : List w8) (hk : k.length = 8) : lin.keyName (keyAcc k 8) = k := by
  match k, hk with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
  have e : ∀ (x : w64) (m : Nat), W8 ((x.toNat / 2 ^ m % 256 : Nat) : Int) =
      (x >>> m).setWidth 8 := by
    intro x m
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    omega
  simp only [lin.keyName, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_append, List.map_nil, List.cons_append, List.nil_append, e]
  have ez : ∀ b : w8, W64 (uint.Z b) = b.setWidth 64 := by
    intro b
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
    have := b.isLt
    simp only [uint.Z]
    omega
  simp only [keyAcc, List.getD_cons_succ, List.getD_cons_zero, ez, BitVec.ofInt_natCast]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    all_goals first
      | omega
      | simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
          BitVec.getLsbD_shiftLeft, BitVec.toNat_ofNat]

section small
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [C : net.rpc.RpcCodec netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

theorem key.wp_proof (k : GoString) (hk : k.length = 8) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
    (App (Val (@! examples.swiftnet.key)) (Val #k))
  {{ (r : w64), RET #r; ⌜lin.keyName r = k⌝ }} := by
  wp_start
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ keyAcc k (uint.nat i) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp netDistGF) $$ [i x]
  · iexists W64 0
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hi : uint.nat i < k.length := by rw [hk]; word
    list_elem k (uint.nat i) as ch
    have h0 : 0 ≤ sint.Z i := by word
    have hs : sint.nat i = uint.nat i := by word
    simp only [h0, ↓reduceIte, hs, Hch_lookup]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1
    have hsucc : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    have hsh : W64 8 * i = W64 ((8 * uint.nat i : Nat) : Int) := by word
    rw [hsucc, hsh]
    simp only [keyAcc, List.getD_eq_getElem?_getD, Hch_lookup, Option.getD_some]
    iframe
    ipureintro; word
  · have h8 : uint.nat i = 8 := by word
    rw [h8]
    iapply HΦ
    ipureintro
    exact keyName_keyAcc k hk

theorem sysV_inj {s s' : Loc} (h : sysV s = sysV s') : s = s' := by
  unfold sysV at h
  rw [interface_mkOk_inj] at h
  exact go.intoVal_inj h.2

/-- `s.returned()`. -/
theorem Sys.returned.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (s : Loc) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      isSysL γ c s }}
    (App (Val (s @!! go.GoType.PointerType examples.swiftnet.Sys.ty @!! go!"returned")) (Val #()))
  {{ RET #(); True }} := by
  wp_start as #Hs
  iunfold isSysL at Hs
  icases Hs with ⟨%conf, %asl, -, -, -, -, #Hmu, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  icases HR with ⟨%d, Hd⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hd]
  · iframe Hmu Hlocked
    iexists _
    iexact Hd
  iapply HΦ $$ %trivial

end small

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [C : net.rpc.RpcCodec netDistGF]

/-- `s.connect(c)`: the node's client connected (ready at sequence number 0) or, on `false`,
as it was. -/
abbrev Sys.connect.spec (γ : SwiftNames netDistGF) (c : Nat) : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
      isSysL γ c s ∗ s.[examples.swiftnet.Sys, go!"b"] ↦ (null : Loc) ∗
      sp.clientSeq γ.sp (cidOf c) 0 ∗ sp.allPredsReg γ.sp γ.conf }}
    (App (Val (s @!! go.GoType.PointerType examples.swiftnet.Sys.ty @!! go!"connect"))
      (Val #(W64 (c : Int))))
  {{ (ok : Bool), RET #ok;
      if ok then ∃ b : Loc, s.[examples.swiftnet.Sys, go!"b"] ↦ b ∗ ⌜b ≠ null⌝ ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin (cidOf c) 0
      else s.[examples.swiftnet.Sys, go!"b"] ↦ (null : Loc) ∗ sp.clientSeq γ.sp (cidOf c) 0 }}

end specs

section op
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [C : net.rpc.RpcCodec netDistGF]
variable [examples.swiftnet.Assumptions] [client.Assumptions]

set_option goose.wp.extras true

theorem Op.wp_proof (γ : SwiftNames netDistGF) (c : Nat)
    (wp_connect : Sys.connect.spec γ c)
    (wp_Write : client.BufferClient.Write.spec) (wp_Read : client.BufferClient.Read.spec)
    (sys : GoInterface) (j : Nat) (i : (kv GoString GoString).Input)
    (hj : j < 8) (hpre : kit.pre i) :
    ⊢ isPkgInit (PROP := IProp netDistGF) kit.pkg -∗ isSys γ c sys -∗ clientTok γ c sys j -∗
      opAwpMaybe (App (App (App (Val (@! examples.swiftnet.Op)) (Val #sys)) (Val #(W64 (c : Int))))
          (Val #(encKvIn i)))
        (↑clientN) (ownState γ)
        (fun σ σ' o => iprop(ownState γ σ' ∗ ⌜(kv GoString GoString).step σ i σ' o⌝))
        (fun o => PairV #(encKvOut o) #true) (fun v => ∃ x : GoInterface, v = PairV #x #false)
        (clientTok γ c sys (j + 1)) := by
  dsimp only [kit]
  iintro #Hpkg #Hsys Htok
  unfold opAwpMaybe
  iintro %Q HAU
  iunfold isSys at Hsys
  icases Hsys with ⟨%s, %Hsys, #Hs⟩
  iunfold clientTok at Htok
  icases Htok with ⟨%s', %Hs', Hst⟩
  have hss : s = s' := sysV_inj (Hsys.symm.trans Hs')
  subst hss Hsys
  wp_func_call
  wp_call
  imod driverAU_peek γ i Q $$ HAU with ⟨HAU, #Hreg⟩
  wp_auto
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ c_ptr ↦ W64 (c : Int) ∗ s_ptr ↦ s ∗ «$res0_ptr» ↦ GoInterface.nil ∗
        «$res1_ptr» ↦ zero_val Bool ∗ ∃ (b : Loc) (sq : Nat),
        s.[examples.swiftnet.Sys, go!"b"] ↦ b ∗ ⌜b ≠ null ∧ sq ≤ j⌝ ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin (cidOf c) sq) ∨
      (⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ GoInterface.nil ∗ «$res1_ptr» ↦ false ∗
        clSt γ s c (j + 1))))
    at next with [Hst c s «$res0» «$res1»]
  · iunfold clSt at Hst
    icases Hst with (⟨Hb, Hseq⟩ | ⟨%b, %sq, Hb, %Hbs, Hready⟩)
    · wp_auto
      wp_apply wp_connect s $$ [Hb Hseq] as %ok Hok
      · iframe Hs Hb Hseq Hreg
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iright
        iframe
        isplitr
        · ipureintro; rfl
        iunfold clSt
        ileft
        iexact Hok
      · simp only [↓reduceIte]
        wp_auto
        ileft
        iframe
        isplitr
        · ipureintro; rfl
        icases Hok with ⟨%b, Hb, %Hb, Hready⟩
        iexists b, 0
        iframe
        ipureintro; exact ⟨Hb, Nat.zero_le _⟩
    · wp_auto
      wp_if_destruct
      · exact absurd rfl Hbs.1
      ileft
      iframe
      ipureintro
      first | exact Hbs | exact ⟨rfl, Hbs⟩
  iintro (⟨%Hv, c, s, «$res0», «$res1», %b, %sq, Hb, %Hbs, Hready⟩ |
    ⟨%Hv, «$res0», «$res1», Hst⟩)
  · subst Hv
    wp_auto
    have hsq : sq < 2 ^ 10 := by omega
    cases i with
    | put k v =>
      obtain ⟨hk, hv, hvlen⟩ := hpre
      simp only [kvInV]
      wp_auto
      wp_apply key.wp_proof k hk as %key %Hkey
      wp_apply wp_string_to_bytes v as %vsl ⟨Hvsl, Hcap⟩
      imod ownSlice_persist $$ Hvsl with #Hvsl
      subst Hkey
      wp_apply wp_Write_au wp_Write γ b (cidOf c) sq key vsl v hv hvlen hsq Q $$ [Hready HAU]
        as Hready HQ
      · iframe Hready HAU Hvsl
      wp_apply Sys.returned.wp_proof γ c s $$ []
      · iexact Hs
      isplitl [Hb Hready]
      · iunfold clientTok
        iexists s
        isplitr
        · ipureintro; rfl
        iunfold clSt
        iright
        iexists b, sq + 1
        iframe
        ipureintro; exact ⟨Hbs.1, by omega⟩
      ileft
      icases HQ with ⟨%σ, %σ', HQ⟩
      iexists σ, σ', KvOutput.done
      iframe HQ
      ipureintro; rfl
    | get k =>
      have hk : k.length = 8 := hpre
      simp only [kvInV]
      wp_auto
      wp_apply key.wp_proof k hk as %key %Hkey
      subst Hkey
      wp_apply wp_Read_au wp_Read γ b (cidOf c) sq key hsq Q $$ [Hready HAU]
        as %sl %ov %Hov #Hsl Hready HQ
      · iframe
      wp_apply Sys.returned.wp_proof γ c s $$ []
      · iexact Hs
      ihave %Hsllen := ownSlice_len $$ Hsl
      wp_if_destruct
      · have hov : ov = none := by
          rcases ov with _ | w
          · rfl
          · exfalso
            have : w.length = 0 := by
              have h := Hsllen.1
              rw [Option.getD_some, Hif] at h
              rw [h]; rfl
            exact Hov (by rw [List.length_eq_zero_iff.mp this])
        subst hov
        isplitl [Hb Hready]
        · iunfold clientTok
          iexists s
          isplitr
          · ipureintro; rfl
          iunfold clSt
          iright
          iexists b, sq + 1
          iframe
          ipureintro; exact ⟨Hbs.1, by omega⟩
        ileft
        icases HQ with ⟨%σ, %σ', HQ⟩
        iexists σ, σ', KvOutput.got none
        iframe HQ
        ipureintro
        rfl
      · rcases ov with _ | w
        · exfalso
          apply Hif
          have h0 : sint.nat sl.len = 0 := by simp at Hsllen; omega
          word
        simp only [Option.getD_some]
        wp_apply wp_bytes_to_string sl w _ $$ [] as -
        · iexact Hsl
        isplitl [Hb Hready]
        · iunfold clientTok
          iexists s
          isplitr
          · ipureintro; rfl
          iunfold clSt
          iright
          iexists b, sq + 1
          iframe
          ipureintro; exact ⟨Hbs.1, by omega⟩
        ileft
        icases HQ with ⟨%σ, %σ', HQ⟩
        iexists σ, σ', KvOutput.got (some w)
        iframe HQ
        ipureintro
        rfl
  · subst Hv
    wp_auto
    iframe
    isplitl [Hst]
    · iunfold clientTok
      iexists s
      iframe Hst
      ipureintro; rfl
    iright
    ipureintro
    exact ⟨_, rfl⟩

end op

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
