/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchAddr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`at(addrs, id, off)` (`kit.go`) on the deployment's 13 addresses, for the orchestrator
(`configure`): node `id`'s host and its first port plus `off` (`fmt.Sprintf("%s:%d", ...)` is
exactly `host:port`); and the configuration ports it computes (`ConfOff` = 2000 above the client
nodes' and the server nodes' first ports).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch

/-- Node `i`'s host (`"10.77.0.(10+i)"`). -/
def hostStr (i : Nat) : GoString :=
  if i < 10 then go!"10.77.0.1" ++ [W8 (48 + i)] else go!"10.77.0.2" ++ [W8 (48 + (i - 10))]

/-- Node `i`'s first port, as text. -/
def portStr (i : Nat) : GoString :=
  if i < 7 then go!"7000" else go!"700" ++ [W8 (48 + (i - 6))]

/-- Node `i`'s first port. -/
def portNum (i : Nat) : Nat := if i < 7 then 7000 else 7000 + (i - 6)

/-- `at(addrs, i, off)`. -/
def atStr (i : Nat) (off : w64) : GoString :=
  hostStr i ++ go!":" ++ fmt.decimal (uint.Z (W64 (portNum i) + off))

theorem split_addr (i : Nat) (a : GoString) (ha : addrs[i]? = some a) :
    strings.split a go!":" = [hostStr i, portStr i] := by
  match i, ha with
  | 0, ha | 1, ha | 2, ha | 3, ha | 4, ha | 5, ha | 6, ha | 7, ha | 8, ha | 9, ha | 10, ha
  | 11, ha | 12, ha =>
    simp only [addrs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    simp [strings.split, strings.splitAux, hostStr, portStr]

theorem portVal_portStr (i : Nat) (hi : i < 13) : adapter.portVal (portStr i) = W64 (portNum i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ => simp [adapter.portVal, portStr, portNum]

/-- Client node `c`'s configuration port (node `1 + c`, port 9000). -/
theorem atStr_clientConf (c : Nat) (hc : c < 6) :
    clientConfAddrs[c]? = some (atStr (1 + c) (W64 2000)) := by
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [atStr, hostStr, portNum, fmt.decimal, fmt.decimalNat, fmt.digitByte, clientConfAddrs]

/-- Server node `id`'s configuration port (node `6 + id`, port `9000 + id`), `1 ≤ id ≤ 6`. -/
theorem atStr_conf (k : Nat) (hk : k < 6) :
    confAddrs[k]? = some (atStr (7 + k) (W64 2000)) := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ =>
    simp [atStr, hostStr, portNum, fmt.decimal, fmt.decimalNat, fmt.digitByte, confAddrs]

/-- Replica node `k`'s rpc port (server node `k + 2`, node `8 + k`, port `8000 + k + 2`). -/
theorem atStr_rpc (k : Nat) (hk : k < 5) :
    replicaRpcAddrs[k]? = some (atStr (8 + k) (W64 1000)) := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [atStr, hostStr, portNum, fmt.decimal, fmt.decimalNat, fmt.digitByte, replicaRpcAddrs]

section sprintf
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] [go.string ↓u go.string]

theorem IntArgValue.uniq_uint64' [go.IntoValInj w64] (n : w64) :
    ∀ z', fmt.IntArgValue (interface.mk go.uint64 #n) z' → z' = uint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := fmt.IntArgValue.of_uint64 h
  rw [go.intoVal_inj hv]

/-- `Sprintf("%s:%d", x, n)` for a string `x` and a `uint64` `n` is exactly `x:n`. -/
theorem SprintfOut.str_colon_d_uint64 [go.IntoValInj GoString] [go.IntoValInj w64]
    (x : GoString) (n : w64) (out : GoString)
    (h : fmt.SprintfOut go!"%s:%d" [interface.mkOk go.string #x, interface.mkOk go.uint64 #n] out) :
    out = x ++ go!":" ++ fmt.decimal (uint.Z n) := by
  have hfmt : go!"%s:%d" = W8 37 :: W8 115 :: W8 58 :: W8 37 :: [W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := fmt.SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := fmt.SprintfOut.int_inv (w := 0) (rest := []) (by decide)
    (fmt.IntArgValue.uint64 n) (IntArgValue.uniq_uint64' n) h2
  rw [fmt.SprintfOut.done_inv h3, fmt.decimalPad_zero]
  simp

end sprintf

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- `at(addrs, id, off)` on the deployment's addresses. -/
abbrev at.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (id off : w64), uint.nat id < 13 →
  {{ isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.«at»)) (Val #sl)) (Val #id)) (Val #off))
  {{ RET #(atStr (uint.nat id) off); sl ↦*{dq} addrs }}

theorem at.wp_proof : at.spec := by
  intro sl dq id off hid
  wp_start as Hsl
  ihave %Hl := ownSlice_len $$ Hsl
  have hlen : sint.Z sl.len = 13 := by
    have h1 := Hl.1; simp only [addrs, List.length_cons, List.length_nil] at h1; word
  obtain ⟨a, ha⟩ : ∃ a, addrs[uint.nat id]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by simp [addrs]; omega)⟩
  have hsid : (sint.Z id).toNat = uint.nat id := by
    have : sint.Z id = uint.Z id := by word
    rw [this]; rfl
  have hb : 0 ≤ sint.Z id ∧ sint.Z id < sint.Z sl.len := by rw [hlen]; constructor <;> word
  wp_auto
  simp only [hb, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z id) _ _ a hb.1 $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rw [hsid]; exact ha
  wp_apply adapter.host.wp_proof a _ _ (split_addr _ a ha)
  simp only [hb, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index sl (sint.Z id) _ _ a hb.1 $$ [Hsl] as Hsl
  · iframe Hsl; ipureintro; rw [hsid]; exact ha
  wp_apply adapter.port.wp_proof a _ _ _ (split_addr _ a ha) (by
    unfold portStr; split <;> simp)
  rw [portVal_portStr _ hid]
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.string #(hostStr (uint.nat id)),
     interface.mkOk go.uint64 #(W64 (portNum (uint.nat id)) + off)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit_ptr ⟨Hlit, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf _ _ _ _
    (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.uint64 _) fmt.ArgsWf.nil))
    $$ [Hlit] as %str ⟨-, %Hout⟩
  · iexact Hlit
  rw [SprintfOut.str_colon_d_uint64 _ _ _ Hout, show hostStr (uint.nat id) ++ go!":" ++
    fmt.decimal (uint.Z (W64 (portNum (uint.nat id)) + off)) = atStr (uint.nat id) off from rfl]
  iapply HΦ
  iexact Hsl

end proofs

end orch

end Perennial.github_com.imdea_software.swiftpaxos
